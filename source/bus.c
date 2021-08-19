/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/bus.h>

#include <aws/common/allocator.h>
#include <aws/common/atomics.h>
#include <aws/common/byte_buf.h>
#include <aws/common/condition_variable.h>
#include <aws/common/hash_table.h>
#include <aws/common/linked_list.h>
#include <aws/common/mutex.h>
#include <aws/common/thread.h>

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4204) /* nonstandard extension used: non-constant aggregate initializer */
#endif

/* MUST be the first member of any impl to allow blind casting */
struct bus_vtable {
    void (*clean_up)(struct aws_bus *bus);

    int (*send)(struct aws_bus *bus, uint64_t address, void *payload, void (*destructor)(void *));

    int (*subscribe)(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data);

    int (*unsubscribe)(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data);
};

/* each bound callback is stored as a bus_listener in the slots table */
struct bus_listener {
    struct aws_linked_list_node list_node;
    void *user_data;
    aws_bus_listener_fn *deliver;
};

/* value type stored in each slot in the slots table in a bus */
struct listener_list {
    struct aws_allocator *allocator;
    struct aws_linked_list listeners;
};

/* find a listener list (or NULL) by address */
static struct listener_list *bus_find_listeners(struct aws_hash_table *slots, uint64_t address) {
    struct aws_hash_element *elem = NULL;
    if (aws_hash_table_find(slots, (void *)(uintptr_t)address, &elem)) {
        return NULL;
    }

    if (!elem) {
        return NULL;
    }

    struct listener_list *list = elem->value;
    return list;
}

/* find a listener list by address, or create/insert/return a new one */
static struct listener_list *bus_find_or_create_listeners(
    struct aws_allocator *allocator,
    struct aws_hash_table *slots,
    uint64_t address) {
    struct listener_list *list = bus_find_listeners(slots, address);
    if (list) {
        return list;
    }

    list = aws_mem_calloc(allocator, 1, sizeof(struct listener_list));
    list->allocator = allocator;
    aws_linked_list_init(&list->listeners);
    aws_hash_table_put(slots, (void *)(uintptr_t)address, list, NULL);
    return list;
}

static int bus_deliver_msg_to_slot(
    struct aws_bus *bus,
    uint64_t slot,
    uint64_t address,
    struct aws_hash_table *slots,
    const void *payload) {
    (void)bus;
    struct listener_list *list = bus_find_listeners(slots, slot);
    if (!list) {
        return AWS_OP_SUCCESS;
    }
    struct aws_linked_list_node *node = aws_linked_list_begin(&list->listeners);
    for (; node != aws_linked_list_end(&list->listeners); node = aws_linked_list_next(node)) {
        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        listener->deliver(address, payload, listener->user_data);
    }

    return AWS_OP_SUCCESS;
}

/* common delivery logic */
static int bus_deliver_msg(struct aws_bus *bus, uint64_t address, struct aws_hash_table *slots, const void *payload) {
    (void)bus;
    int result = AWS_OP_SUCCESS;
    result |= bus_deliver_msg_to_slot(bus, AWS_BUS_ADDRESS_ALL, address, slots, payload);
    result |= bus_deliver_msg_to_slot(bus, address, address, slots, payload);
    return result;
}

/* common subscribe logic */
static int bus_subscribe(
    struct aws_bus *bus,
    uint64_t address,
    struct aws_hash_table *slots,
    aws_bus_listener_fn *callback,
    void *user_data) {
    struct listener_list *list = bus_find_or_create_listeners(bus->allocator, slots, address);
    if (!list) {
        return AWS_OP_ERR;
    }

    struct bus_listener *listener = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_listener));
    listener->deliver = callback;
    listener->user_data = user_data;
    aws_linked_list_push_back(&list->listeners, &listener->list_node);

    return AWS_OP_SUCCESS;
}

/* common unsubscribe logic */
static int bus_unsubscribe(
    struct aws_bus *bus,
    uint64_t address,
    struct aws_hash_table *slots,
    aws_bus_listener_fn *callback,
    void *user_data) {
    (void)bus;

    struct listener_list *list = bus_find_listeners(slots, address);
    if (!list) {
        return AWS_OP_SUCCESS;
    }

    struct aws_linked_list_node *node;
    for (node = aws_linked_list_begin(&list->listeners); node != aws_linked_list_end(&list->listeners);
         node = aws_linked_list_next(node)) {

        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        if (listener->deliver == callback && listener->user_data == user_data) {
            aws_linked_list_remove(node);
            aws_mem_release(list->allocator, listener);
            break;
        }
    }

    return AWS_OP_SUCCESS;
}

/* destructor for listener lists in the slots tables */
void bus_destroy_listener_list(void *data) {
    struct listener_list *list = data;
    AWS_PRECONDITION(list->allocator);
    /* call all listeners with an AWS_BUS_ADDRESS_CLOSE message type to clean up */
    while (!aws_linked_list_empty(&list->listeners)) {
        struct aws_linked_list_node *back = aws_linked_list_back(&list->listeners);
        struct bus_listener *listener = AWS_CONTAINER_OF(back, struct bus_listener, list_node);
        listener->deliver(AWS_BUS_ADDRESS_CLOSE, NULL, listener->user_data);
        aws_linked_list_pop_back(&list->listeners);
        aws_mem_release(list->allocator, listener);
    }
    aws_mem_release(list->allocator, list);
}

/*
 * AWS_BUS_SYNC implementation
 */
struct bus_sync_impl {
    struct bus_vtable vtable;
    struct {
        /* Map of address -> list of listeners */
        struct aws_hash_table table;
    } slots;
};

static void bus_sync_clean_up(struct aws_bus *bus) {
    struct bus_sync_impl *impl = bus->impl;
    aws_hash_table_clean_up(&impl->slots.table);
    aws_mem_release(bus->allocator, impl);
}

static int bus_sync_send(struct aws_bus *bus, uint64_t address, void *payload, void (*destructor)(void *)) {
    struct bus_sync_impl *impl = bus->impl;
    int result = bus_deliver_msg(bus, address, &impl->slots.table, payload);
    if (destructor) {
        destructor(payload);
    }
    return result;
}

static int bus_sync_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data) {
    struct bus_sync_impl *impl = bus->impl;
    return bus_subscribe(bus, address, &impl->slots.table, callback, user_data);
}

static int bus_sync_unsubscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data) {
    struct bus_sync_impl *impl = bus->impl;
    return bus_unsubscribe(bus, address, &impl->slots.table, callback, user_data);
}

static struct bus_vtable bus_sync_vtable = {
    .clean_up = bus_sync_clean_up,
    .send = bus_sync_send,
    .subscribe = bus_sync_subscribe,
    .unsubscribe = bus_sync_unsubscribe,
};

static void bus_sync_init(struct aws_bus *bus, struct aws_bus_options *options) {
    (void)options;

    struct bus_sync_impl *impl = bus->impl = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_sync_impl));
    impl->vtable = bus_sync_vtable;

    if (aws_hash_table_init(
            &impl->slots.table, bus->allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, bus_destroy_listener_list)) {
        goto error;
    }

    return;

error:
    aws_mem_release(bus->allocator, impl);
}

/*
 * AWS_BUS_ASYNC implementation
 */
struct bus_async_impl {
    struct bus_vtable vtable;
    struct {
        /* Map of address -> list of listeners */
        struct aws_hash_table table;
    } slots;

    /* Queue of bus_messages to deliver */
    struct {
        struct aws_mutex mutex;
        /* backing memory for the message free list */
        void *buffer;
        /* message free list */
        struct aws_linked_list free;
        /* message delivery queue */
        struct aws_linked_list msgs;
        /* list of pending adds/removes of listeners */
        struct aws_linked_list subs;
    } queue;

    /* dispatch thread */
    struct {
        struct aws_thread thread;
        struct aws_condition_variable notify;
        struct aws_atomic_var running;
        struct aws_atomic_var exited;
    } dispatch;
};

/* represents a message in the queue on impls that queue */
struct bus_message {
    struct aws_linked_list_node list_node;
    uint64_t address;
    void *payload;

    void (*destructor)(void *);
};

struct pending_listener {
    struct aws_linked_list_node list_node;
    uint64_t address;
    aws_bus_listener_fn *listener;
    void *user_data;
    uint32_t add : 1;
    uint32_t remove : 1;
};

/*
 * resolve all adds and removes of listeners, in FIFO order
 * NOTE: expects mutex to be held by caller
 */
static void bus_apply_listeners(struct aws_bus *bus, struct aws_linked_list *pending_subs) {
    struct bus_async_impl *impl = bus->impl;
    while (!aws_linked_list_empty(pending_subs)) {
        struct aws_linked_list_node *node = aws_linked_list_pop_front(pending_subs);
        struct pending_listener *listener = AWS_CONTAINER_OF(node, struct pending_listener, list_node);
        if (listener->add) {
            bus_subscribe(bus, listener->address, &impl->slots.table, listener->listener, listener->user_data);
        } else if (listener->remove) {
            bus_unsubscribe(bus, listener->address, &impl->slots.table, listener->listener, listener->user_data);
        }
        aws_mem_release(bus->allocator, listener);
    }
}

static void bus_async_clean_up(struct aws_bus *bus) {
    struct bus_async_impl *impl = bus->impl;

    /* shut down delivery thread, clean up dispatch */
    aws_atomic_exchange_int(&impl->dispatch.running, 0);
    aws_condition_variable_notify_one(&impl->dispatch.notify);
    while (!aws_atomic_load_int(&impl->dispatch.exited)) {
        aws_thread_current_sleep(1000 * 1000);
    }
    aws_thread_join(&impl->dispatch.thread);
    aws_condition_variable_clean_up(&impl->dispatch.notify);

    /* clean up work queue */
    while (!aws_linked_list_empty(&impl->queue.subs)) {
        /* apply the subs so they'll be cleaned up when the table is cleaned up */
        bus_apply_listeners(bus, &impl->queue.subs);
    }
    aws_mem_release(bus->allocator, impl->queue.buffer);
    aws_mutex_clean_up(&impl->queue.mutex);

    aws_hash_table_clean_up(&impl->slots.table);
    aws_mem_release(bus->allocator, impl);
}

static bool bus_async_should_wake_up(void *user_data) {
    struct bus_async_impl *impl = user_data;
    return !aws_atomic_load_int(&impl->dispatch.running) || !aws_linked_list_empty(&impl->queue.subs) ||
           !aws_linked_list_empty(&impl->queue.msgs);
}

/* Async bus delivery thread loop */
static void bus_async_deliver(void *user_data) {
    struct aws_bus *bus = user_data;
    struct bus_async_impl *impl = bus->impl;

    while (aws_atomic_load_int(&impl->dispatch.running)) {
        struct aws_linked_list pending_msgs;
        aws_linked_list_init(&pending_msgs);

        struct aws_linked_list pending_subs;
        aws_linked_list_init(&pending_subs);

        aws_mutex_lock(&impl->queue.mutex);
        {
            aws_condition_variable_wait_for_pred(
                &impl->dispatch.notify, &impl->queue.mutex, 100, bus_async_should_wake_up, impl);

            /* copy out any queued subs/unsubs */
            aws_linked_list_swap_contents(&pending_subs, &impl->queue.subs);
            /* copy out any queued messages */
            aws_linked_list_swap_contents(&pending_msgs, &impl->queue.msgs);
        }
        aws_mutex_unlock(&impl->queue.mutex);

        /* resolve any pending sub/unsubs first */
        if (!aws_linked_list_empty(&pending_subs)) {
            bus_apply_listeners(bus, &pending_subs);
        }

        if (aws_linked_list_empty(&pending_msgs)) {
            continue;
        }

        struct aws_linked_list_node *msg_node = aws_linked_list_begin(&pending_msgs);
        for (; msg_node != aws_linked_list_end(&pending_msgs); msg_node = aws_linked_list_next(msg_node)) {
            struct bus_message *msg = AWS_CONTAINER_OF(msg_node, struct bus_message, list_node);
            bus_deliver_msg(bus, msg->address, &impl->slots.table, msg->payload);

            /* Release payload */
            if (msg->destructor) {
                msg->destructor(msg->payload);
            }
        }

        /* push all pending messages back on the free list */
        aws_mutex_lock(&impl->queue.mutex);
        aws_linked_list_move_all_front(&impl->queue.free, &pending_msgs);
        aws_mutex_unlock(&impl->queue.mutex);
    }

    aws_atomic_exchange_int(&impl->dispatch.exited, 1);
}

int bus_async_send(struct aws_bus *bus, uint64_t address, void *payload, void (*destructor)(void *)) {
    struct bus_async_impl *impl = bus->impl;

    aws_mutex_lock(&impl->queue.mutex);

    /* take a msg from the free list, or bail if there aren't any */
    if (aws_linked_list_empty(&impl->queue.free)) {
        aws_mutex_unlock(&impl->queue.mutex);
        return AWS_OP_ERR;
    }
    struct aws_linked_list_node *msg_node = aws_linked_list_pop_back(&impl->queue.free);

    /* initialize the new message */
    struct bus_message *msg = AWS_CONTAINER_OF(msg_node, struct bus_message, list_node);
    AWS_ZERO_STRUCT(*msg);
    msg->address = address;
    msg->payload = payload;
    msg->destructor = destructor;

    /* push the messgae onto the delivery queue */
    struct aws_linked_list *queue = &impl->queue.msgs;
    aws_linked_list_push_back(queue, &msg->list_node);
    /* END CRITICAL SECTION */
    aws_mutex_unlock(&impl->queue.mutex);

    /* notify the delivery thread to wake up */
    aws_condition_variable_notify_one(&impl->dispatch.notify);

    return AWS_OP_SUCCESS;
}

int bus_async_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data) {
    struct bus_async_impl *impl = bus->impl;
    struct pending_listener *sub = aws_mem_calloc(bus->allocator, 1, sizeof(struct pending_listener));
    sub->address = address;
    sub->listener = listener;
    sub->user_data = user_data;
    sub->add = true;
    aws_mutex_lock(&impl->queue.mutex);
    aws_linked_list_push_back(&impl->queue.subs, &sub->list_node);
    aws_mutex_unlock(&impl->queue.mutex);
    aws_condition_variable_notify_one(&impl->dispatch.notify);
    return AWS_OP_SUCCESS;
}

int bus_async_unsubscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data) {
    struct bus_async_impl *impl = bus->impl;
    struct pending_listener *unsub = aws_mem_calloc(bus->allocator, 1, sizeof(struct pending_listener));
    unsub->address = address;
    unsub->listener = listener;
    unsub->user_data = user_data;
    unsub->remove = true;
    aws_mutex_lock(&impl->queue.mutex);
    aws_linked_list_push_back(&impl->queue.subs, &unsub->list_node);
    aws_mutex_unlock(&impl->queue.mutex);
    return AWS_OP_SUCCESS;
}

static struct bus_vtable bus_async_vtable = {
    .clean_up = bus_async_clean_up,
    .send = bus_async_send,
    .subscribe = bus_async_subscribe,
    .unsubscribe = bus_async_unsubscribe,
};

static void bus_async_init(struct aws_bus *bus, struct aws_bus_options *options) {
    struct bus_async_impl *impl = bus->impl = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_async_impl));
    impl->vtable = bus_async_vtable;

    /* init msg queue */
    if (aws_mutex_init(&impl->queue.mutex)) {
        goto error;
    }
    aws_linked_list_init(&impl->queue.msgs);
    aws_linked_list_init(&impl->queue.free);
    aws_linked_list_init(&impl->queue.subs);

    /* push as many bus_messages as we can into the free list from the buffer */
    const size_t buffer_size = options->buffer_size ? options->buffer_size : (4 * 1024);
    impl->queue.buffer = aws_mem_calloc(bus->allocator, 1, buffer_size);
    const size_t msg_count = buffer_size / sizeof(struct bus_message);
    for (int msg_idx = 0; msg_idx < msg_count; ++msg_idx) {
        struct bus_message *msg = (void *)&((char *)impl->queue.buffer)[msg_idx * sizeof(struct bus_message)];
        aws_linked_list_push_back(&impl->queue.free, &msg->list_node);
    }

    /* init subscription table */
    if (aws_hash_table_init(
            &impl->slots.table, bus->allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, bus_destroy_listener_list)) {
        goto error;
    }

    /* Setup dispatch thread */
    if (aws_condition_variable_init(&impl->dispatch.notify)) {
        goto error;
    }

    if (aws_thread_init(&impl->dispatch.thread, bus->allocator)) {
        goto error;
    }

    aws_atomic_exchange_int(&impl->dispatch.running, 1);
    if (aws_thread_launch(&impl->dispatch.thread, bus_async_deliver, bus, aws_default_thread_options())) {
        goto error;
    }

    return;

error:
    aws_thread_clean_up(&impl->dispatch.thread);
    aws_condition_variable_clean_up(&impl->dispatch.notify);
    aws_hash_table_clean_up(&impl->slots.table);
    aws_mem_release(bus->allocator, &impl->queue.buffer);
    aws_mutex_clean_up(&impl->queue.mutex);

    aws_mem_release(bus->allocator, impl);
}

/*
 * Public API
 */
int aws_bus_init(struct aws_bus *bus, struct aws_bus_options *options) {
    bus->allocator = options->allocator;

    if (options->policy == AWS_BUS_ASYNC) {
        bus_async_init(bus, options);
    } else if (options->policy == AWS_BUS_SYNC) {
        bus_sync_init(bus, options);
    }

    if (!bus->impl) {
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

void aws_bus_clean_up(struct aws_bus *bus) {
    struct bus_vtable *vtable = bus->impl;
    vtable->clean_up(bus);
}

int aws_bus_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data) {
    struct bus_vtable *vtable = bus->impl;
    return vtable->subscribe(bus, address, listener, user_data);
}

void aws_bus_unsubscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data) {
    struct bus_vtable *vtable = bus->impl;
    vtable->unsubscribe(bus, address, listener, user_data);
}

int aws_bus_send(struct aws_bus *bus, uint64_t address, void *payload, void (*destructor)(void *)) {
    struct bus_vtable *vtable = bus->impl;
    return vtable->send(bus, address, payload, destructor);
}

#ifdef _MSC_VER
#    pragma warning(pop)
#endif
