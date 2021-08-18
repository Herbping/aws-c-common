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

#include <aws/testing/aws_test_harness.h>

#include <aws/common/bus.h>

static struct {
    int count;
    bool payload_deleted;
} s_sync_test;

static const char s_test_payload[] = "TEST ME SENPAI";

static void s_bus_sync_test_recv(uint64_t address, const void *msg, void *user_data) {
    AWS_ASSERT(42 == address);
    AWS_ASSERT(0 == strcmp(msg, s_test_payload));
    AWS_ASSERT(&s_sync_test == user_data);
    ++s_sync_test.count;
}

static void s_test_payload_dtor(void *payload) {
    (void)payload;
    s_sync_test.payload_deleted = true;
}

static int s_bus_sync_test_send(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_SYNC,
    };

    struct aws_bus bus;
    ASSERT_SUCCESS(aws_bus_init(&bus, &options));
    AWS_ZERO_STRUCT(s_sync_test);

    ASSERT_SUCCESS(aws_bus_subscribe(&bus, 42, s_bus_sync_test_recv, &s_sync_test));
    ASSERT_SUCCESS(aws_bus_send(&bus, 42, (void *)&s_test_payload[0], s_test_payload_dtor));

    ASSERT_INT_EQUALS(1, s_sync_test.count);
    ASSERT_TRUE(s_sync_test.payload_deleted);

    /* reset test and send a bunch of events */
    AWS_ZERO_STRUCT(s_sync_test);

    const int send_count = 100;
    for (int send = 0; send < send_count; ++send) {
        ASSERT_SUCCESS(aws_bus_send(&bus, 42, (void*)&s_test_payload[0], s_test_payload_dtor));
    }

    ASSERT_INT_EQUALS(send_count, s_sync_test.count);
    ASSERT_TRUE(s_sync_test.payload_deleted);

    aws_bus_unsubscribe(&bus, 42, s_bus_sync_test_recv, &s_sync_test);
    aws_bus_clean_up(&bus);

    return 0;
}
AWS_TEST_CASE(bus_sync_test_send, s_bus_sync_test_send)

static int s_bus_async_test_lifetime(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_ASYNC,
    };

    struct aws_bus bus;
    ASSERT_SUCCESS(aws_bus_init(&bus, &options));
    aws_bus_clean_up(&bus);

    /* If the background thread didn't exit cleanly, there will be leaks */

    return 0;
}
AWS_TEST_CASE(bus_async_test_lifetime, s_bus_async_test_lifetime)

static int s_bus_async_test_send_single_threaded(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    return 0;
}
AWS_TEST_CASE(bus_async_test_send_single_threaded, s_bus_async_test_send_single_threaded)

static int s_bus_async_test_send_multi_threaded(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    return 0;
}
AWS_TEST_CASE(bus_async_test_send_multi_threaded, s_bus_async_test_send_multi_threaded)
