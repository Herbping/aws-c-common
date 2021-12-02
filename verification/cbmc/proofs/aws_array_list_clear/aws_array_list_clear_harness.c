/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 5s
 */
void aws_array_list_clear_harness() {
    /* data structure */
    struct aws_array_list list;
    size_t bound_len;
    size_t bound_item;
    /* assumptions */
    //__CPROVER_assume(aws_array_list_is_bounded(&list, MAX_INITIAL_ITEM_ALLOCATION, 20));
    __CPROVER_assume(list.item_size == 3 && list.length <= bound_item);
    ensure_array_list_has_allocated_data_member(&list);
    __CPROVER_assume(aws_array_list_is_valid(&list));

    /* save current state of the data structure */
    struct aws_array_list old = list;

    /* perform operation under verification */
    aws_array_list_clear(&list);

    /* assertions */
    assert(aws_array_list_is_valid(&list));
    assert(list.length == 0);
    assert(list.alloc == old.alloc);
    assert(list.current_size == old.current_size);
    assert(list.item_size == old.item_size);
    assert(list.data == old.data);
}
