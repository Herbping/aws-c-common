/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

void __CPROVER_file_local_priority_queue_c_s_sift_down(struct aws_priority_queue *queue, size_t root);

void aws_priority_queue_s_sift_down_harness() {
    /* Data structure */
    struct aws_priority_queue queue;
    size_t size;

    /* Assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, 3, 2));
    ensure_priority_queue_has_allocated_members(&queue);

    /* Assume the function preconditions */
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));
    size_t root;
    __CPROVER_assume(root < queue.container.length);


    /* Perform operation under verification */
    __CPROVER_file_local_priority_queue_c_s_sift_down(&queue, root);

}
