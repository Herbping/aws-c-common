/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_eq_harness() {
    /* parameters */
    struct aws_byte_buf lhs;
    struct aws_byte_buf rhs;

    size_t size;

    /* assumptions */
     __CPROVER_assume(aws_byte_buf_is_bounded(&lhs, MAX_MALLOC));
    ensure_byte_buf_has_allocated_buffer_member(&lhs);
    __CPROVER_assume(aws_byte_buf_is_valid(&lhs));
    if (nondet_bool()) {
        rhs = lhs;
    } else {
         __CPROVER_assume(aws_byte_buf_is_bounded(&rhs, MAX_MALLOC));
        ensure_byte_buf_has_allocated_buffer_member(&rhs);
        __CPROVER_assume(aws_byte_buf_is_valid(&rhs));
    }

    /* operation under verification */
    if (aws_byte_buf_eq(&lhs, &rhs)) {
        assert(lhs.len == rhs.len);
        if (lhs.len > 0) {

        }
    }

    /* assertions */
    assert(aws_byte_buf_is_valid(&lhs));
    assert(aws_byte_buf_is_valid(&rhs));
}
