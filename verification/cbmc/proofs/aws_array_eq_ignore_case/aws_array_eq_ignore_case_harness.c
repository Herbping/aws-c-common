/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_array_eq_ignore_case_harness() {
    /* assumptions */
    size_t lhs_len;
     __CPROVER_assume(lhs_len <= UINT32_MAX);
    void *lhs = malloc(lhs_len);

    void *rhs;
    size_t rhs_len;
    if (nondet_bool()) { /* rhs could be equal to lhs */
        rhs_len = lhs_len;
        rhs = lhs;
    } else {
        __CPROVER_assume(rhs_len <= UINT32_MAX);
        rhs = malloc(rhs_len);
    }

    /* pre-conditions */
    __CPROVER_assume((lhs_len == 0) || AWS_MEM_IS_READABLE(lhs, lhs_len));
    __CPROVER_assume((rhs_len == 0) || AWS_MEM_IS_READABLE(rhs, rhs_len));

    /* operation under verification */
    aws_array_eq_ignore_case(lhs, lhs_len, rhs, rhs_len);

}
