/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_array_eq_c_str_ignore_case_harness() {
    /* assumptions */
    size_t array_len;
    //__CPROVER_assume(array_len <= MAX_BUFFER_SIZE);
    void *array = malloc(array_len);
    const char *c_str = ensure_c_str_is_allocated(array_len);

    /* pre-conditions */
    __CPROVER_assume(array || (array_len == 0));
    __CPROVER_assume(c_str);

    /* operation under verification */
    if (aws_array_eq_c_str_ignore_case(array, array_len, c_str)) {
        //assert(array_len == str_len);
    }

  
}
