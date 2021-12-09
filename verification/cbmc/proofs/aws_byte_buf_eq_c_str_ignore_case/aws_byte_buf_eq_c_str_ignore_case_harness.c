/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_eq_c_str_ignore_case_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    const char *c_str = ensure_c_str_is_allocated(MAX_MALLOC);

    /* assumptions */
    __CPROVER_assume(c_str != NULL);
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_MALLOC));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the parameters */

    /* operation under verification */
    if (aws_byte_buf_eq_c_str_ignore_case(&buf, c_str)) {

    }

    /* asserts both parameters remain unchanged */
    assert(aws_byte_buf_is_valid(&buf));
}
