/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_write_u8_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    uint8_t x;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, UINT32_MAX));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));


    /* operation under verification */
    aws_byte_buf_write_u8(&buf, x);

}
