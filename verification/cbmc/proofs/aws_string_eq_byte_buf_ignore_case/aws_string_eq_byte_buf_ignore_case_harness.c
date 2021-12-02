/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_string_eq_byte_buf_ignore_case_harness() {
    size_t size;
    struct aws_string *str = nondet_allocate_string_bounded_length(size);
    struct aws_byte_buf buf;

    __CPROVER_assume(IMPLIES(str != NULL, aws_string_is_valid(str)));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, size));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    bool nondet_parameter;
    if (aws_string_eq_byte_buf_ignore_case(str, nondet_parameter ? &buf : NULL) && str) {
        assert(aws_string_is_valid(str));
        if (nondet_parameter) {
            assert(str->len == buf.len);
        }
    }

    assert(aws_byte_buf_is_valid(&buf));
}
