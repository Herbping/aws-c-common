/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_array_list_comparator_string_harness() {
    struct aws_string *str_a = ensure_string_is_allocated_nondet_length();
    struct aws_string *str_b = nondet_bool() ? str_a : ensure_string_is_allocated_nondet_length();
    __CPROVER_assume(aws_string_is_valid(str_a));
    __CPROVER_assume(aws_string_is_valid(str_b));

    bool nondet_parameter_a;
    bool nondet_parameter_b;
    if (aws_array_list_comparator_string(nondet_parameter_a ? &str_a : NULL, nondet_parameter_b ? &str_b : NULL) == 0) {
        if (nondet_parameter_a && nondet_parameter_b) {
            assert_bytes_match(str_a->bytes, str_b->bytes, str_a->len);
        }
    }
}
