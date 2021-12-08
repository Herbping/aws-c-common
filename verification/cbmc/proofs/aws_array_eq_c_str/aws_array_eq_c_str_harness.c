/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

size_t _strlen(const char *s)
/*
  __CPROVER_requires(s != NULL && __CPROVER_exists {
    int i;
    (0 <= i && i < MAX_BUFFER_SIZE) ==> (i < __CPROVER_OBJECT_SIZE(s)) ==> s[i] == '\0'
  })
  __CPROVER_ensures(
    __CPROVER_return_value < __CPROVER_OBJECT_SIZE(s)
    &&
    (  (
    s[__CPROVER_return_value]=='\0' &&  __CPROVER_forall {
    int i;
    (0 <= i && i < MAX_BUFFER_SIZE) ==> (i < __CPROVER_return_value) ==> s[i] != '\0'
  }))
  )
  */
{
  __CPROVER_size_t len=0;
  while(s[len]!=0)
  __CPROVER_loop_invariant (
    (0 <= len) && (len < __CPROVER_OBJECT_SIZE(s)) &&
    (__CPROVER_forall {
            int k;
            (0 <= k && k < MAX_BUFFER_SIZE) ==> ((k < len) ==>  (s[k] != '\0'))
      })
    )
    len++;
  return len;
}

void aws_array_eq_c_str_harness() {
    /* assumptions */
    void *array;
    size_t array_len;
    // __CPROVER_assume(array_len <= MAX_BUFFER_SIZE);
    array = malloc(array_len);
    const char *c_str = ensure_c_str_is_allocated(array_len);

    /* save current state of the parameters */
    struct store_byte_from_buffer old_byte_from_array;
    save_byte_from_array((uint8_t *)array, array_len, &old_byte_from_array);
    size_t str_len = (c_str != NULL) ? _strlen(c_str) : 0;
    struct store_byte_from_buffer old_byte_from_str;
    save_byte_from_array((uint8_t *)c_str, str_len, &old_byte_from_str);

    /* pre-conditions */
    __CPROVER_assume(array || (array_len == 0));
    __CPROVER_assume(c_str);

    /* operation under verification */
    if (aws_array_eq_c_str(array, array_len, c_str)) {
        /* asserts equivalence */
        // assert(array_len == str_len);
        if (array_len > 0) {
            // assert_bytes_match((uint8_t *)array, (uint8_t *)c_str, array_len);
        }
    }

    /* asserts both parameters remain unchanged */
    if (array_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)array, &old_byte_from_array);
    }
    if (str_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)c_str, &old_byte_from_str);
    }
}
