/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

/*
size_t _strlen(const char *s)
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
*/

void aws_array_eq_c_str_harness() {
    /* assumptions */
    void *array__;
    size_t array_len__;
    // __CPROVER_assume(array_len__ <= 72057594037927935 );
    array__ = malloc(array_len__);
    const char *c_str__ = ensure_c_str_is_allocated(array_len__);

    /* pre-conditions */
    __CPROVER_assume(array__ || (array_len__ == 0));
    __CPROVER_assume(c_str__);

    /* operation under verification */
    aws_array_eq_c_str(array__, array_len__, c_str__);
}
