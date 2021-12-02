/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

bool _strcmp(const char *s1, const char *s2)
{
  size_t i=0;
  char ch1, ch2;
  
  while(ch1!=0 && ch2!=0)
    __CPROVER_loop_invariant (
        (i >= 0))
    __CPROVER_loop_invariant( (i <= __CPROVER_OBJECT_SIZE(s1)) && (i <= __CPROVER_OBJECT_SIZE(s2)))
    __CPROVER_loop_invariant((i == 0) || (ch1 == s1[i-1]))
    __CPROVER_loop_invariant((i == 0) || (ch2 == s2[i-1]))
    /*__CPROVER_loop_invariant(__CPROVER_forall {
            size_t k;
            (0 <= k && k < 10) ==> ((k < i) ==> ((s1[k] != '\0') && (s2[k] != '\0')))
        }
    )*/
  {
    ch1=s1[i];
    ch2=s2[i];
    if(ch1==ch2)
    {
    }
    else if(ch1<ch2)
      return -1;
    else
      return 1;

    i++;
  }
    
  return 0;
}

void aws_hash_callback_c_str_eq_harness() {
    size_t bound;
    const char *str1 = ensure_c_str_is_allocated(bound);
    const char *str2 = nondet_bool() ? str1 : ensure_c_str_is_allocated(bound);

    __CPROVER_assume(aws_c_string_is_valid(str1));
    __CPROVER_assume(aws_c_string_is_valid(str2));

    bool rval = aws_hash_callback_c_str_eq(str1, str2);
    if (rval) {
        // size_t len = strlen(str1);
        // assert_bytes_match(str1, str2, len);
    }
}
