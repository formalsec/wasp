/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/cryptosdk/cipher.h>
#include <aws/cryptosdk/private/cipher.h>
#include <make_common_data_structures.h>

extern int __VERIFIER_nondet_int(char *);

void aws_cryptosdk_genrandom_harness() {
    size_t len = __VERIFIER_nondet_int("len");
    __CPROVER_assume(len < 0xff);

    uint8_t *buf = can_fail_malloc(len);
    __CPROVER_assume(buf != NULL);

    assert(!aws_cryptosdk_genrandom(buf, len));
}
