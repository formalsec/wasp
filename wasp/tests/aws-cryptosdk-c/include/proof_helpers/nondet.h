/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <assert.h>

/**
 * Non-determinstic functions used in CBMC proofs
 */
bool nondet_bool();
int nondet_int();
size_t nondet_size_t();
uint16_t nondet_uint16_t();
uint32_t nondet_uint32_t();
uint64_t nondet_uint64_t();
uint8_t nondet_uint8_t();
void *nondet_voidp();

void __CPROVER_assume(bool assumption);
void __CPROVER_assert(bool assertion, const char *description);
size_t __CPROVER_OBJECT_SIZE(const void *p);
