/*
 Copyright (c) 2019 - for information on the respective copyright owner
 see the NOTICE file and/or the repository
 https://github.com/boschresearch/blech.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

	 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
*/

#ifndef blech_h
#define blech_h

#include <stdarg.h>
#include <stddef.h>

#include "blechconf.h"


typedef BLC_VOID blc_void;
typedef BLC_BOOL blc_bool;

typedef BLC_INT8 blc_int8;
typedef BLC_INT16 blc_int16;
typedef BLC_INT32 blc_int32;
typedef BLC_INT64 blc_int64;

typedef BLC_NAT8 blc_nat8;
typedef BLC_NAT16 blc_nat16;
typedef BLC_NAT32 blc_nat32;
typedef BLC_NAT64 blc_nat64;

typedef BLC_BITS8 blc_bits8;
typedef BLC_BITS16 blc_bits16;
typedef BLC_BITS32 blc_bits32;
typedef BLC_BITS64 blc_bits64;

typedef BLC_FLOAT32 blc_float32;
typedef BLC_FLOAT64 blc_float64;

typedef BLC_PC_T blc_pc_t;


/* Experiments on built-in types */
#define blc_lenArray(arr) \
    (size_of(arr)/sizeof((arr)[0])  /* TODO: does not work on parameters: fjg 18.02.19 */

/* #define blc_lenSequence(seq) */



/* Program counter magic:
 * 0 means termination of activity / thread
 * Odd pc indicates end of reaction.
 * Even pc = 2i indicates that block i shall be executed now.
 */

/* 0..01 */
#define BLC_ONE (BLC_PC_T)1
/* 1..10 */
#define BLC_BUTONE ~BLC_ONE
/* Goes from 2i + 1 to 2i */
#define BLC_SWITCH_TO_NEXTSTEP(p) p &= BLC_BUTONE
/* Given a k = 2i, set p = 2i + 1. */
/* #define _BLECH_END_STEP(p,k) p = k | _BLECH_ONE */


/*
 * Macro for size-correct number literals
 */

#define BLC_I8(i) (blc_int8)i
#define BLC_I16(i) (blc_int16)i
#define BLC_I32(i) (blc_int32)i
#define BLC_I64(i) (blc_int64)i

#define BLC_N8(n) (blc_nat8)n
#define BLC_N16(n) (blc_nat16)n
#define BLC_N32(n) (blc_nat32)n
#define BLC_N64(n) (blc_nat64)n

#define BLC_B8(b) (blc_bits8)b
#define BLC_B16(b) (blc_bits16)b
#define BLC_B32(b) (blc_bits32)b
#define BLC_B64(b) (blc_bits64)b

#define BLC_F32(f) (blc_float32)f
#define BLC_F64(f) (blc_float64)f

/*
 * Using a void cast, explicitly mark a variable as unused
 */
#define BLC_UNUSED(v) ((void) v)

#endif