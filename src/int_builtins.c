/**************************************************************************/
/*  This file is part of the Codex semantics library                      */
/*    (patricia-tree sub-component).                                      */
/*                                                                        */
/*                                                                        */
/*  Copyright (C) 2013-2026                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  You can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

#ifdef _MSC_VER
#include <intrin.h>
#endif

__attribute__((__always_inline__))
static inline uintnat clz(uintnat v){
  /* Note: on a 64 bit platform, GCC's _builtin_clz will perform a 32
     bit operation (even if the argument has type int). We have to use
     _builtin_clzll instead. */
#if __GNUC__
  #ifdef ARCH_SIXTYFOUR
    return __builtin_clzll(v);
  #else
    return __builtin_clz(v);
  #endif
#endif
#ifdef _MSC_VER
    int res = 0;     
  #ifdef ARCH_SIXTYFOUR  
    _BitScanReverse64(&res,v);
  #else
    _BitScanReverse(&res,v);
  #endif
    return res;
#endif
}

/**************** Highest bit ****************/

CAMLprim uintnat  caml_int_builtin_highest_bit (value i){
  /* printf("Highest bit In C: %x %x %x %x\n", */
  /* 	 i, i >> 1, 62-clz(i), 1 << (62 - clz(i))); */
  /* fflush(stdout); */
  return ((uintnat) 1 << (8*sizeof(value) - 2 - clz(i)));
}

CAMLprim value caml_int_builtin_highest_bit_byte (value i){
  return Val_int(caml_int_builtin_highest_bit(i));
}
