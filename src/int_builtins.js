/* ************************************************************************ */
/*   This file is part of the Codex semantics library                       */
/*     (patricia-tree sub-component).                                       */
/*                                                                          */
/*                                                                          */
/*   Copyright (C) 2013-2026                                                */
/*     CEA (Commissariat à l'énergie atomique et aux énergies               */
/*          alternatives)                                                   */
/*                                                                          */
/*   You can redistribute it and/or modify it under the terms of the GNU    */
/*   Lesser General Public License as published by the Free Software        */
/*   Foundation, version 2.1.                                               */
/*                                                                          */
/*   It is distributed in the hope that it will be useful,                  */
/*   but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/*   GNU Lesser General Public License for more details.                    */
/*                                                                          */
/*   See the GNU Lesser General Public License version 2.1                  */
/*   for more details (enclosed in the file LICENSE).                       */
/*                                                                          */
/* ************************************************************************ */

// Implement the C stubs from int_builtins.c in JS
// See https://ocsigen.org/js_of_ocaml/latest/manual/linker for how this works
// as well as required annotations

//Provides: caml_int_builtin_highest_bit_byte const
function caml_int_builtin_highest_bit_byte(x) {
  if (x === 0) return 0;
  return 1 << (31 - Math.clz32(x));
}
