(**************************************************************************)
(*  This file is part of the Codex semantics library                      *)
(*    (patricia-tree sub-component).                                      *)
(*                                                                        *)
(*  Copyright (C) 2024                                                    *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  You can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file LICENSE).                      *)
(**************************************************************************)

(** Small utilities used to manipulate the integer masks and branching bits *)

type intkey = private int
(** Private type used to represent prefix stored in nodes.
    These are integers with all bits after branching bit (included) set to zero *)

type mask = private int
(** Private type: integers with a single bit set. *)

val unsigned_lt : int -> int -> bool
(** All integers comparisons in this library are done according to their
    {b unsigned representation}. This is the same as signed comparison for same
    sign integers, but all negative integers are greater than the positives.
    This means [-1] is the greatest possible number, and [0] is the smallest.
    {[
    # unsigned_lt 2 (-1);;
    - : bool = true
    # unsigned_lt max_int min_int;;
    - : bool = true
    # unsigned_lt 3 2;;
    - : bool = false
    # unsigned_lt 2 3;;
    - : bool = true
    # unsigned_lt (-2) (-3);;
    - : bool = false
    # unsigned_lt (-4) (-3);;
    - : bool = true
    # unsigned_lt 0 0;;
    - : bool = false
    ]}

    Using this unsigned order helps avoid a bug described in
    {{: https://www.cs.tufts.edu/comp/150FP/archive/jan-midtgaard/qc-patricia.pdf}{i QuickChecking Patricia Trees}}
    by Jan Mitgaard.

    @since v0.10.0 *)

(**/**)
(** For internal use and testing *)

val branching_bit : int -> int -> mask
(** Returns the {!mask} corresponding to the highest bit that differs between
    both arguments. *)

val mask : int -> mask -> intkey
(** Only keeps the bits above mask set *)

external highest_bit: int -> (int[@untagged]) =
  "caml_int_builtin_highest_bit_byte" "caml_int_builtin_highest_bit" [@@noalloc]
(** [highest_bit x] is an integer with a single bit set: the highest set bit of [x].
    exported for test purposes only.

    @since v0.10.0 *)

(**/**)
