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

(** {1 Integer manipulations} *)

include Ints

(** {1 Signatures} *)

include Signatures

(** {1 Functors} *)

include Functors

(** {1 Default KEY and VALUE implementations} *)
(** These can be used as parameters to {!MakeMap}/{!MakeSet} functors in the
    most common use cases. *)

include Key_value

(** {1:node_impl Some implementations of NODE} *)
(** We provide a few different implementations of {!NODE}, they can be used with
    the {!MakeCustomMap}, {!MakeCustomSet}, {!MakeCustomHeterogeneousMap} and
    {!MakeCustomHeterogeneousSet} functors. *)

include Nodes
