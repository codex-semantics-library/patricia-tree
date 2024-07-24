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

(** Association maps from key to values, and sets, implemented with
    Patricia Trees, allowing fast merge operations by making use of
    physical equality between subtrees; and custom implementation of
    {{!node_impl}tree nodes} (allowing normal maps, {{!hash_consed}hash-consed maps}, weak key or
    value maps, sets, custom maps, etc.).

    The main entry points into this library are the functors that build maps
    and sets:
    {table
      {tr
        {th }
        {th Map}
        {th Set}
      }
      {tr
        {th Homogeneous}
        {td {!MakeMap}}
        {td {!MakeSet}}
      }
      {tr
        {th Heterogeneous}
        {td {!MakeHeterogeneousMap}}
        {td {!MakeHeterogeneousSet}}
      }
      {tr
        {th {{!hash_consed}Hash-consed} Homogeneous}
        {td {!MakeHashconsedMap}}
        {td {!MakeHashconsedSet}}
      }
      {tr
        {th {{!hash_consed}Hash-consed} Heterogeneous}
        {td {!MakeHashconsedHeterogeneousMap}}
        {td {!MakeHashconsedHeterogeneousSet}}
      }
    }


    Differences between this library and OCaml's {{: https://ocaml.org/api/Map.S.html}[Map]} include:

    {ul
    {- The required signature for keys is different, in that we require
      each key to be mapped to a unique integer identifier.}

    {- The implementation uses Patricia Tree, as described in Okasaki
      and Gill's 1998 paper
      {{: https://www.semanticscholar.org/paper/Fast-Mergeable-Integer-Maps-Okasaki-Gill/23003be706e5f586f23dd7fa5b2a410cc91b659d}{i Fast mergeable integer maps}},
      i.e. it is a space-efficient prefix trie over the big-endian representation of
      the key's integer identifier.

      Example of a 5-bit patricia tree containing five numbers: 0 [0b0000], 1 [0b0001],
      5 [0b0101] and 7 [0b0111] and -8 [0b1111]:
      {v
                              Branch
                          (prefix=0b?___)
                          /             \
                    Branch               Leaf(-8)
                (prefix=0b0?__)          0b1111
                /             \
           Branch             Branch
       (prefix=0b000?)     (prefix=0b01?_)
         |        |          |       |
      Leaf(0)  Leaf(1)    Leaf(5)  Leaf(7)
      0b0000   0b0001     0b0101   0b0111
      v}

      The main benefit of Patricia Tree is that their representation
      is stable (contrary to maps, inserting nodes in any order will
      return the same shape), which allows different versions of a map
      to share more subtrees in memory, and the
      {{!BASE_MAP.functions_on_pairs}operations over two maps}
      to benefit from this sharing. The functions in this library
      attempt to maximally preserve sharing and benefit from sharing,
      allowing very important improvements in complexity and running
      time when combining maps or sets is a frequent operation.}

    {- Finally, the implementation is more customizable, allowing
      notably (key,value) pairs or different types to be in the same map,
      or to choose the memory representation of the nodes of the tree.}

    {- Some operations like {{!BASE_MAP.pop_unsigned_minimum}[pop_unsigned_minimum]} and
     {{!BASE_MAP.pop_unsigned_maximum}[pop_unsigned_maximum]} make our Set
     suitable as priority queue (but remember that each element in the
     queue must map to a distinct integer, and that using the {{!unsigned_lt}unsigned order}
     means elements with negative priority are seen as greater than elements with
     positive ones).}
    }

    {b Note on complexity:} in the following, n represents the size of the
    map when there is one (and [|map1|] is the number of elements in
    [map1]).  The term log(n) correspond to the maximum height of the
    tree, which is log(n) if we assume an even distribution of numbers
    in the map (e.g. random distribution, or integers chosen
    contiguously using a counter). The worst-case height is
    O(min(n,64)) which is actually constant, but not really
    informative; log(n) corresponds to the real complexity in usual
    distributions. *)

(** {1 Integer manipulations} *)

include module type of Ints

(** {1 Signatures} *)

include module type of Signatures

(** {1 Functors} *)

include module type of Functors

(** {1 Default KEY and VALUE implementations} *)
(** These can be used as parameters to {!MakeMap}/{!MakeSet} functors in the
    most common use cases. *)

include module type of Key_value

(** {1:node_impl Some implementations of NODE} *)
(** We provide a few different implementations of {!NODE}, the internal representation
    of a PatriciaTree's nodes. They can be used with
    the {!MakeCustomMap}, {!MakeCustomSet}, {!MakeCustomHeterogeneousMap} and
    {!MakeCustomHeterogeneousSet} functors to build maps and sets with custom
    internal representation. *)

include module type of Nodes
