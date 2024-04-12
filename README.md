# Patricia Tree

This is an [OCaml](https://ocaml.org/) library that implements sets and maps as
Patricia Trees, as described in Oksasaki and Gill's 1998 paper [*Fast mergeable integer maps*](https://www.semanticscholar.org/paper/Fast-Mergeable-Integer-Maps-Okasaki-Gill/23003be706e5f586f23dd7fa5b2a410cc91b659d).
It is a space-efficient prefix trie over the big-endian representation of the key's integer identifier.

## Release status

This should be close to a stable release. It is already being
used as part of a larger project successfully, and this usage as helped us mature
the interface. As is, we believe the project is usable, and we don't anticipate
any major change before 1.0.0. We didn't commit to a stable release straight
away as we would like a bit more time using this library before doing so.

## Features

- Similar to OCaml's `Map` and `Set`, using the same function names when possible
  and the same convention for order of arguments. This should allow switching to
  and from Patricia Tree with minimal effort.
- `Key` module requires an injective `to_int : t -> int` function instead of a
  `compare` function.
- The Patricia Tree representation is stable, contrary to maps, inserting nodes
  in any order will return the same shape.
  This allows different versions of a map to share more subtrees in memory, and
  the operations over two maps to benefit from this sharing. The functions in
  this library attempt to **maximally preserve sharing and benefit from sharing**,
  allowing very important improvements in complexity and running time when
  combining maps or sets is a frequent operation.

  To do so, these functions often have extra requirements on their argument
  (e.g. `inter f m1 m2` can be optimized by not inspecting common subtrees when
  `f` is idempotent). To avoid accidental errors, they are renamed (e.g. to
  `idempotent_inter` for the efficient version and `nonidempotent_inter_no_share`
  for the general one)

- Since our Patricia Tree use big-endian order on keys, the maps and sets are
  sorted in increasing order of keys.
- Supports generic maps and sets: a `'m map` that maps `'k key` to `('k, 'm) value`.
  This is especially useful when using [GADTs](https://v2.ocaml.org/manual/gadts-tutorial.html) for the type of keys.
- Allows easy and fast operations across different types of maps and set (e.g.
  an intersection between a map and a set), since all sets and maps, no matter their key type, are really integer sets or maps.
- Multiple choices for internal representation (`Node`), which allows for efficient
  storage (no need to store a value for sets), or using weak nodes only (values removed from the tree if no other pointer to it exists). This system can also
  be extended to store size information in nodes if needed.
- Exposes a common interface (`view`) to allow users to write their own pattern
  matching on the tree structure without depending on the `Node` being used.

## Known issues

There is a bug in the OCaml typechecker which prevents us from directly
defining non-generic maps as instances of generic maps. To avoid this, non-generic maps use a separate value type (instead of just using `'b`)
```ocaml
type (_, 'b) snd = Snd of 'b [@@unboxed]
```
It should not incur any extra performance cost as it is unboxed, but can appear
when manipulating non-generic maps.

For more details about this issue, see [the OCaml discourse discussion](https://discuss.ocaml.org/t/weird-behaviors-with-first-order-polymorphism/13783)

## Comparison to other OCaml libraries

There are other implementations of Patricia Tree in OCaml, namely
[ptmap](https://github.com/backtracking/ptmap) and
[ptset](https://github.com/backtracking/ptset), both by J.C. Filliatre.
These are smaller and closer to OCaml's built-in Map and Set, however:
- Our library allows using any type `key` that comes with an injective `to_int`
  function, instead of requiring `key = int`.
- We support generic types for keys/elements.
- We support operation between sets and maps of different types.
- We use a big-endian representation, allowing easy access to min/max elements of
  maps and trees.

## Contributions and bug reports

Any contributions are welcome!

You can report any bug, issues, or desired features using the [Github issue tracker](https://github.com/codex-semantics-library/patricia-tree/issues).
Please include OCaml, dune, and Patricia Tree version information in you bug reports.

If you want to contribute code, feel free to fork and open a pull request. By doing
so you agree to release your code under this project's license ([LGPL-2.1](https://choosealicense.com/licenses/lgpl-2.1/)). There is no imposed coding style for this
repository, so use whichever you prefer as long as it is legible. Please consider
adding tests for new features if at all possible.
