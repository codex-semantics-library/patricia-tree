# v0.10.0 - Unreleased

- Renamed `MakeCustom` to `MakeCustomMap`, added new functor `MakeCustomSet`.
- Renamed `MakeCustomHeterogeneous` to `MakeCustomHeterogeneousMap`, added new functor
  `MakeCustomHeterogeneousSet`.
- Added `MAP_WITH_VALUE` interface, similar to `MAP` but replaces `'a` with `'a value`
- `MakeCustomMap` changed to take a new argument to specify the `'a value` type.
- Added `HashconsedNode`, `HashconsedSetNode` as well as four functors to create
  hash-consed heterogeneous/homogeneous maps/sets: `MakeHashconsedMap`, `MakeHashconsedSet`,
  `MakeHashconsedHeterogeneousMap` and `MakeHashconsedHeterogeneousSet`.
- Patricia Tree now support using negative keys. Tree are built using the bitwise representation
  of integer, meaning they effectively use an unsigned order. Negative keys are
  considered bigger than positive keys, `0` is the minimal number and `-1` the maximal one.
- Renamed `min_binding`, `max_binding`, `pop_minimum`, `pop_maximum`, `min_elt`
  and `max_elt` to `unsigned_min_binding`, `unsigned_max_binding`,
  `pop_unsigned_minimum`, `pop_unsigned_maximum`, `unsigned_min_elt`
  and `unsigned_max_elt` respectively, to clarify that these functions consider
  negative numbers as larger than positive ones.
- Fixed a bug where `NodeWithId` wasn't incrementing ids properly
- `zarith` is no longer a dependency, used GCC's `__builtin_clz` as a faster
  method of finding an integer's highest bit.

# v0.9.0 - 2024-04-18

- Initial release of Patricia Tree
