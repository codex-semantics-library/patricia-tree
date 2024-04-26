# v0.10.0 - Unreleased

- Renamed `MakeCustom` to `MakeCustomMap`, added new functor `MakeCustomSet`.
- Renamed `MakeCustomHeterogeneous` to `MakeCustomHeterogeneousMap`, added new functor
  `MakeCustomHeterogeneousSet`.
- Added `MAP_WITH_VALUE` interface, similar to `MAP` but replaces `'a` with `'a value`
- `MakeCustomMap` changed to take a new argument to specify the `'a value` type.
- Added `HashconsedNode`, `HashconsedSetNode` as well as four functors to create
  hash-consed heterogeneous/homogeneous maps/sets: `MakeHashconsedMap`, `MakeHashconsedSet`,
  `MakeHashconsedHeterogeneousMap` and `MakeHashconsedHeterogeneousSet`.
- Fixed a bug where `NodeWithId` wasn't incrementing ids properly

# v0.9.0 - 2024-04-18

- Initial release of Patricia Tree
