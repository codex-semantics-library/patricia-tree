open Signatures

(** {1 Mutex protected sets and maps} *)
(** Some {!NODE} implementations are {b not thread-safe}. Namely {!WeakNode},
    {!WeakSetNode}, {!HashconsedNode} and {!HashconsedSetNode}, as they rely
    on {{: https://ocaml.org/api/Weak.html}[Stdlib.Weak]} hash-sets. This means
    any map or set using these, like {!MakeHashconsedMap}, {!MakeHashconsedSet}
    or their heterogeneous versions, are not thread safe.

    The following functors wrap all interface calls between a {!MUTEX.lock} and
    {!MUTEX.unlock} call, allowing to use these unsafe constructs in a
    multi-threaded context. *)

(** Add {!MUTEX} protection around a {!MAP}.

    @canonical PatriciaTree.MutexProtectMap
    @since 0.12.0 *)
module MutexProtectMap(Map: MAP)(Mutex: MUTEX) : MAP with type key = Map.key

(** Add {!MUTEX} protection around a {!SET}.

    @canonical PatriciaTree.MutexProtectSet
    @since 0.12.0 *)
module MutexProtectSet(Set: SET)(Mutex: MUTEX) : SET with type elt = Set.elt

(** Add {!MUTEX} protection around a {!HETEROGENEOUS_MAP}.

    @canonical PatriciaTree.MutexProtectHeterogeneousMap
    @since 0.12.0 *)
module MutexProtectHeterogeneousMap(Map: HETEROGENEOUS_MAP)(Mutex: MUTEX)
: HETEROGENEOUS_MAP
    with type 'k key = 'k Map.key
     and type ('k, 'm) value = ('k, 'm) Map.value

(** Add {!MUTEX} protection around a {!HETEROGENEOUS_SET}.

    @canonical PatriciaTree.MutexProtectHeterogeneousSet
    @since 0.12.0 *)
module MutexProtectHeterogeneousSet(Set: HETEROGENEOUS_SET)(Mutex: MUTEX)
: HETEROGENEOUS_SET
  with type 'a elt = 'a Set.elt
