(** File run by MDX before running all others, sets up some stuff so the
    comments don't have to *)

open PatriciaTree

type foo

module IntKey = struct
    type 'a t = int
    let to_int x = x
    let polyeq : type a b. a t -> b t -> (a, b) cmp = fun a b ->
        if a == Obj.magic b then Obj.magic Eq else Diff
end
module MyValue = Int
module MyMap = MakeHeterogeneousMap(IntKey)(struct type ('a,'b) t = int end)
