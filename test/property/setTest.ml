(** Test the Set API. *)

open QCheck

let mk name arb f = Test.check_exn (Test.make ~count:1000 ~name arb f)

module Model = Set.Make (Int)

module TestImpl (Impl : sig
    type 'a elt = int
    type t

    val mem : 'a elt -> t -> bool
    val add : 'a elt -> t -> t
  end) () = struct

  let set = list int

  let abstract 

let () =
  mk "mem"

    end

module _ = TestImpl (PatriciaTree.MakeSet (struct
    type t = int
    let to_int x = x
  end)) ()

module _ = TestImpl (PatriciaTree.MakeHeterogeneousSet (struct
    type 'a t = int
    let to_int x = x
  end)) ()
