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
