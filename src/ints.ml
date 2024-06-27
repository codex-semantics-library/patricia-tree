(** The integer associated with a key *)
type intkey = int

(** A mask is an integer with a single bit set (i.e. a power of 2). *)
type mask = int

(** Fast highest bit computation in c, using GCC's __builtin_clz
    which compile to efficient instruction (bsr) when possible. *)
external highest_bit: int -> (int[@untagged]) =
  "caml_int_builtin_highest_bit_byte" "caml_int_builtin_highest_bit" [@@noalloc]

let unsigned_lt x y = x - min_int < y - min_int
  (* if x >= 0 && y >= 0
  then x < y
  else if x >= 0
    then (* pos < neg *) true
    else if y >= 0 then false
    else x < y *)

(** Note: in the original version, okasaki give the masks as arguments
    to optimize the computation of highest_bit. *)
let branching_bit a b = highest_bit (a lxor b)

let mask i m = i land (lnot (2*m-1))
