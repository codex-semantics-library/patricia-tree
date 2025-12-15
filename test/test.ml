let tree = Symbolic.tree
let two = Symbolic.two
let protect call = try Ok (call ()) with e -> Result.error e

open QCheck
module O = Observable

module Intmap = PatriciaTree.MakeMap (struct
  type t = int

  let to_int = Fun.id
end)

let rec interpret = function
  | Symbolic.Empty -> Intmap.empty
  | Singleton (i, a) -> Intmap.singleton i a
  | Add (i, a, m) -> Intmap.add i a @@ interpret m
  | Remove (i, m) -> Intmap.remove i @@ interpret m
  | Union (f, m0, m1) ->
      let t0 = interpret m0 and t1 = interpret m1 in
      Intmap.idempotent_union f t0 t1
  | Inter (f, m0, m1) ->
      let t0 = interpret m0 and t1 = interpret m1 in
      Intmap.idempotent_inter f t0 t1
  | Merge (f, m0, m1) ->
      let t0 = interpret m0 and t1 = interpret m1 in
      Intmap.slow_merge f t0 t1

let abstract t =
  let aux i a acc = (i, a) :: acc in
  List.sort Model.cmp_keys @@ Intmap.fold aux t []

let key_and_tree =
  let open QCheck.Gen in
  let open Symbolic in
  let gen =
    let* t = tree.gen in
    match Model.keys @@ abstract @@ interpret t with
    | [] -> pair key (return t)
    | keys -> oneof [ pair key (return t); pair (oneofl keys) (return t) ]
  in
  let print (k, tree) = Int.to_string k ^ ", " ^ print tree in
  QCheck.make ~print gen

let print_model = QCheck.Print.(list (pair int char))
let print_exn = Printexc.to_string
let count = 1000

(** Make a QCheck test that fails if the two values returned by [f] are not
    equal. Compared to using [Test.make], this prints the two unequal values
    when the test fails. [f] returns [(output, model)] where [output] is the
    output of the function being tested and [model] is the output expected by
    the model. [print_model] prints [output] and [model]. *)
let mk ?(count = count) ?(test_fun = ( = )) name arbitrary print_model f =
  Test.make ~name ~count arbitrary @@ fun input ->
  let r0, r1 = f input in
  if not (test_fun r0 r1) then
    Test.fail_reportf "Output:\n%s\n\nModel:\n%s" (print_model r0)
      (print_model r1);
  true

(* Test functions similar to [map] or [filter]. *)
let make_map_test name arb intmap_map model_map =
  mk name (pair arb tree) print_model (fun (f, t) ->
      let f = Fn.apply f and t = interpret t in
      (abstract (intmap_map f t), model_map f (abstract t)))

(* Test functions similar to [for_all]. *)
let make_quantifier_test name intmap_quant model_quant =
  mk name
    (pair (fun2 O.int O.char bool) tree)
    Print.bool
    (fun (p, t) ->
      let p = Fn.apply p and t = interpret t in
      (intmap_quant p t, model_quant p (abstract t)))

(* Test set operations. *)
let make_setop_test name fun_arb fun_apply intmap_op model_op =
  mk name (triple fun_arb tree tree) print_model (fun (f, t0, t1) ->
      let f = fun_apply f and t0 = interpret t0 and t1 = interpret t1 in
      (abstract (intmap_op f t0 t1), model_op f (abstract t0) (abstract t1)))

(* Arbitrary functions cannot be passed to idempotent set operations. The
   implementation uses physical equality to perform optimisations, which are
   hard to model. Only two reconciliation functions are used. *)
let idempotent_fst_or_snd =
  choose
    [
      always ~print:(fun _ -> "fst") (fun _ a _ -> a);
      always ~print:(fun _ -> "snd") (fun _ _ b -> b);
    ]

(* Like [idempotent_fst_or_snd] but with an extra [None] case. *)
let idempotent_fst_or_snd_option =
  choose
    [
      always ~print:(fun _ -> "-> Some a") (fun _ a _ -> Some a);
      always ~print:(fun _ -> "-> Some b") (fun _ _ b -> Some b);
      always ~print:(fun _ -> "-> None") (fun _ _ b -> Some b);
    ]

let make_setcmp_test name arb_fun intmap_setcmp model_setcmp =
  mk name (triple arb_fun tree tree) Print.bool (fun (f, t0, t1) ->
      let f = Fn.apply f and t0 = interpret t0 and t1 = interpret t1 in
      (intmap_setcmp f t0 t1, model_setcmp f (abstract t0) (abstract t1)))

let intersect a b = Option.is_some (Intmap.min_binding_inter a b)

let tests =
  [
    mk "singleton" (pair small_nat char) print_model (fun (n, c) ->
        (abstract (Intmap.singleton n c), Model.singleton n c));
    mk "compare" two Print.bool (fun (t0, t1) ->
        let t0 = interpret t0 and t1 = interpret t1 in
        ( Intmap.reflexive_compare Char.compare t0 t1 = 0,
          Model.compare Char.compare (abstract t0) (abstract t1) = 0 ));
    mk "equal" two Print.bool (fun (t0, t1) ->
        let t0 = interpret t0 and t1 = interpret t1 in
        ( Intmap.reflexive_equal ( = ) t0 t1,
          Model.equal ( = ) (abstract t0) (abstract t1) ));
    mk "cardinal" tree Print.int (fun t ->
        let t = interpret t in
        (Intmap.cardinal t, Model.size (abstract t)));
    mk "mem" key_and_tree Print.bool (fun (i, t) ->
        let t = interpret t in
        (Intmap.mem i t, Model.mem i (abstract t)));
    mk "find" key_and_tree
      Print.(result char print_exn)
      (fun (i, t) ->
        let t = interpret t in
        ( protect (fun () -> Intmap.find i t),
          protect (fun () -> Model.find i (abstract t)) ));
    mk "add" (pair char key_and_tree) print_model (fun (c, (i, t)) ->
        let t = interpret t in
        (abstract (Intmap.add i c t), Model.add i c (abstract t)));
    mk "remove" key_and_tree print_model (fun (i, t) ->
        let t = interpret t in
        (abstract (Intmap.remove i t), Model.remove i (abstract t)));
    mk "insert"
      (quad small_nat (fun2 O.char O.(option char) char) char tree)
      print_model
      (fun (i, f, c, t) ->
        let f = Fn.apply f c and t = interpret t in
        (abstract (Intmap.insert i f t), Model.insert i f (abstract t)));
    mk "update"
      (tup3 small_nat (fun1 O.(option char) (option char)) tree)
      print_model
      (fun (i, f, t) ->
        let f = Fn.apply f and t = interpret t in
        (abstract (Intmap.update i f t), Model.update i f (abstract t)));
    mk "fold (cumulative)" (pair tree int) Print.int (fun (t, acc) ->
        let f _i v acc = Char.code v + acc in
        let t = interpret t in
        (Intmap.fold f t acc, Model.fold f (abstract t) acc));
    mk "fold (ordered)"
      (pair tree (list char))
      Print.(list char)
      (fun (t, acc) ->
        let f _i v acc = v :: acc in
        let t = interpret t in
        (Intmap.fold f t acc, Model.fold f (abstract t) acc));
    mk "fold (keys)"
      (triple (fun3 O.int O.char O.int int) tree int)
      Print.int
      (fun (f, t, acc) ->
        let f = Fn.apply f and t = interpret t in
        (Intmap.fold f t acc, Model.fold f (abstract t) acc));
    mk "iter" tree
      Print.(list (tup2 int char))
      (fun t ->
        let f acc i v = acc := (i, v) :: !acc in
        let t = interpret t in
        let acc0 = ref [] and acc1 = ref [] in
        Intmap.iter (f acc0) t;
        Model.iter (f acc1) (abstract t);
        (!acc0, !acc1));
    make_map_test "map" (fun1 O.char char) Intmap.map Model.map;
    make_map_test "mapi" (fun2 O.int O.char char) Intmap.mapi Model.mapi;
    make_map_test "filter" (fun2 O.int O.char bool) Intmap.filter Model.filter;
    make_quantifier_test "for_all" Intmap.for_all Model.for_all;
    make_setop_test "idempotent_union" idempotent_fst_or_snd Fun.id
      Intmap.idempotent_union Model.union;
    make_setop_test "idempotent_inter" idempotent_fst_or_snd Fun.id
      Intmap.idempotent_inter Model.inter;
    make_setop_test "idempotent_inter_filter" idempotent_fst_or_snd_option
      Fun.id Intmap.idempotent_inter_filter Model.interf;
    make_setop_test "different"
      (fun3 O.int O.char O.char (option char))
      Fn.apply Intmap.difference Model.diff;
    make_setcmp_test "reflexive_subset_domain_for_all2"
      (fun3 O.int O.char O.char bool)
      Intmap.reflexive_subset_domain_for_all2 Model.subset;
    mk "intersect" (pair tree tree) Print.bool (fun (t0, t1) ->
        let t0 = interpret t0 and t1 = interpret t1 in
        (intersect t0 t1, Model.intersect (abstract t0) (abstract t1)));
    make_setop_test "slow_merge"
      (fun3 O.int O.(option char) O.(option char) (option char))
      Fn.apply Intmap.slow_merge Model.merge;
  ]

let _ = QCheck_runner.run_tests ~verbose:true tests
