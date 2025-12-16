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

(* Test the order of iteration in functions similar to [iter]. Calls [f
   thunk_intmap thunk_model input] where [thunk_intmap] and [thunk_model] are
   thunks intended to be called by a [iter] function. *)
let make_iter_test name arb f =
  let iter_thunk acc i v = acc := (i, v) :: !acc in
  let acc0 = ref [] and acc1 = ref [] in
  mk name arb
    Print.(list (tup2 int char))
    (fun input ->
      f (iter_thunk acc0) (iter_thunk acc1) input;
      (!acc0, !acc1))

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
  oneofl ~print:fst [ ("fst", fun _ a _ -> a); ("snd", fun _ _ b -> b) ]

(* Like [idempotent_fst_or_snd] but with an extra [None] case. *)
let idempotent_fst_or_snd_option =
  oneofl ~print:fst
    [
      ("-> Some a", fun _ a _ -> Some a);
      ("-> Some b", fun _ _ b -> Some b);
      ("-> None", fun _ _ _ -> None);
    ]

let make_setcmp_test name arb_fun intmap_setcmp model_setcmp =
  mk name (triple arb_fun tree tree) Print.bool (fun (f, t0, t1) ->
      let f = Fn.apply f and t0 = interpret t0 and t1 = interpret t1 in
      (intmap_setcmp f t0 t1, model_setcmp f (abstract t0) (abstract t1)))

let intersect a b = Option.is_some (Intmap.min_binding_inter a b)

let tests =
  [
    mk "is_empty" tree Print.bool (fun t ->
        let t = interpret t in
        (Intmap.is_empty t, Model.is_empty (abstract t)));
    mk "is_singleton" tree
      Print.(option (pair int char))
      (fun t ->
        let t = interpret t in
        (Intmap.is_singleton t, Model.is_singleton (abstract t)));
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
    make_iter_test "fold (ordered)" tree (fun f0 f1 t ->
        let t = interpret t in
        Intmap.fold (fun i v () -> f0 i v) t ();
        Model.fold (fun i v () -> f1 i v) (abstract t) ());
    mk "fold (keys)"
      (triple (fun3 O.int O.char O.int int) tree int)
      Print.int
      (fun (f, t, acc) ->
        let f = Fn.apply f and t = interpret t in
        (Intmap.fold f t acc, Model.fold f (abstract t) acc));
    make_iter_test "iter" tree (fun f0 f1 t ->
        let t = interpret t in
        Intmap.iter f0 t;
        Model.iter f1 (abstract t));
    make_map_test "map" (fun1 O.char char) Intmap.map Model.map;
    make_map_test "mapi" (fun2 O.int O.char char) Intmap.mapi Model.mapi;
    make_map_test "map_no_share" (fun1 O.char char) Intmap.map_no_share
      Model.map;
    make_map_test "mapi_no_share" (fun2 O.int O.char char) Intmap.mapi_no_share
      Model.mapi;
    make_map_test "filter" (fun2 O.int O.char bool) Intmap.filter Model.filter;
    make_map_test "filter_map"
      (fun2 O.int O.char (option char))
      Intmap.filter_map Model.filter_map;
    make_map_test "filter_map_no_share"
      (fun2 O.int O.char (option char))
      Intmap.filter_map_no_share Model.filter_map;
    make_quantifier_test "for_all" Intmap.for_all Model.for_all;
    make_setop_test "idempotent_union" idempotent_fst_or_snd snd
      Intmap.idempotent_union Model.union;
    make_setop_test "idempotent_inter" idempotent_fst_or_snd snd
      Intmap.idempotent_inter Model.inter;
    make_setop_test "idempotent_inter_filter" idempotent_fst_or_snd_option snd
      Intmap.idempotent_inter_filter Model.idempotent_inter_filter;
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
    mk "of_list"
      (list (pair int char))
      print_model
      (fun lst -> (abstract (Intmap.of_list lst), Model.of_list lst));
    mk "of_seq"
      (list (pair int char))
      print_model
      (fun lst ->
        let seq = List.to_seq lst in
        (abstract (Intmap.of_seq seq), Model.of_seq seq));
    mk "add_seq"
      (pair (list (pair int char)) tree)
      print_model
      (fun (lst, tree) ->
        let tree = interpret tree in
        let seq = List.to_seq lst in
        (abstract (Intmap.add_seq seq tree), Model.add_seq seq (abstract tree)));
    mk "to_list" tree
      Print.(list (pair int char))
      (fun tree ->
        let tree = interpret tree in
        (Intmap.to_list tree, Model.to_list (abstract tree)));
    mk "to_seq" tree
      Print.(list (pair int char))
      (fun tree ->
        let tree = interpret tree in
        ( List.of_seq (Intmap.to_seq tree),
          List.of_seq (Model.to_seq (abstract tree)) ));
    mk "to_rev_seq" tree
      Print.(list (pair int char))
      (fun tree ->
        let tree = interpret tree in
        ( List.of_seq (Intmap.to_rev_seq tree),
          List.of_seq (Model.to_rev_seq (abstract tree)) ));
  ]

let _ = QCheck_runner.run_tests ~verbose:true tests
