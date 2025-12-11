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

let singleton_test =
  mk "singleton" (pair small_nat char) print_model @@ fun (n, c) ->
  (abstract (Intmap.singleton n c), Model.singleton n c)

let compare_test =
  mk "compare" two Print.bool @@ fun (t0, t1) ->
  let t0 = interpret t0 and t1 = interpret t1 in
  ( Intmap.reflexive_compare Char.compare t0 t1 = 0,
    Model.compare Char.compare (abstract t0) (abstract t1) = 0 )

let equal_test =
  mk "equal" two Print.bool @@ fun (t0, t1) ->
  let t0 = interpret t0 and t1 = interpret t1 in
  ( Intmap.reflexive_equal ( = ) t0 t1,
    Model.equal ( = ) (abstract t0) (abstract t1) )

let cardinal_test =
  mk "cardinal" tree Print.int @@ fun t ->
  let t = interpret t in
  (Intmap.cardinal t, Model.size (abstract t))

let mem_test =
  mk "mem" key_and_tree Print.bool @@ fun (i, t) ->
  let t = interpret t in
  (Intmap.mem i t, Model.mem i (abstract t))

let find_test =
  mk "find" key_and_tree Print.(result char print_exn) @@ fun (i, t) ->
  let t = interpret t in
  let a = protect @@ fun () -> Intmap.find i t
  and b = protect @@ fun () -> Model.find i (abstract t) in
  (a, b)

let add_test =
  mk "add" (pair char key_and_tree) print_model @@ fun (c, (i, t)) ->
  let t = interpret t in
  (abstract (Intmap.add i c t), Model.add i c (abstract t))

let remove_test =
  mk "remove" key_and_tree print_model @@ fun (i, t) ->
  let t = interpret t in
  (abstract (Intmap.remove i t), Model.remove i (abstract t))

let insert_test =
  mk "insert"
    (quad small_nat (fun2 O.char O.(option char) char) char tree)
    print_model
  @@ fun (i, f, c, t) ->
  let f = Fn.apply f c and t = interpret t in
  (abstract (Intmap.insert i f t), Model.insert i f (abstract t))

let update_test =
  mk "update"
    (tup3 small_nat (fun1 O.(option char) (option char)) tree)
    print_model
  @@ fun (i, f, t) ->
  let f = Fn.apply f and t = interpret t in
  (abstract (Intmap.update i f t), Model.update i f (abstract t))

let fold_cumulative_test =
  let f _i v acc = Char.code v + acc in
  mk "fold (cumulative)" (pair tree int) Print.int @@ fun (t, acc) ->
  let t = interpret t in
  (Intmap.fold f t acc, Model.fold f (abstract t) acc)

let fold_ordered_test =
  let f _i v acc = v :: acc in
  mk "fold (ordered)" (pair tree (list char)) Print.(list char)
  @@ fun (t, acc) ->
  let t = interpret t in
  (Intmap.fold f t acc, Model.fold f (abstract t) acc)

let fold_keys_test =
  mk "fold (keys)" (triple (fun3 O.int O.char O.int int) tree int) Print.int
  @@ fun (f, t, acc) ->
  let f = Fn.apply f and t = interpret t in
  (Intmap.fold f t acc, Model.fold f (abstract t) acc)

let iter_test =
  let f acc i v = acc := (i, v) :: !acc in
  mk "iter" tree Print.(list (tup2 int char)) @@ fun t ->
  let t = interpret t in
  let acc0 = ref [] and acc1 = ref [] in
  Intmap.iter (f acc0) t;
  Model.iter (f acc1) (abstract t);
  (!acc0, !acc1)

let make_map_test name arb intmap_map model_map =
  mk name (pair arb tree) print_model @@ fun (f, t) ->
  let f = Fn.apply f and t = interpret t in
  (abstract (intmap_map f t), model_map f (abstract t))

let map_test = make_map_test "map" (fun1 O.char char) Intmap.map Model.map

let mapi_test =
  make_map_test "mapi" (fun2 O.int O.char char) Intmap.mapi Model.mapi

let filter_test =
  make_map_test "filter" (fun2 O.int O.char bool) Intmap.filter Model.filter

let make_quantifier_test name intmap_quant model_quant =
  mk name (pair (fun2 O.int O.char bool) tree) Print.bool @@ fun (p, t) ->
  let p = Fn.apply p and t = interpret t in
  (intmap_quant p t, model_quant p (abstract t))

let for_all_test = make_quantifier_test "for_all" Intmap.for_all Model.for_all

let make_setop_test name fun_arb intmap_op model_op =
  mk name (triple fun_arb tree tree) print_model @@ fun (f, t0, t1) ->
  let f = Fn.apply f and t0 = interpret t0 and t1 = interpret t1 in
  (abstract (intmap_op f t0 t1), model_op f (abstract t0) (abstract t1))

let union_test =
  make_setop_test "idempotent_union"
    (fun3 O.int O.char O.char char)
    Intmap.idempotent_union Model.union

let inter_test =
  make_setop_test "idempotent_inter"
    (fun3 O.int O.char O.char char)
    Intmap.idempotent_inter Model.inter

let interf_test =
  make_setop_test "idempotent_inter_filter"
    (fun3 O.int O.char O.char (option char))
    Intmap.idempotent_inter_filter Model.interf

let diff_test =
  make_setop_test "different"
    (fun3 O.int O.char O.char (option char))
    Intmap.difference Model.diff

let make_setcmp_test name arb_fun intmap_setcmp model_setcmp =
  mk name (triple arb_fun tree tree) Print.bool @@ fun (f, t0, t1) ->
  let f = Fn.apply f and t0 = interpret t0 and t1 = interpret t1 in
  (intmap_setcmp f t0 t1, model_setcmp f (abstract t0) (abstract t1))

let subset_test =
  make_setcmp_test "reflexive_subset_domain_for_all2"
    (fun3 O.int O.char O.char bool)
    Intmap.reflexive_subset_domain_for_all2 Model.subset

let intersect a b = Option.is_some (Intmap.min_binding_inter a b)

let intersect_test =
  mk "intersect" (pair tree tree) Print.bool @@ fun (t0, t1) ->
  let t0 = interpret t0 and t1 = interpret t1 in
  (intersect t0 t1, Model.intersect (abstract t0) (abstract t1))

let merge_test =
  make_setop_test "slow_merge"
    (fun3 O.int O.(option char) O.(option char) (option char))
    Intmap.slow_merge Model.merge

let tests =
  [
    singleton_test;
    compare_test;
    equal_test;
    cardinal_test;
    mem_test;
    find_test;
    add_test;
    remove_test;
    insert_test;
    update_test;
    fold_cumulative_test;
    fold_ordered_test;
    fold_keys_test;
    iter_test;
    map_test;
    mapi_test;
    filter_test;
    for_all_test;
    union_test;
    inter_test;
    interf_test;
    subset_test;
    intersect_test;
    diff_test;
    merge_test;
  ]

let _ = QCheck_runner.run_tests ~verbose:true tests
