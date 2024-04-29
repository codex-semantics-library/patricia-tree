(**************************************************************************)
(*  This file is part of the Codex semantics library                      *)
(*    (patricia-tree sub-component).                                      *)
(*                                                                        *)
(*  Copyright (C) 2024                                                    *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  You can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file LICENSE).                      *)
(**************************************************************************)

open PatriciaTree

let%test_module "TestHeterogeneous" = (module struct

  module MyKey = struct
    type 'a t =
      | Int: int -> int t
      | Bool: bool -> bool t

    let to_int (type a) (key:a t):int = match key with
      | Bool false -> 1
      | Bool true -> 3
      | Int x -> (x lsl 1)

    let polyeq: type a b. a t -> b t -> (a,b) cmp = fun a b -> match a,b with
      | Bool _, Int _ -> Diff
      | Int _, Bool _ -> Diff
      | Bool a, Bool b -> if a == b then Eq else Diff
      | Int a, Int b -> if a == b then Eq else Diff
  end

  type a = |
  type b = |

  module MyValue = struct
    type ('a,'b) t =
      | AString: string -> (int,a) t
      | APair: (int * int) -> (bool,a) t
      | BInt: int -> (int,b) t
      | BString: string -> (bool,b) t
  end


  module Map = MakeCustomHeterogeneous(MyKey)(MyValue)(SimpleNode(MyKey)(MyValue))
  open Map

  let _m1 = singleton (MyKey.Int 7) (MyValue.AString "seven")
  let _m1 = add (MyKey.Bool false) (MyValue.APair (11,22)) _m1
  let _m1 = remove (MyKey.Int 7) _m1

  let _m2 = singleton (MyKey.Int 7) (MyValue.BInt 21)
  let _m2 = add (MyKey.Bool true) (MyValue.BString "hello") _m2


  (* Here we redefine a node to store key and value a flat way, which
     should decrease the amount of allocations. *)
  module OptimizedNode : NODE
    with type 'key key = 'key MyKey.t
     and type ('key,'map) value = ('key,'map) MyValue.t
  = struct

    type 'a key = 'a MyKey.t
    type ('key,'map) value = ('key,'map) MyValue.t

    type 'map view =
      | Empty: 'map view                      (* Does not appear below interior nodes. *)
      | Branch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map view
      | Leaf: {key:'key key; value:('key,'map) value} -> 'map view            (* The entire key. *)

    and 'map t =
      | NEmpty: 'map t
      | NBranch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map t
      | LeafAString: (int * string) -> a t
      | LeafAPair: (bool * int * int) -> a t
      | LeafBInt: (int * int) -> b t
      | LeafBString: (bool * string) -> b t

    let view: type map. map t -> map view = function
      | LeafAString(a,s) -> Leaf{key=MyKey.Int a;value=MyValue.AString s}
      | LeafAPair(b,p1,p2) -> Leaf{key=MyKey.Bool b;value=MyValue.APair(p1,p2)}
      | LeafBInt(a,s) -> Leaf{key=MyKey.Int a;value=MyValue.BInt s}
      | LeafBString(a,s) -> Leaf{key=MyKey.Bool a;value=MyValue.BString s}
      | NBranch{prefix;branching_bit;tree0;tree1} -> Branch{prefix;branching_bit;tree0;tree1}
      | NEmpty -> Empty

    let empty:'map t = NEmpty
    let is_empty (x:'map t) = x == NEmpty
    let leaf: type a map. a key -> (a,map) value -> map t =
      fun key value -> match key,value with
        | MyKey.Int a, MyValue.AString s -> LeafAString(a,s)
        | MyKey.Bool b, MyValue.APair(p1,p2) -> LeafAPair(b,p1,p2)                                              | MyKey.Int a, MyValue.BInt s -> LeafBInt(a,s)
        | MyKey.Bool a, MyValue.BString s -> LeafBString(a,s)

    let branch ~prefix ~branching_bit ~tree0 ~tree1 =
      match (tree0:'map t),(tree1:'map t) with
      | NEmpty, x -> x
      | x, NEmpty -> x
      | _ -> NBranch{prefix;branching_bit;tree0;tree1}
  end

  module Map2 = MakeCustomHeterogeneous(MyKey)(MyValue)(SimpleNode(MyKey)(MyValue))
  open Map2

  let _m1 = singleton (MyKey.Int 7) (MyValue.AString "seven")
  let _m1 = add (MyKey.Bool false) (MyValue.APair (11,22)) _m1
  let _m1 = remove (MyKey.Int 7) _m1

  let _m2 = singleton (MyKey.Int 7) (MyValue.BInt 21)
  let _m2 = add (MyKey.Bool true) (MyValue.BString "hello") _m2
end)

(* module IntKey = struct  type 'a t = Int: int -> 'a t [@@unboxed];; let to_int (Int x) = x end *)
(* module Test = Make(IntKey)(SimpleNode(IntKey)) *)
(* open Test;; *)

(* (\**************** Tests ****************\) *)
(* let _m1 = singleton (IntKey.Int 7) 1;; *)
(* let _m1 = add (IntKey.Int 3) 2 _m1;; *)
(* let _m1 = remove (IntKey.Int 7) _m1;; *)

(* let _m1 = singleton (7) 1;; *)
(* let _m1 = add (3) 2 _m1;; *)
(* let _m1 = remove (7) _m1;; *)



(* let _m2 = singleton 4 3;; *)
(* let _m2 = add 10 4 _m2;; *)

(* let _m3 = union (Obj.magic 0) _m1 _m2;; *)

(* (\* let m8 = m1;; *\) *)
(* let _m4 = inter (fun a b -> a) _m1 _m3;; *)
(* let _m5 = inter (fun a b -> a) _m2 _m3;; *)

(* let _m6 = inter (fun a b -> a) _m1 _m2;; *)
let unsigned_compare x y =
  if unsigned_lt x y then -1
  else if x = y then 0 else 1

let%test_module _ = (module struct

  (* A model. *)
  module IntMap = struct
    module M = Map.Make(struct
      type t = int
      let compare = unsigned_compare
    end)
    include M
    let subset_domain_for_all_2 m1 m2 f =
      let exception False in
      try
        let res = M.merge (fun key v1 v2 -> match v1,v2 with
            | None, None -> assert false
            | Some _, None -> raise False
            | None, Some _ -> None
            | Some v1, Some v2 ->
              if f key v1 v2 then None else raise False) m1 m2 in
        assert (M.is_empty res);
        true
      with False -> false

    let same_domain_for_all_2 m1 m2 f =
      let exception False in
      try
        let res = M.merge (fun key v1 v2 -> match v1,v2 with
            | None, None -> assert false
            | Some _, None -> raise False
            | None, Some _ -> raise False
            | Some v1, Some v2 ->
              if f key v1 v2 then None else raise False) m1 m2 in
        assert (M.is_empty res);
        true
      with False -> false

    let inter m1 m2 f =
      M.merge (fun key a b ->
          match a,b with
          | None, _ | _, None -> None
          | Some a, Some b -> Some (f key a b)) m1 m2

    let update_multiple_from_foreign m1 m2 f =
      M.merge (fun key a b ->
          match a, b with
          | a, None -> a
          | a, Some b -> f key a b) m1 m2

    let update_multiple_from_inter_with_foreign m1 m2 f =
      M.fold (fun key value acc ->
          match M.find key acc with
          | exception Not_found -> acc
          | v -> begin match f key v value with
              | None -> M.remove key acc
              | Some v' -> M.add key v' acc
            end) m2 m1

    let inter_filter m1 m2 f =
      M.merge (fun key a b ->
          match a,b with
          | None, _ | _, None -> None
          | Some a, Some b -> (f key a b)) m1 m2

    let pop_minimum m =
      match M.min_binding m with
      | exception Not_found -> None
      | (key,value) -> Some(key,value,M.remove key m)

    let pop_maximum m =
      match M.max_binding m with
      | exception Not_found -> None
      | (key,value) -> Some(key,value,M.remove key m)
  end

  (* An implementation. *)
  module IntValue : sig
    type ('a, 'b) t = int
    val pretty : Format.formatter -> ('a, 'b) t -> unit
  end = struct
    type ('a,'b) t = int
    let pretty fmt x = Format.pp_print_int fmt x
  end

  module HIntKey : sig
    type t = int
    val to_int : t -> int
  end = struct
    type t = int
    let to_int x = x
  end

  (* module MyMap = Make(SimpleNode(IntKey)(IntValue))(IntKey)(IntValue);; *)
  module MyMap = MakeMap(HIntKey)

  (* Add a list of pair of ints to a map. *)
  let rec extend_map mymap alist =
    match alist with
    | [] -> mymap
    | (a,b)::rest ->
      extend_map (MyMap.add a b mymap) rest

  let intmap_of_mymap m =
    MyMap.fold (fun key value acc -> IntMap.add key value acc) m IntMap.empty

  let two_maps_from_three_lists (alist1,alist2,alist3) =
    let first = extend_map MyMap.empty alist1 in
    let second = extend_map first alist2 in
    let third = extend_map first alist3 in
    (second,third)

  let nat_gen = QCheck.int

  let gen = QCheck.(triple
                      (small_list (pair nat_gen nat_gen))
                      (small_list (pair nat_gen nat_gen))
                      (small_list (pair nat_gen nat_gen)));;

  let model_from_gen x =
    let (m1,m2) = two_maps_from_three_lists x in
    (m1,intmap_of_mymap m1,m2,intmap_of_mymap m2)

  (* let dump_model m =
    Printf.printf "[";
    m |> IntMap.iter (fun key value -> Printf.printf "%d %d\n" key value);
    Printf.printf "]\n%!"

  let dump_test m1 m2 res expected =
    Printf.printf "=========\n";
    dump_model m1;
    dump_model m2;
    dump_model res;
    dump_model expected;
    Printf.printf "result is %b\n%!" (IntMap.equal (=) res expected) *)

  (** Fast hash function *)
  let sdbm x y = y + (x lsl 16) + (x lsl 6) - x
  let sdbm3 x y z = sdbm x @@ sdbm y z

  module Foreign = MyMap.WithForeign(MyMap.BaseMap)

  let test_pop_minimum = QCheck.Test.make ~count:1000 ~name:"pop_minimum"
      QCheck.(small_list (pair nat_gen nat_gen)) (fun x ->
          let m = extend_map MyMap.empty x in
          let model = intmap_of_mymap m in
          match MyMap.pop_minimum m, IntMap.pop_minimum model with
          | None, Some _ | Some _, None -> false
          | None, None -> true
          | Some(key1,val1,m'), Some(key2,val2,model') ->
            key1 = key2 && val1 = val2 && IntMap.equal (=) (intmap_of_mymap m') model')
  let () = QCheck.Test.check_exn test_pop_minimum

  let test_pop_maximum = QCheck.Test.make ~count:1000 ~name:"pop_maximum"
      QCheck.(small_list (pair nat_gen nat_gen)) (fun x ->
          let m = extend_map MyMap.empty x in
          let model = intmap_of_mymap m in
          match MyMap.pop_maximum m, IntMap.pop_maximum model with
          | None, Some _ | Some _, None -> false
          | None, None -> true
          | Some(key1,val1,m'), Some(key2,val2,model') ->
            key1 = key2 && val1 = val2 && IntMap.equal (=) (intmap_of_mymap m') model')
  let () = QCheck.Test.check_exn test_pop_maximum

  (** Create a function to check calls are made in increasing order *)
  let check_increases () =
    let seen = ref None in (* Store [to_int last_key]*)
    let f key =
      let key_int = HIntKey.to_int key in
      let () = match !seen with
        | None -> ()
        | Some old_key_int ->
          if unsigned_compare old_key_int key_int < 0
          then ()
          else QCheck.Test.fail_reportf
            "Non increasing calls to f : key %d seen after %d"
            key_int old_key_int
      in seen := Some key_int
    in f

  (** Create a function to check calls are made in increasing order and not on equal values *)
  let check_increases_and_neq () =
    let chk = check_increases () in
    let f key v1 v2 =
      chk key;
      if v1 == v2 then
        QCheck.Test.fail_reportf
          "Called on physically equal values %a and %a"
          IntValue.pretty v1 IntValue.pretty v2
    in f

 let test_map_filter = QCheck.Test.make ~count:1000 ~name:"map_filter"
      QCheck.(small_list (pair nat_gen nat_gen)) (fun x ->
          let m1 = extend_map MyMap.empty x in
          let model1 = intmap_of_mymap m1 in
          let chk_calls1 = check_increases () in
          let chk_calls2 = check_increases () in
          let f k x = if (x mod 3 == 0) then None else Some (x - k + 1) in
          let res1 = intmap_of_mymap @@ MyMap.filter_map (fun k v -> chk_calls1 k; f k v) m1 in
          let res2 = intmap_of_mymap @@ MyMap.filter_map_no_share (fun k v -> chk_calls2 k; f k v) m1 in
          let modelres = IntMap.filter_map f model1 in
          IntMap.equal (=) res1 modelres &&
          IntMap.equal (=) res2 modelres)
  let () = QCheck.Test.check_exn test_map_filter


  (* This way of generating the test has the benefits that it is easy to understand when a test fails. *)
  let test_reflexive_subset_domain_for_all2 = QCheck.Test.make ~count:1000 ~name:"reflexive_subset_domain_for_all2"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let f _key a b = a <= b in  (* This is reflexive. *)
          let myres = MyMap.reflexive_subset_domain_for_all2 f m1 m2 in
          let modelres = IntMap.subset_domain_for_all_2 model1 model2 f in
          myres = modelres)
  let () = QCheck.Test.check_exn test_reflexive_subset_domain_for_all2

  let test_reflexive_same_domain_for_all2 = QCheck.Test.make ~count:1000 ~name:"reflexive_same_domain_for_all2"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let f _key a b = a <= b in  (* This is reflexive. *)
          let myres = MyMap.reflexive_same_domain_for_all2 f m1 m2 in
          let modelres = IntMap.same_domain_for_all_2 model1 model2 f in
          myres = modelres)
  let () = QCheck.Test.check_exn test_reflexive_same_domain_for_all2

  let test_idempotent_union = QCheck.Test.make ~count:1000 ~name:"idempotent_union"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let f key (a:int) b = if key mod 2 == 0 then min a b else max a b in
          let chk_calls = check_increases_and_neq () in
          let myres = intmap_of_mymap @@ MyMap.idempotent_union
            (fun k a b -> chk_calls k a b; f k a b) m1 m2 in
          let modelres = IntMap.union (fun key a b -> Some (f key a b)) model1 model2 in
          (* dump_test model1 model2 myres modelres;           *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_idempotent_union;;


  let test_idempotent_inter = QCheck.Test.make ~count:1000 ~name:"idempotent_inter"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let f key (a:int) b = if key mod 2 == 0 then min a b else max a b in
          let chk_calls = check_increases_and_neq () in
          let myres = intmap_of_mymap @@ MyMap.idempotent_inter
            (fun k a b -> chk_calls k a b; f k a b) m1 m2 in
          let modelres = IntMap.inter model1 model2 f in
          (* dump_test model1 model2 myres modelres;           *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_idempotent_inter



  let test_nonidempotent_inter_no_share = QCheck.Test.make ~count:1000 ~name:"nonidempotent_inter_no_share"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let f key (a:int) b = sdbm3 key a b in
          let chk_calls = check_increases () in
          let myres = intmap_of_mymap @@ MyMap.nonidempotent_inter_no_share
            (fun k a b -> chk_calls k; f k a b) m1 m2 in
          let modelres = IntMap.inter model1 model2 f in
          (* dump_test model1 model2 myres modelres; *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_nonidempotent_inter_no_share


  let test_nonidempotent_inter_no_share_foreign = QCheck.Test.make ~count:1000 ~name:"nonidempotent_inter_no_share_foreign"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let orig_f = sdbm3 in
          let chk_calls = check_increases () in
          let f : int -> int -> int -> int = fun key (a:int) b -> chk_calls key; orig_f key a b in
          let myres = intmap_of_mymap @@ Foreign.nonidempotent_inter {f=fun k v (Snd v2) -> f k v v2 } m1 m2 in
          let modelres = IntMap.inter model1 model2 orig_f in
          (* dump_test model1 model2 myres modelres; *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_nonidempotent_inter_no_share_foreign


  let test_update_multiple_foreign = QCheck.Test.make ~count:1000 ~name:"update_multiple_foreign"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let orig_f key va vb =
            let res = match va with
              | None -> sdbm key vb
              | Some va -> sdbm3 key va vb
            in if res mod 2 == 0 then None else Some res
          in
          let chk_calls = check_increases () in
          let f = fun key a b -> chk_calls key; orig_f key a b in
          let myres = intmap_of_mymap @@ Foreign.update_multiple_from_foreign m2 {f=fun k v (Snd v') -> f k v v' } m1 in
          let modelres = IntMap.update_multiple_from_foreign model1 model2 orig_f in
          (* dump_test model1 model2 myres modelres; *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_update_multiple_foreign

  let test_update_multiple_inter_foreign = QCheck.Test.make ~count:1000 ~name:"update_multiple_inter_foreign"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let orig_f = fun key va vb ->
            let res = sdbm3 key va vb in
            if res mod 2 == 0 then None else Some res
          in
          let chk_calls = check_increases () in
          let f key (a:int) b = chk_calls key; orig_f key a b in
          let myres = intmap_of_mymap @@ Foreign.update_multiple_from_inter_with_foreign m2 {f=fun k v (Snd v') -> f k v v'} m1 in
          let modelres = IntMap.update_multiple_from_inter_with_foreign model1 model2 orig_f in
          (* dump_test model1 model2 myres modelres; *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_update_multiple_inter_foreign

  let test_idempotent_inter_filter = QCheck.Test.make ~count:1000 ~name:"idempotent_inter_filter"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          let f key (a:int) b =
            if a == b then Some a
            else let res =  sdbm3 key a b in
              if res mod 3 == 0 then None else Some res
          in
          let chk_calls = check_increases_and_neq () in
          let myres = intmap_of_mymap @@ MyMap.idempotent_inter_filter
            (fun k a b -> chk_calls k a b; f k a b) m1 m2 in
          let modelres = IntMap.inter_filter model1 model2 f in
          (* dump_test model1 model2 myres modelres;           *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_idempotent_inter_filter

  let test_slow_merge = QCheck.Test.make ~count:1000 ~name:"slow_merge"
      gen (fun x ->
          let (m1,model1,m2,model2) = model_from_gen x in
          (* A nonidempotent function that changes a lot according to inputs *)
          let f key a b = match a,b with
            | Some a, None -> if ((a * a) - key == 0) then None else Some((a * a) - key)
            | None, Some b -> if (key - b) == 0 then None else Some(key - b)
            | Some a, Some b -> if ((a - b - key) == 0) then None else Some(a-b-key)
            | None, None -> assert false
          in
          let myres = intmap_of_mymap @@ MyMap.slow_merge f m1 m2 in
          let modelres = IntMap.merge f model1 model2 in
          (* dump_test model1 model2 myres modelres; *)
          (* Printf.printf "res is %b\n%!" @@ IntMap.equal (=) modelres myres; *)
          IntMap.equal (=) modelres myres)
  let () = QCheck.Test.check_exn test_slow_merge

  let test_disjoint = QCheck.Test.make ~count:1000 ~name:"disjoint"
  gen (fun x ->
      let (m1,model1,m2,model2) = model_from_gen x in
      let myres = MyMap.disjoint m1 m2 in
      let modelres = IntMap.is_empty (IntMap.inter model1 model2 (fun _ a _ -> a)) in
      (* dump_test model1 model2 myres modelres; *)
      (* Printf.printf "res is %b\n%!" @@ IntMap.equal (=) modelres myres; *)
      modelres == myres)
  let () = QCheck.Test.check_exn test_disjoint

  let%test "negative_keys" =
    let map = MyMap.add 0 0 MyMap.empty in
    let _pp_l fmt = Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
      (fun fmt (k,l) -> Format.fprintf fmt "(%x, %x)" k l) fmt in
    let map2 = MyMap.add min_int 5 map in
    let map3 = MyMap.add max_int 8 map2 in
    let map4 = MyMap.add 25 8 map2 in
    let map5 = MyMap.idempotent_inter_filter (fun _ _ _ -> None) map3 map4 in
    (* Format.printf "[%a]@." pp_l (MyMap.to_list  map3);
    Format.printf "[%a]@." pp_l (MyMap.to_list  map4);
    Format.printf "[%a]@." pp_l (MyMap.to_list  map5);
    (match MyMap.BaseMap.view map3 with
      | Branch{prefix; branching_bit; _} -> Format.printf "%x : %x@." (Obj.magic prefix) (Obj.magic branching_bit)
      | _ -> ()
    ); *)
    MyMap.to_list map = [(0,0)] &&
    MyMap.to_list map2 = [(0,0); (min_int,5)] &&
    MyMap.to_list map3 = [(0,0); (max_int,8); (min_int,5)] &&
    MyMap.to_list map4 = [(0,0); (25,8); (min_int,5)] &&
    MyMap.to_list map5 = MyMap.to_list map2
end)


let%test_module "TestWeak" = (module struct

  module MyKey(* :KEY *) = struct
    type t = Block of int [@@ocaml.boxed]
    let to_int (Block x) = x
  end

  module NODE = WeakNode(struct type 'a t = MyKey.t end)(WrappedHomogeneousValue)
  module Map = MakeCustom(MyKey)(NODE)
  open Map

  let _m1 = singleton (MyKey.Block 7) "seven"
  let _m1 = add (MyKey.Block 9) "nine" _m1

  (* let dump_map m =
    Printf.printf "----\n%!";
    Map.iter (fun (Block key) value -> Printf.printf "key: %d value: %s\n%!" key value) m *)

  let length m =
    Map.fold (fun (MyKey.Block _key) _value acc -> acc + 1) m 0

  (* dump_map _m1;; *)

  let add n v m = add (MyKey.Block n) v m

  (* We have to make the test sufficiently complex, other as
     e.g. (Block 11) could be installed as a static value that would
     never get garbage-collected.  *)
  let test i =
    let n1,m2 =
      let m2 = (Sys.opaque_identity add) (11 + i) "eleven" _m1 in
      (* dump_map m2; *)
      length m2, m2
    in
    (* dump_map m2; *)
    Gc.full_major();
    let n2 = length m2 in
    (* Check that the key is removed. *)
    assert (n1 == 3);
    assert (n2 == 2);
    ()

  let () =
    for i = 0 to 10 do
      (* Printf.printf "==========="; *)
      test i
    done
end)
