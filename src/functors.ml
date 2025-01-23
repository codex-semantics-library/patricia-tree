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

open Ints
open Signatures
open Key_value
open Nodes

(** [match_prefix k p m] returns [true] if and only if the key [k] has prefix [p] up to bit [m]. *)
let match_prefix k p m = mask k m = p

(** Returns true if the branch caracterized by the two first arguments
    would contain the branch caracterized by the second (as right or left subtree) *)
let [@inline always] branches_before l_prefix (l_mask : mask) (r_prefix : intkey) (r_mask : mask) =
  unsigned_lt (r_mask :> int) (l_mask :> int) && match_prefix (r_prefix :> int) l_prefix l_mask


module MakeCustomHeterogeneousMap
    (Key:HETEROGENEOUS_KEY)
    (Value:HETEROGENEOUS_VALUE)
    (NODE:NODE with type 'a key = 'a Key.t and type ('key,'map) value = ('key,'map) Value.t) :
  HETEROGENEOUS_MAP with type 'a key = 'a Key.t
                       and type ('key,'map) value = ('key,'map) Value.t
                       and type 'a t = 'a NODE.t
= struct
  include NODE

  type 'map key_value_pair = KeyValue: 'a Key.t * ('a,'map) value -> 'map key_value_pair
  let rec unsigned_min_binding x = match NODE.view x with
    | Empty -> raise Not_found
    | Leaf{key;value} -> KeyValue(key,value)
    | Branch{tree0;_} -> unsigned_min_binding tree0
  let rec unsigned_max_binding x = match NODE.view x with
    | Empty -> raise Not_found
    | Leaf{key;value} -> KeyValue(key,value)
    | Branch{tree1;_} -> unsigned_max_binding tree1

  (* Merge trees whose prefix disagree. *)
  let join pa treea pb treeb =
    (* Printf.printf "join %d %d\n" pa pb; *)
    let m = branching_bit (pa :> int) (pb :> int) in
    let p = mask (pa :> int) (* for instance *) m in
    if ((pa :> int) land (m :> int)) = 0 then
      branch ~prefix:p ~branching_bit:m ~tree0:treea ~tree1:treeb
    else
      branch ~prefix:p ~branching_bit:m ~tree0:treeb ~tree1:treea

  let singleton = leaf

  let rec cardinal m =
    match NODE.view m with
    | Empty -> 0
    | Leaf _ -> 1
    | Branch{tree0; tree1; _ } -> cardinal tree0 + cardinal tree1

  let is_singleton m =
    match NODE.view m with
    | Leaf{key;value} -> Some (KeyValue(key,value))
    | _ -> None

  let rec findint: type a map. a Key.t -> int -> map t -> (a,map) value =
    fun witness searched m -> match NODE.view m with
      | Leaf{key;value} -> begin
          match Key.polyeq key witness with
          | Eq -> value
          | Diff -> raise Not_found
        end
      | Branch{branching_bit;tree0;tree1;_} ->
        (* Optional if not (match_prefix searched prefix branching_bit) then raise Not_found
           else *) if ((branching_bit :> int) land searched == 0)
        then findint witness searched tree0
        else findint witness searched tree1
      | Empty -> raise Not_found
  let find searched m = findint searched (Key.to_int searched) m

  let rec split: type a map. a key -> int -> map t -> map t * ((a,map) value) option * map t =
    fun split_key split_key_int m -> match NODE.view m with
      | Leaf{key;value} -> begin
          match Key.polyeq key split_key with
          | Eq -> NODE.empty, Some value, NODE.empty
          | Diff ->
            if unsigned_lt (Key.to_int key) split_key_int then
              m, None, NODE.empty else NODE.empty, None, m
        end
      | Branch{prefix;branching_bit;tree0;tree1} ->
          if not (match_prefix split_key_int prefix branching_bit) then
            if unsigned_lt (prefix :> int) split_key_int
            then m, None, NODE.empty
            else NODE.empty, None, m
          else if ((branching_bit :> int) land split_key_int == 0) then
            let left, found, right = split split_key split_key_int tree0 in
            left, found, NODE.branch ~prefix ~branching_bit ~tree0:right ~tree1
          else
            let left, found, right = split split_key split_key_int tree1 in
            NODE.branch ~prefix ~branching_bit ~tree0 ~tree1:left, found, right
      | Empty -> NODE.empty, None, NODE.empty

  let split k m = split k (Key.to_int k) m

  let find_opt searched m = match find searched m with
    | x -> Some x
    | exception Not_found -> None

  let mem searched m =
    match findint searched (Key.to_int searched) m with
    | exception Not_found -> false
    | _ -> true

  type ('map1,'map2) polymapi = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t } [@@unboxed]
  let rec mapi (f:('map1,'map1) polymapi) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} ->
      let newval = (f.f key value) in
      if newval == value
      then m
      else leaf key newval
    | Branch{prefix;branching_bit;tree0;tree1} ->
      let newtree0 = mapi f tree0 in
      let newtree1 = mapi f tree1 in
      if tree0 == newtree0 && tree1 == newtree1 then m
      else branch ~prefix ~branching_bit ~tree0:newtree0 ~tree1:newtree1


  (* MAYBE: A map (and map_filter) homogeneous, that try to preserve physical equality. *)
  let rec mapi_no_share (f:('map1,'map2) polymapi) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} -> leaf key (f.f key value)
    | Branch{prefix;branching_bit;tree0;tree1} ->
        let tree0 = mapi_no_share f tree0 in
        let tree1 = mapi_no_share f tree1 in
        branch ~prefix ~branching_bit ~tree0 ~tree1

  type ('map1,'map2) polymap = { f: 'a. ('a,'map1) Value.t -> ('a,'map2) Value.t } [@@unboxed]
  let map (f:('map1,'map1) polymap) m = mapi { f=fun _ v -> f.f v } m
  let map_no_share (f:('map1,'map2) polymap) m = mapi_no_share { f=fun _ v -> f.f v } m

  type ('map1,'map2) polyfilter_map = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t option } [@@unboxed]
  let rec filter_map (f:('map1,'map1) polyfilter_map) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} ->
      (match f.f key value with
       | None -> empty
       | Some newval -> if newval == value then m else leaf key newval)
    | Branch{prefix;branching_bit;tree0;tree1} ->
      let newtree0 = filter_map f tree0 in
      let newtree1 = filter_map f tree1 in
      if tree0 == newtree0 && tree1 == newtree1 then m
      else branch ~prefix ~branching_bit ~tree0:newtree0 ~tree1:newtree1

  let rec filter_map_no_share (f:('b,'c) polyfilter_map) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} -> (match (f.f key value) with Some v -> leaf key v | None -> empty)
    | Branch{prefix;branching_bit;tree0;tree1} ->
        let tree0 = filter_map_no_share f tree0 in
        let tree1 = filter_map_no_share f tree1 in
        branch ~prefix ~branching_bit ~tree0 ~tree1

  type 'map polypretty = { f: 'a. Format.formatter -> 'a Key.t -> ('a, 'map) Value.t -> unit } [@@unboxed]
  let rec pretty ?(pp_sep=Format.pp_print_cut) (f : 'map polypretty) fmt m =
    match NODE.view m with
    | Empty -> ()
    | Leaf{key;value} -> (f.f fmt key value)
    | Branch{tree0; tree1; _} ->
        pretty f ~pp_sep fmt tree0;
        pp_sep fmt ();
        pretty f ~pp_sep fmt tree1

  let rec removeint to_remove m = match NODE.view m with
    | Leaf{key;_} when (Key.to_int key) == to_remove -> empty
    | (Empty | Leaf _) -> m
    | Branch{prefix;branching_bit;tree0;tree1} ->
      if ((branching_bit :> int) land to_remove) == 0
      then begin
        let tree0' = removeint to_remove tree0 in
        if tree0' == empty then tree1
        else if tree0' == tree0 then m
        else branch ~prefix ~branching_bit ~tree0:tree0' ~tree1
      end
      else begin
        let tree1' = removeint to_remove tree1 in
        if tree1' == empty then tree0
        else if tree1' == tree1 then m
        else branch ~prefix ~branching_bit ~tree0 ~tree1:tree1'
      end

  let remove to_remove m = removeint (Key.to_int to_remove) m

  let rec pop_unsigned_minimum m = match NODE.view m with
    | Empty -> None
    | Leaf{key;value} -> Some (KeyValue(key,value),empty)
    | Branch{prefix;branching_bit;tree0;tree1} ->
      match pop_unsigned_minimum tree0 with
      | None -> pop_unsigned_minimum tree1
      | Some(res,tree0') ->
          let restree =
            if is_empty tree0' then tree1
            else branch ~prefix ~branching_bit ~tree0:tree0' ~tree1
          in Some(res,restree)

  let rec pop_unsigned_maximum m = match NODE.view m with
    | Empty -> None
    | Leaf{key;value} -> Some (KeyValue(key,value),empty)
    | Branch{prefix;branching_bit;tree0;tree1} ->
      match pop_unsigned_maximum tree1 with
      | None -> pop_unsigned_maximum tree0
      | Some(res,tree1') ->
          let restree =
            if is_empty tree1' then tree0
            else branch ~prefix ~branching_bit ~tree0 ~tree1:tree1'
          in Some(res,restree)

  let insert: type a map. a Key.t -> ((a,map) Value.t option -> (a,map) Value.t) -> map t -> map t =
    fun thekey f t ->
    let thekeyint = Key.to_int thekey in
    (* Preserve physical equality whenever possible. *)
    let exception Unmodified in
    try
      let rec loop t = match NODE.view t with
        | Empty -> leaf thekey (f None)
        | Leaf{key;value=old} ->
          begin match Key.polyeq key thekey with
            | Eq ->
              let newv = f (Some old) in
              if newv == old then raise Unmodified
              else leaf key newv
            | Diff ->
              let keyint = (Key.to_int key) in
              join thekeyint (leaf thekey (f None)) keyint t
          end
        | Branch{prefix;branching_bit;tree0;tree1} ->
          if match_prefix thekeyint prefix branching_bit then
            if ((branching_bit :> int) land thekeyint) == 0
            then branch ~prefix ~branching_bit ~tree0:(loop tree0) ~tree1
            else branch ~prefix ~branching_bit ~tree0 ~tree1:(loop tree1)
          else join thekeyint (leaf thekey (f None)) (prefix :> int) t
      in loop t
    with Unmodified -> t

  (* XXXX: This is a better update, that can also remove element, depending on how the join between the old and new values goes.
     Can be useful (e.g. when join is top), I should export that, maybe replace insert with it. *)
  (* TODO: Test. *)
  let update: type a map. a Key.t -> ((a,map) Value.t option -> (a,map) Value.t option) -> map t -> map t =
    fun thekey f t ->
    let thekeyint = Key.to_int thekey in
    (* Preserve physical equality whenever possible. *)
    let exception Unmodified in
    try
      let rec loop t = match NODE.view t with
        | Empty -> begin
            match (f None) with
            | None -> raise Unmodified
            | Some v -> leaf thekey v
          end
        | Leaf{key;value=old} ->
          begin match Key.polyeq key thekey with
            | Eq ->
              let newv = f (Some old) in
              begin match newv with
                | None -> empty
                | Some newv when newv == old -> raise Unmodified
                | Some newv -> leaf key newv end
            | Diff ->
              let keyint = (Key.to_int key) in
              begin match f None with
                | None -> raise Unmodified
                | Some value -> join thekeyint (leaf thekey value) keyint t
              end
          end
        | Branch{prefix;branching_bit;tree0;tree1} ->
          if match_prefix thekeyint prefix branching_bit then
            if (thekeyint land (branching_bit :> int)) == 0
            then branch ~prefix ~branching_bit ~tree0:(loop tree0) ~tree1
            else branch ~prefix ~branching_bit ~tree0 ~tree1:(loop tree1)
          else begin match f None with
            | None -> raise Unmodified
            | Some value -> join thekeyint (leaf thekey value) (prefix :> int) t
          end
      in loop t
    with Unmodified -> t

  (* Note: Insert is a bit weird, I am not sure it should be exported. *)
  type 'map polyinsert = { f: 'a . key:'a Key.t -> old:('a,'map) Value.t -> value:('a,'map) Value.t -> ('a,'map) Value.t } [@@unboxed]
  let insert_for_union: type a map. map polyinsert -> a Key.t -> (a,map) Value.t -> map t -> map t =
    fun f thekey value t ->
    let thekeyint = Key.to_int thekey in
    (* Preserve physical equality whenever possible. *)
    let exception Unmodified in
    try
      let rec loop t = match NODE.view t with
        | Empty -> leaf thekey value
        | Leaf{key;value=old} ->
          begin match Key.polyeq key thekey with
            | Eq ->
              if value == old then raise Unmodified else
              let newv = f.f ~key ~old ~value in
              if newv == old then raise Unmodified
              else leaf key newv
            | Diff ->
              let keyint = (Key.to_int key) in
              join thekeyint (leaf thekey value) keyint t
          end
        | Branch{prefix;branching_bit;tree0;tree1} ->
          if match_prefix thekeyint prefix branching_bit then
            if (thekeyint land (branching_bit :> int)) == 0
            then branch ~prefix ~branching_bit ~tree0:(loop tree0) ~tree1
            else branch ~prefix ~branching_bit ~tree0 ~tree1:(loop tree1)
          else join thekeyint (leaf thekey value) (prefix :> int) t
      in loop t
    with Unmodified -> t

  let add key value t = insert key (fun _ -> value) t

  type ('map1,'map2) polysame_domain_for_all2 = { f: 'a 'b. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> bool } [@@unboxed]
  (* Fast equality test between two maps. *)
  let rec reflexive_same_domain_for_all2 f ta tb = match (NODE.view ta),(NODE.view tb) with
    | _ when ta == tb -> true (* Skip same subtrees thanks to reflexivity. *)
    | Empty, _ | _, Empty -> false
    | Leaf _, Branch _ | Branch _, Leaf _ -> false
    | Leaf{key=keya;value=valuea}, Leaf{key=keyb;value=valueb} ->
      begin match Key.polyeq keya keyb with
        | Diff -> false
        | Eq -> f.f keya valuea valueb
      end
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      pa == pb && ma == mb &&
      reflexive_same_domain_for_all2 f ta0 tb0 &&
      reflexive_same_domain_for_all2 f ta1 tb1

  let rec nonreflexive_same_domain_for_all2 f ta tb = match (NODE.view ta),(NODE.view tb) with
    | Empty, _ | _, Empty -> false
    | Leaf _, Branch _ | Branch _, Leaf _ -> false
    | Leaf{key=keya;value=valuea}, Leaf{key=keyb;value=valueb} ->
      begin match Key.polyeq keya keyb with
        | Diff -> false
        | Eq -> f.f keya valuea valueb
      end
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      pa == pb && ma == mb &&
      nonreflexive_same_domain_for_all2 f ta0 tb0 &&
      nonreflexive_same_domain_for_all2 f ta1 tb1

  let rec reflexive_subset_domain_for_all2 f ta tb = match (NODE.view ta),(NODE.view tb) with
    | _ when ta == tb -> true   (* Skip same subtrees thanks to reflexivity. *)
    | Empty, _ -> true
    | _, Empty -> false
    | Branch _, Leaf _ -> false
    | Leaf {key=keya;value=valuea}, viewb ->
      (* Reimplement find locally, mostly because of typing issues
         (which could be solved if we had a version of find that
         returns a (key,value) pair. *)
      let searched = Key.to_int keya in
      let rec search = function
        | Leaf{key=keyb;value=valueb} ->
          begin match Key.polyeq keya keyb with
            | Diff -> false
            | Eq -> f.f keya valuea valueb
          end
        | Branch{branching_bit;tree0;tree1;_} ->
          if ((branching_bit :> int) land searched == 0)
          then search (NODE.view tree0)
          else search (NODE.view tree1)
        | Empty -> false (* Can only happen on weak nodes. *)
      in search viewb
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: divide the search. *)
      then
        (reflexive_subset_domain_for_all2 f ta0 tb0) &&
        (reflexive_subset_domain_for_all2 f ta1 tb1)
        (* Case where ta have to be included in one of tb0 or tb1. *)
      else if branches_before pb mb pa ma
      then if (mb :> int) land (pa :> int) == 0
        then reflexive_subset_domain_for_all2 f ta tb0
        else reflexive_subset_domain_for_all2 f ta tb1
        (* Any other case: there are elements in ta that are unmatched in tb. *)
      else false

  type 'map polycompare =
      { f : 'a. 'a key -> ('a, 'map) value -> ('a, 'map) value -> int; } [@@unboxed]

  let compare_aux : type a b m. m polycompare -> a key -> (a,m) value -> b key -> (b,m) value -> int -> int =
  fun f ka va kb vb default ->
    let cmp = Int.compare (Key.to_int ka) (Key.to_int kb) in
    if cmp <> 0 then cmp else
    match Key.polyeq ka kb with
      | Eq -> let cmp = f.f ka va vb in
              if cmp <> 0 then cmp else default
      | Diff -> default (* Should not happen since same Key.to_int values should imply equality *)

  let rec reflexive_compare f ta tb = match (NODE.view ta),(NODE.view tb) with
    | _ when ta == tb -> 0
    | Empty, _ -> 1
    | _, Empty -> -1
    | Branch _, Leaf {key;value} ->
        let KeyValue(k,v) = unsigned_min_binding ta in
        compare_aux f k v key value 1
    | Leaf {key;value}, Branch _ ->
        let KeyValue(k,v) = unsigned_min_binding tb in
        compare_aux f key value k v (-1)
    | Leaf {key;value}, Leaf{key=keyb;value=valueb} ->
        compare_aux f key value keyb valueb 0
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: divide the search. *)
      then
        let cmp = reflexive_compare f ta0 tb0 in
        if cmp <> 0 then cmp else
          reflexive_compare f ta1 tb1
      else if branches_before pb mb pa ma (* ta has to be included in  tb0 or tb1. *)
      then if (mb :> int) land (pa :> int) == 0
        then let cmp = reflexive_compare f ta tb0 in if cmp <> 0 then cmp else -1
        else -1 (* ta included in tb1, so there are elements of tb that appear before any elements of ta *)
      else if branches_before pa ma pb mb (* tb has to be included in ta0 or ta1. *)
        then if (mb :> int) land (pa :> int) == 0
          then let cmp = reflexive_compare f ta0 tb in if cmp <> 0 then cmp else 1
          else 1 (* tb included in ta1, so there are elements of ta that appear before any elements of tb *)
      else Int.compare (pa :> int) (pb :> int)

  let rec disjoint ta tb =
    if ta == tb then is_empty ta
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> true
      | Leaf{key;_},_ -> not (mem key tb)
      | _,Leaf{key;_} -> not (mem key ta)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: check both subtrees *)
        then disjoint ta0 tb0 && disjoint ta1 tb1
        else if branches_before pa ma pb mb (* tb included in ta0 or ta1 *)
        then if (ma :> int) land (pb :> int) == 0
          then disjoint ta0 tb
          else disjoint ta1 tb
        else if branches_before pb mb pa ma (* ta included in tb0 or tb1 *)
        then if (mb :> int) land (pa :> int) == 0
          then disjoint ta tb0
          else disjoint ta tb1
        else true (* Different prefixes => no intersection *)

  type ('map1,'map2,'map3) polyunion = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> ('a,'map3) Value.t } [@@unboxed]
  let rec idempotent_union f ta tb =
    if ta == tb then ta
    else
      match NODE.view ta,NODE.view tb with
      | Empty, _ -> tb
      | _, Empty -> ta
      | Leaf{key;value},_ -> insert_for_union ({f=fun ~key ~old ~value -> f.f key value old}) key value tb
      | _,Leaf{key;value} -> insert_for_union ({f=fun ~key ~old ~value -> f.f key old value}) key value ta
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          (* MAYBE: if ta0 == tb0 and ta1 == tb1, we can return ta (or
             tb). Probably not useful. *)
          let tree0 = idempotent_union f ta0 tb0 in
          let tree1 = idempotent_union f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then branch ~prefix:pa ~branching_bit:ma ~tree0:(idempotent_union f ta0 tb) ~tree1:ta1
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:(idempotent_union f ta1 tb)
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then branch ~prefix:pb ~branching_bit:mb ~tree0:(idempotent_union f ta tb0) ~tree1:tb1
          else branch ~prefix:pb ~branching_bit:mb ~tree0:tb0 ~tree1:(idempotent_union f ta tb1)
        else join (pa :> int) ta (pb :> int) tb

  type ('map1,'map2,'map3) polyinter = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> ('a,'map3) Value.t } [@@unboxed]
  let rec idempotent_inter f ta tb =
    if ta == tb then ta
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> empty
      | Leaf{key;value},_ ->
        (try let res = find key tb in
            if res == value then ta else
            let newval = f.f key value res in
            if newval == value then ta else
            leaf key newval
         with Not_found -> empty)
      | _,Leaf{key;value} ->
        (try let res = find key ta in
            if res == value then tb else
            let newval = f.f key res value in
            if newval == value then tb else
            leaf key newval
         with Not_found -> empty)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = idempotent_inter f ta0 tb0 in
          let tree1 = idempotent_inter f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then idempotent_inter f ta0 tb
          else idempotent_inter f ta1 tb
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then idempotent_inter f ta tb0
          else idempotent_inter f ta tb1
        else empty

  (* Same as above, without the same subtree optimisation. *)
  let rec nonidempotent_inter_no_share f ta tb =
    match NODE.view ta,NODE.view tb with
    | Empty, _ | _, Empty -> empty
    | Leaf{key;value},_ ->
      (try let res = find key tb in
         leaf key (f.f key value res)
       with Not_found -> empty)
    | _,Leaf{key;value} ->
      (try let res = find key ta in
         leaf key (f.f key res value)
       with Not_found -> empty)
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: merge the subtrees *)
      then
        let tree0 = nonidempotent_inter_no_share f ta0 tb0 in
        let tree1 = nonidempotent_inter_no_share f ta1 tb1 in
        branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
      else if branches_before pa ma pb mb
      then if (ma :> int) land (pb :> int) == 0
        then nonidempotent_inter_no_share f ta0 tb
        else nonidempotent_inter_no_share f ta1 tb
      else if branches_before pb mb pa ma
      then if (mb :> int) land (pa :> int) == 0
        then nonidempotent_inter_no_share f ta tb0
        else nonidempotent_inter_no_share f ta tb1
      else empty

  type ('map1,'map2,'map3) polyinterfilter = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> ('a,'map3) Value.t option } [@@unboxed]
  let rec idempotent_inter_filter f ta tb =
    if ta == tb then ta
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> empty
      | Leaf{key;value},_ ->
        (try let res = find key tb in
           if res == value then ta else
           match (f.f key value res) with
           | Some v when v == value -> ta
           | Some v -> leaf key v
           | None -> empty
         with Not_found -> empty)
      | _,Leaf{key;value} ->
        (try let res = find key ta in
           if res == value then tb else
           match f.f key res value with
           | Some v when v == value -> tb
           | Some v -> leaf key v
           | None -> empty
         with Not_found -> empty)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = idempotent_inter_filter f ta0 tb0 in
          let tree1 = idempotent_inter_filter f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then idempotent_inter_filter f ta0 tb
          else idempotent_inter_filter f ta1 tb
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then idempotent_inter_filter f ta tb0
          else idempotent_inter_filter f ta tb1
        else empty

  type ('map1,'map2,'map3) polymerge = { f: 'a. 'a Key.t -> ('a,'map1) Value.t option -> ('a,'map2) Value.t option -> ('a,'map3) Value.t option } [@@unboxed]
  let rec slow_merge: type mapa mapb mapc. (mapa,mapb,mapc) polymerge -> mapa NODE.t -> mapb NODE.t -> mapc NODE. t=
    fun f ta tb ->
    let upd_ta ta = filter_map_no_share {f=fun key value -> f.f key (Some value) None} ta in
    let upd_tb tb = filter_map_no_share {f=fun key value -> f.f key None (Some value)} tb in
    let oldf = f in
    match NODE.view ta,NODE.view tb with
    | Empty, _ -> upd_tb tb
    | _, Empty -> upd_ta ta
    | Leaf{key;value},_ ->
      let found = ref false in
      let f: type a. a Key.t -> (a,mapb) Value.t -> (a,mapc) Value.t option = fun curkey curvalue ->
        match Key.polyeq curkey key with
        | Eq -> found:= true; f.f key (Some value) (Some curvalue)
        | Diff -> f.f curkey None (Some curvalue) in
      let res = filter_map_no_share {f} tb in
      (* If the key of the leaf is not present, add it back.  Note
         that it breaks the assumption that merge is done in ascending
         number of keys; if we wanted that, we would need a
         "filter_map_no_share_add_key" function.  *)
      if !found then res
      else begin
        match oldf.f key (Some value) None with
        | None -> res
        | Some value -> add key value res
      end
    | _, Leaf{key;value} ->
      let found = ref false in
      let f: type a. a Key.t -> (a,mapa) Value.t -> (a,mapc) Value.t option = fun curkey curvalue ->
        match Key.polyeq curkey key with
        | Eq -> found := true; f.f key (Some curvalue) (Some value)
        | Diff -> f.f curkey (Some curvalue) None in
      let res = filter_map_no_share {f} ta in
      if !found then res
      else begin
        match oldf.f key None (Some value) with
        | None -> res
        | Some value -> add key value res
      end
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: merge the subtrees *)
      then
        branch ~prefix:pa ~branching_bit:ma ~tree0:(slow_merge f ta0 tb0) ~tree1:(slow_merge f ta1 tb1)
      else if branches_before pa ma pb mb
      then if (ma :> int) land (pb :> int) == 0
        then branch ~prefix:pa ~branching_bit:ma ~tree0:(slow_merge f ta0 tb) ~tree1:(upd_ta ta1)
        else branch ~prefix:pa ~branching_bit:ma ~tree0:(upd_ta ta0) ~tree1:(slow_merge f ta1 tb)
      else if branches_before pb mb pa ma
      then if (mb :> int) land (pa :> int) == 0
        then branch ~prefix:pb ~branching_bit:mb ~tree0:(slow_merge f ta tb0) ~tree1:(upd_tb tb1)
        else branch ~prefix:pb ~branching_bit:mb ~tree0:(upd_tb tb0) ~tree1:(slow_merge f ta tb1)
      else join (pa :> int) (upd_ta ta) (pb :> int) (upd_tb tb)

  type ('a, 'b) polydifference = ('a, 'b, 'a) polyinterfilter
  let rec symmetric_difference (f : (_,_) polydifference) ta tb =
    if ta == tb then empty
    else match NODE.view ta, NODE.view tb with
      | Empty, _ -> tb
      | _, Empty -> ta
      | Leaf{key;value},_ ->
        (try let res = find key tb in
            if res == value then remove key tb else
            match (f.f key value res) with
            | Some v when v == res -> tb
            | Some v -> add key v tb
            | None -> remove key tb
          with Not_found -> add key value tb)
      | _,Leaf{key;value} ->
        (try let res = find key ta in
            if res == value then remove key ta else
            match f.f key res value with
            | Some v when v == res -> ta
            | Some v -> add key v ta
            | None -> remove key ta
          with Not_found -> add key value ta)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = symmetric_difference f ta0 tb0 in
          let tree1 = symmetric_difference f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then branch ~prefix:pa ~branching_bit:ma ~tree0:(symmetric_difference f ta0 tb) ~tree1:ta1
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:(symmetric_difference f ta1 tb)
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then branch ~prefix:pb ~branching_bit:mb ~tree0:(symmetric_difference f ta tb0) ~tree1:tb1
          else branch ~prefix:pb ~branching_bit:mb ~tree0:tb0 ~tree1:(symmetric_difference f ta tb1)
        else join (pa :> int) ta (pb :> int) tb

  let rec difference (f: (_,_) polydifference) ta tb =
    if ta == tb then empty else
    match NODE.view ta, NODE.view tb with
    | Empty, _ | _, Empty -> ta
    | Leaf{key;value=va},_ -> (try let vb = find key tb in
          if va == vb then empty else
          match f.f key va vb with
          | None -> empty
          | Some v -> if v == va then ta else leaf key v
        with Not_found -> ta)
    | _,Leaf{key;value} -> update key (function
        | None -> None
        | Some v when v == value -> None
        | Some v -> f.f key v value) ta
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb then
        let tree0 = difference f ta0 tb0 in
        let tree1 = difference f ta1 tb1 in
        branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
      else if branches_before pa ma pb mb
      then if (ma :> int) land (pb :> int) == 0
        then branch ~prefix:pa ~branching_bit:ma ~tree0:(difference f ta0 tb) ~tree1:ta1
        else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:(difference f ta1 tb)
      else if branches_before pb mb pa ma
      then if (mb :> int) land (pa :> int) == 0
        then difference f ta tb0
        else difference f ta tb1
      else ta

  type 'map polyiter = { f: 'a. 'a Key.t -> ('a,'map) Value.t -> unit } [@@unboxed]
  let rec iter f x = match NODE.view x with
    | Empty -> ()
    | Leaf{key;value} -> f.f key value
    | Branch{tree0;tree1;_} -> iter f tree0; iter f tree1

  type ('acc,'map) polyfold = { f: 'a. 'a Key.t -> ('a,'map) Value.t -> 'acc -> 'acc } [@@unboxed]
  let rec fold f m acc = match NODE.view m with
    | Empty -> acc
    | Leaf{key;value} -> f.f key value acc
    | Branch{tree0;tree1;_} ->
      let acc = fold f tree0 acc in
      fold f tree1 acc


  type ('acc,'map) polyfold2 = { f: 'a. 'a key -> ('a,'map) value -> ('a,'map) value -> 'acc -> 'acc } [@@unboxed]
  let rec fold_on_nonequal_inter f ta tb acc =
    if ta == tb then acc
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> acc
      | Leaf{key;value},_ ->
        (try let valueb = find key tb in
           if valueb == value then acc else
             f.f key value valueb acc
         with Not_found -> acc)
      | _,Leaf{key;value} ->
        (try let valuea = find key ta in
           if valuea == value then acc else
             f.f key valuea value acc
         with Not_found -> acc)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: fold on each subtrees *)
        then
          let acc = fold_on_nonequal_inter f ta0 tb0 acc in
          let acc = fold_on_nonequal_inter f ta1 tb1 acc in
          acc
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then fold_on_nonequal_inter f ta0 tb acc
          else fold_on_nonequal_inter f ta1 tb acc
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then fold_on_nonequal_inter f ta tb0 acc
          else fold_on_nonequal_inter f ta tb1 acc
        else acc


  type ('acc,'map) polyfold2_union =
    { f: 'a. 'a key -> ('a,'map) value option -> ('a,'map) value option ->
        'acc -> 'acc } [@@unboxed]
  let rec fold_on_nonequal_union:
    'm 'acc. ('acc,'m) polyfold2_union -> 'm t -> 'm t -> 'acc -> 'acc =
    fun (type m) f (ta:m t) (tb:m t) acc ->
    if ta == tb then acc
    else
      let fleft:(_,_) polyfold =
        {f=fun key value acc -> f.f key (Some value) None acc} in
      let fright:(_,_)polyfold =
        {f=fun key value acc -> f.f key None (Some value) acc} in
      match NODE.view ta,NODE.view tb with
      | Empty, _ -> fold fright tb acc
      | _, Empty -> fold fleft ta acc
      | Leaf{key;value},_ ->
        let ida = Key.to_int key in
        (* Fold on the rest, knowing that ida may or may not be in b. So we fold and use
           did_a to remember if we already did the call to a. *)
        let g (type b) (keyb:b key) (valueb:(b,m) value) (acc,did_a) =
          let default() = (f.f keyb None (Some valueb) acc,did_a) in
          if did_a then default()
          else
            let idb = Key.to_int keyb in
            if unsigned_lt idb ida then default()
            else if unsigned_lt ida idb then
              let acc = f.f key (Some value) None acc in
              let acc = f.f keyb None (Some valueb) acc in
              (acc,true)
            else match Key.polyeq key keyb with
              | Eq ->
                if value == valueb then (acc,true)
                else (f.f key (Some value) (Some valueb) acc,true)
              | Diff ->
                raise (Invalid_argument "Keys with same to_int value are not equal by polyeq")
        in
        let (acc,found) = fold{f=fun keyb valueb acc -> g keyb valueb acc} tb (acc,false) in
        if found then acc
        else f.f key (Some value) None acc
      | _,Leaf{key;value} ->
        let idb = Key.to_int key in
        let g (type a) (keya: a key) (valuea:(a,m) value) (acc,did_b) =
          let default() = (f.f keya (Some valuea) None acc,did_b) in
          if did_b then default()
          else
            let ida = Key.to_int keya in
            if unsigned_lt ida idb then default()
            else if unsigned_lt idb ida then
              let acc = f.f key None (Some value) acc in
              let acc = f.f keya (Some valuea) None acc in
              (acc,true)
            else match Key.polyeq keya key with
              | Eq ->
                if valuea == value then (acc,true)
                else (f.f keya (Some valuea) (Some value) acc,true)
              | Diff ->
                raise (Invalid_argument "Keys with same to_int value are not equal by polyeq")
        in
        let (acc,found) = fold{f=fun keya valuea acc -> g keya valuea acc} ta (acc,false) in
        if found then acc
        else f.f key None (Some value) acc
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let acc = fold_on_nonequal_union f ta0 tb0 acc in
          let acc = fold_on_nonequal_union f ta1 tb1 acc in
          acc
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then
            let acc = fold_on_nonequal_union f ta0 tb acc in
            let acc = fold fleft ta1 acc in
            acc
          else
            let acc = fold fleft ta0 acc in
            let acc = fold_on_nonequal_union f ta1 tb acc in
            acc
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then
            let acc = fold_on_nonequal_union f ta tb0 acc in
            let acc = fold fright tb1 acc in
            acc
          else
            let acc = fold fright tb0 acc in
            let acc = fold_on_nonequal_union f ta tb1 acc in
            acc
        else
        (* Distinct subtrees: process them in increasing order of keys. *)
        if unsigned_lt (pa :> int) (pb :> int) then
          let acc = fold fleft ta acc in
          let acc = fold fright tb acc in
          acc
        else
          let acc = fold fright tb acc in
          let acc = fold fleft ta acc in
          acc

  type 'map polypredicate = { f: 'a. 'a key -> ('a,'map) value -> bool; } [@@unboxed]
  let filter f m = filter_map {f = fun k v -> if f.f k v then Some v else None } m
  let rec for_all f m = match NODE.view m with
    | Empty -> true
    | Leaf{key;value} -> f.f key value
    | Branch{tree0; tree1; _ } -> for_all f tree0 && for_all f tree1

  module WithForeign(Map2:BASE_MAP with type 'a key = 'a key) = struct

    (* Intersects the first map with the values of the second map,
       trying to preserve physical equality of the first map whenever
       possible. *)
    type ('map1,'map2) polyinter_foreign = { f: 'a. 'a key -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value } [@@unboxed]
    let rec nonidempotent_inter f ta tb =
      match NODE.view ta,Map2.view tb with
      | Empty, _ | _, Empty -> NODE.empty
      | Leaf{key;value},_ ->
        (try let res = Map2.find key tb in
           let newval = (f.f key value res) in
           if newval == value then ta
           else NODE.leaf key newval
         with Not_found -> NODE.empty)
      | _,Leaf{key;value} ->
        (try let res = find key ta in
           NODE.leaf key (f.f key res value)
         with Not_found -> NODE.empty)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = (nonidempotent_inter f ta0 tb0) in
          let tree1 = (nonidempotent_inter f ta1 tb1) in
          if(ta0 == tree0 && ta1 == tree1)
          then ta
          else NODE.branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then nonidempotent_inter f ta0 tb
          else nonidempotent_inter f ta1 tb
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then nonidempotent_inter f ta tb0
          else nonidempotent_inter f ta tb1
        else NODE.empty

    type ('map2,'map1) polyfilter_map_foreign = { f: 'a. 'a Key.t -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
    let rec filter_map_no_share (f:('b,'c) polyfilter_map_foreign) m = match Map2.view m with
      | Empty -> empty
      | Leaf{key;value} -> (match (f.f key value) with Some v -> leaf key v | None -> empty)
      | Branch{prefix;branching_bit;tree0;tree1} ->
          let tree0 = filter_map_no_share f tree0 in
          let tree1 = filter_map_no_share f tree1 in
          branch ~prefix ~branching_bit ~tree0 ~tree1

    (** Add all the bindings in tb to ta (after transformation).  *)
    type ('map1,'map2) polyupdate_multiple = { f: 'a. 'a Key.t -> ('a,'map1) value option -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
    let rec update_multiple_from_foreign (tb:'map2 Map2.t) f (ta:'map1 t) =
      let upd_tb tb = filter_map_no_share {f=fun key value -> f.f key None value} tb in
      match NODE.view ta,Map2.view tb with
      | Empty, _ -> upd_tb tb
      | _, Empty -> ta
      | _,Leaf{key;value} -> update key (fun maybeval -> f.f key maybeval value) ta
      | Leaf{key;value},_ ->
        let found = ref false in
        let f: type a. a key -> (a,'map2) Map2.value -> (a,'map1) value option =
          fun curkey curvalue ->
            match Key.polyeq key curkey with
            | Eq -> found := true; f.f curkey (Some value) curvalue
            | Diff -> f.f curkey None curvalue
        in
        let res = filter_map_no_share {f} tb in
        if !found then res
        else add key value res
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = update_multiple_from_foreign tb0 f ta0 in
          let tree1 = update_multiple_from_foreign tb1 f ta1 in
          if tree0 == ta0 && tree1 == ta1 then ta
          else branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then
            let ta0' = update_multiple_from_foreign tb f ta0 in
            if ta0' == ta0 then ta
            else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0' ~tree1:ta1
          else
            let ta1' = update_multiple_from_foreign tb f ta1 in
            if ta1' == ta1 then ta
            else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:ta1'
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then
            let tree0 = update_multiple_from_foreign tb0 f ta in
            let tree1 = upd_tb tb1 in
            branch ~prefix:pb ~branching_bit:mb ~tree0 ~tree1
          else
            let tree0 = upd_tb tb0 in
            let tree1 = update_multiple_from_foreign tb1 f ta in
            branch ~prefix:pb ~branching_bit:mb ~tree0 ~tree1
        else join (pa :> int) ta (pb :> int) (upd_tb tb)


    (* Map difference: (possibly) remove from ta elements that are in tb, the other are preserved, no element is added. *)
    type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. 'a Key.t -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
    let rec update_multiple_from_inter_with_foreign tb f ta =
      match NODE.view ta, Map2.view tb with
      | Empty, _ -> ta
      | _, Empty -> ta
      | Leaf{key;value},_ ->
        begin match Map2.find key tb with
        | exception Not_found -> ta
        | foundv -> begin
            match f.f key value foundv with
            | None -> empty
            | Some v when v == value -> ta
            | Some v -> leaf key v
          end
        end
      | _,Leaf{key;value} ->
        update key (fun v -> match v with None -> None | Some v -> f.f key v value) ta
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = update_multiple_from_inter_with_foreign tb0 f ta0 in
          let tree1 = update_multiple_from_inter_with_foreign tb1 f ta1 in
          if tree0 == ta0 && tree1 == ta1 then ta
          else branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then
            let ta0' = update_multiple_from_inter_with_foreign tb f ta0 in
            if ta0' == ta0 then ta
            else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0' ~tree1:ta1
          else
            let ta1' = update_multiple_from_inter_with_foreign tb f ta1 in
            if ta1' == ta1 then ta
            else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:ta1'
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then update_multiple_from_inter_with_foreign tb0 f ta
          else update_multiple_from_inter_with_foreign tb1 f ta
        else ta

    type ('map1, 'map2) polydifference = ('map1,'map2) polyupdate_multiple_inter
    let rec difference f ta tb =
      match NODE.view ta, Map2.view tb with
      | Empty, _
      | _, Empty -> ta
      | Leaf{key;value=va},_ -> (try let vb = Map2.find key tb in
            match f.f key va vb with
            | None -> empty
            | Some v -> if v == va then ta else leaf key v
          with Not_found -> ta)
      | _,Leaf{key;value} -> update key (function None -> None | Some v -> f.f key v value) ta
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        then
          let tree0 = difference f ta0 tb0 in
          let tree1 = difference f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if branches_before pa ma pb mb
        then if (ma :> int) land (pb :> int) == 0
          then branch ~prefix:pa ~branching_bit:ma ~tree0:(difference f ta0 tb) ~tree1:ta1
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:(difference f ta1 tb)
        else if branches_before pb mb pa ma
        then if (mb :> int) land (pa :> int) == 0
          then difference f ta tb0
          else difference f ta tb1
        else ta
  end

  let rec to_seq m () = match NODE.view m with
    | Empty -> Seq.Nil
    | Leaf{key; value} -> Seq.Cons (KeyValue(key,value), Seq.empty)
    | Branch{tree0; tree1; _} -> Seq.append (to_seq tree0) (to_seq tree1) ()

  let rec to_rev_seq m () = match NODE.view m with
    | Empty -> Seq.Nil
    | Leaf{key; value} -> Seq.Cons (KeyValue(key,value), Seq.empty)
    | Branch{tree0; tree1; _} -> Seq.append (to_rev_seq tree1) (to_rev_seq tree0) ()

  let rec add_seq: type a. a key_value_pair Seq.t -> a t -> a t =
    fun s m -> match s () with
    | Seq.Nil -> m
    | Seq.Cons(KeyValue(key,value), s) -> add_seq s (add key value m)

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list m = List.of_seq (to_seq m)
end

module MakeCustomHeterogeneousSet
    (Key:HETEROGENEOUS_KEY)
    (Node:NODE with type 'a key = 'a Key.t and type ('a, 'b) value = unit)
: HETEROGENEOUS_SET with type 'a elt = 'a Key.t and type 'a BaseMap.t = 'a Node.t = struct
  module BaseMap = MakeCustomHeterogeneousMap(Key)(struct type ('a,'b) t = unit end)(Node)

  (* No need to differentiate the values. *)
  include BaseMap

  type t = unit BaseMap.t
  type 'a elt = 'a key

  type any_elt = Any : 'a elt -> any_elt

  (* Note: as add is simpler, without any insertion function needed,
     maybe it is worth reimplementing it. *)
  let [@specialise] add key map = BaseMap.add key () map
  let singleton elt = singleton elt ()
  let is_singleton set = match BaseMap.is_singleton set with
    | None -> None
    | Some(KeyValue(k,())) -> Some(Any(k))

  (* Likewise with union and inter: we do not have to worry about
     reconciling the values here, so we could reimplement if the
     compiler is not smart enough. *)
  let  union =
    let f:(unit,unit,unit) BaseMap.polyunion = {f=fun _ () () -> ()} in
    fun [@specialise] sa sb -> BaseMap.idempotent_union f sa sb

  let inter =
    let f:(unit,unit,unit) BaseMap.polyinter = {f=fun _ () () -> ()} in
    fun [@specialise] sa sb -> (BaseMap.idempotent_inter (* [@specialised] *)) f sa sb

  type polyiter = { f: 'a. 'a elt -> unit; } [@@unboxed]
  let iter f set = BaseMap.iter {f=fun k () -> f.f k} set

  (* TODO: A real implementation of fold would be faster. *)
  type 'acc polyfold = { f: 'a. 'a key -> 'acc -> 'acc } [@@unboxed]
  let fold f set acc =
    let f: type a. a key -> unit -> 'acc -> 'acc = fun k () acc -> f.f k acc in
    BaseMap.fold { f } set acc

  let unsigned_min_elt t = let KeyValue(m, ()) = BaseMap.unsigned_min_binding t in Any m
  let unsigned_max_elt t = let KeyValue(m, ()) = BaseMap.unsigned_max_binding t in Any m

  let pop_unsigned_maximum t = Option.map (fun (KeyValue(m,()),t) -> Any m,t) (BaseMap.pop_unsigned_maximum t)
  let pop_unsigned_minimum t = Option.map (fun (KeyValue(m,()),t) -> Any m,t) (BaseMap.pop_unsigned_minimum t)

  type polypretty = { f: 'a. Format.formatter -> 'a key -> unit; } [@@unboxed]
  let pretty ?pp_sep f fmt s = BaseMap.pretty ?pp_sep { f = fun fmt k () -> f.f fmt k} fmt s

  let equal t1 t2 = BaseMap.reflexive_same_domain_for_all2 {f=fun _ _ _ -> true} t1 t2
  let subset t1 t2 = BaseMap.reflexive_subset_domain_for_all2 {f=fun _ _ _ -> true} t1 t2
  let diff = BaseMap.difference { f = fun _ () () -> None }

  let split k m = let (l, present, r) = BaseMap.split k m in
    (l, Option.is_some present, r)

  type polypredicate = { f: 'a. 'a key -> bool; } [@@unboxed]
  let filter f s = BaseMap.filter {f = fun k () -> f.f k } s
  let for_all f s = BaseMap.for_all {f = fun k () -> f.f k} s

  let to_seq m = Seq.map (fun (KeyValue(elt,())) -> Any elt) (BaseMap.to_seq m)
  let to_rev_seq m = Seq.map (fun (KeyValue(elt,())) -> Any elt) (BaseMap.to_rev_seq m)
  let add_seq s m = BaseMap.add_seq (Seq.map (fun (Any elt) -> KeyValue(elt,())) s) m

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list s = List.of_seq (to_seq s)

  let compare s1 s2 = BaseMap.reflexive_compare {f=fun _ () () -> 0} s1 s2
end

module MakeHeterogeneousMap(Key:HETEROGENEOUS_KEY)(Value:HETEROGENEOUS_VALUE) =
  MakeCustomHeterogeneousMap(Key)(Value)(SimpleNode(Key)(Value))

module MakeHeterogeneousSet(Key:HETEROGENEOUS_KEY) =
  MakeCustomHeterogeneousSet(Key)(SetNode(Key))

module MakeCustomMap
    (Key:KEY)
    (Value: VALUE)
    (NODE:NODE with type 'a key = Key.t and type ('key,'map) value = ('key,'map Value.t) snd)
= struct

  module NewKey(* :Key *) = HeterogeneousKeyFromKey(Key)

  module BaseMap = MakeCustomHeterogeneousMap
    (NewKey)(struct type ('key,'map) t = ('key,'map Value.t) snd end)(NODE)
  include BaseMap
  type key = Key.t
  type 'a value = 'a Value.t

  let snd_opt = function
    | None -> None
    | Some x -> Some (Snd x)
  let opt_snd = function
    | None -> None
    | Some (Snd x) -> Some x
  let singleton k v = singleton k (Snd v)
  let find k m = let Snd x = find k m in x
  let find_opt k m = opt_snd (find_opt k m)
  let insert k f m = insert k (fun v -> Snd (f (opt_snd v))) m
  let update k f m = update k (fun v -> snd_opt (f (opt_snd v))) m
  let add k v m = add k (Snd v) m
  let split x m = let (l,m,r) = split x m in (l, opt_snd m, r)
  let unsigned_min_binding m = let KeyValue(key,Snd value) = BaseMap.unsigned_min_binding m in key,value
  let unsigned_max_binding m = let KeyValue(key,Snd value) = BaseMap.unsigned_max_binding m in key,value
  (* let singleton k v = BaseMap.singleton (PolyKey.K k) v *)
  let pop_unsigned_minimum m =
    match BaseMap.pop_unsigned_minimum m with
    | None -> None
    | Some(KeyValue(key,Snd value),m) -> Some(key,value,m)

  let pop_unsigned_maximum m =
    match BaseMap.pop_unsigned_maximum m with
    | None -> None
    | Some(KeyValue(key,Snd value),m) -> Some(key,value,m)

  let is_singleton m = match BaseMap.is_singleton m with
    | None -> None
    | Some(KeyValue(k,Snd v)) -> Some(k,v)

  let filter (f: key -> 'a value -> bool) m = BaseMap.filter {f = fun k (Snd v) -> f k v} m
  let map f a = BaseMap.map {f = fun (Snd v) -> Snd (f v)} a
  let map_no_share f a = BaseMap.map_no_share {f = fun (Snd v) -> Snd (f v)} a
  let mapi (f : key -> 'a value -> 'a value) a = BaseMap.mapi {f = fun k (Snd v) -> Snd (f k v)} a
  let mapi_no_share (f : key -> 'a value -> 'b value) a = BaseMap.mapi_no_share {f = fun k (Snd v) -> Snd (f k v)} a
  let filter_map (f: key -> 'a value -> 'a value option) a =
    BaseMap.filter_map {f=fun k (Snd v) -> snd_opt (f k v) } a
  let filter_map_no_share (f: key -> 'a value -> 'b value option) a =
    BaseMap.filter_map_no_share {f=fun k (Snd v) -> snd_opt (f k v) } a
  let idempotent_union (f: key -> 'a value -> 'a value -> 'a value) a b =
    BaseMap.idempotent_union {f=fun k (Snd v1) (Snd v2) -> Snd (f k v1 v2)} a b
  let idempotent_inter (f: key -> 'a value -> 'a value -> 'a value) a b =
    BaseMap.idempotent_inter {f=fun k (Snd v1) (Snd v2) -> Snd (f k v1 v2)} a b
  let nonidempotent_inter_no_share (f: key -> 'a value -> 'b value -> 'c value) a b =
    BaseMap.nonidempotent_inter_no_share {f=fun k (Snd v1) (Snd v2) -> Snd (f k v1 v2)} a b
  let idempotent_inter_filter (f: key -> 'a value -> 'a value -> 'a value option) a b =
    BaseMap.idempotent_inter_filter {f=fun k (Snd v1) (Snd v2) -> snd_opt (f k v1 v2)} a b
  let reflexive_same_domain_for_all2 (f: key -> 'a value -> 'a value -> bool) a b =
    BaseMap.reflexive_same_domain_for_all2 {f=fun k (Snd v1) (Snd v2) -> f k v1 v2} a b
  let nonreflexive_same_domain_for_all2 (f: key -> 'a value -> 'b value -> bool) a b =
    BaseMap.nonreflexive_same_domain_for_all2 {f=fun k (Snd v1) (Snd v2) -> f k v1 v2} a b
  let reflexive_subset_domain_for_all2 (f: key -> 'a value -> 'a value -> bool) a b =
    BaseMap.reflexive_subset_domain_for_all2 {f=fun k (Snd v1) (Snd v2) -> f k v1 v2} a b
  let slow_merge (f : key -> 'a value option -> 'b value option -> 'c value option) a b = BaseMap.slow_merge {f=fun k v1 v2 -> snd_opt (f k (opt_snd v1) (opt_snd v2))} a b
  let symmetric_difference (f: key -> 'a value -> 'a value -> 'a value option) a b = BaseMap.symmetric_difference {f=fun k (Snd v1) (Snd v2) -> snd_opt (f k v1 v2)} a b
  let difference (f: key -> 'a value -> 'b value -> 'a value option) a b = BaseMap.difference { f=fun k (Snd v1) (Snd v2) -> snd_opt (f k v1 v2) } a b
  let iter (f: key -> 'a value -> unit) a = BaseMap.iter {f=fun k (Snd v) -> f k v} a
  let fold (f: key -> 'a value -> 'acc -> 'acc) m acc = BaseMap.fold {f=fun k (Snd v) acc -> f k v acc} m acc
  let fold_on_nonequal_inter (f: key -> 'a value -> 'a value -> 'acc -> 'acc) ma mb acc =
    let f k (Snd va) (Snd vb) acc = f k va vb acc in
    BaseMap.fold_on_nonequal_inter {f} ma mb acc
  let fold_on_nonequal_union
      (f: key -> 'a value option -> 'a value option -> 'acc -> 'acc) ma mb acc =
    let f k va vb acc =
      let va = Option.map (fun (Snd v) -> v) va in
      let vb = Option.map (fun (Snd v) -> v) vb in
      f k va vb acc in
    BaseMap.fold_on_nonequal_union {f} ma mb acc

  let pretty ?pp_sep (f: Format.formatter -> key -> 'a value -> unit) fmt m =
    BaseMap.pretty ?pp_sep {f=fun fmt k (Snd v) -> f fmt k v} fmt m

  let for_all (f : key -> 'a value -> bool) m = BaseMap.for_all {f = fun k (Snd v) -> f k v} m

  module WithForeign(Map2 : BASE_MAP with type _ key = key) = struct
    module BaseForeign = BaseMap.WithForeign(Map2)
    type ('b,'c) polyfilter_map_foreign = { f: 'a. key -> ('a,'b) Map2.value -> 'c value option } [@@unboxed]
    let filter_map_no_share f m2 =
      BaseForeign.filter_map_no_share { f=fun k v-> snd_opt (f.f k v)} m2


    type ('value,'map2) polyinter_foreign =
      { f: 'a. 'a Map2.key -> 'value value -> ('a, 'map2) Map2.value -> 'value value } [@@unboxed]
    let nonidempotent_inter f m1 m2 =
      BaseForeign.nonidempotent_inter {f = fun k (Snd v) v2 -> Snd (f.f k v v2)} m1 m2

    type ('map1,'map2) polyupdate_multiple = { f: 'a. key -> 'map1 value option -> ('a,'map2) Map2.value -> 'map1 value option } [@@unboxed]
    let update_multiple_from_foreign m2 f m =
      BaseForeign.update_multiple_from_foreign m2 {f = fun k v1 v2 -> snd_opt (f.f k (opt_snd v1) v2)} m

    type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. key -> 'map1 value -> ('a,'map2) Map2.value -> 'map1 value option } [@@unboxed]
    let update_multiple_from_inter_with_foreign m2 f m =
      BaseForeign.update_multiple_from_inter_with_foreign m2 {f = fun k (Snd v1) v2 -> snd_opt (f.f k v1 v2)} m

    type ('map1, 'map2) polydifference = ('map1,'map2) polyupdate_multiple_inter
    let difference f m1 m2 = BaseForeign.difference {f=fun k (Snd v) v2 -> snd_opt (f.f k v v2) } m1 m2
  end

  let to_seq m = Seq.map (fun (KeyValue(key,Snd value)) -> (key,value)) (BaseMap.to_seq m)
  let to_rev_seq m = Seq.map (fun (KeyValue(key,Snd value)) -> (key,value)) (BaseMap.to_rev_seq m)
  let add_seq s m = BaseMap.add_seq (Seq.map (fun (key,value) -> KeyValue(key,Snd value)) s) m

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list s = List.of_seq (to_seq s)

  let reflexive_equal f m1 m2 = reflexive_same_domain_for_all2 (fun _ -> f) m1 m2
  let reflexive_compare f m1 m2 = reflexive_compare {f=fun _ (Snd v1) (Snd v2) -> f v1 v2} m1 m2
end


module MakeMap(Key: KEY) = struct
  module NKey = struct type 'a t = Key.t end
  module Node = SimpleNode(NKey)(WrappedHomogeneousValue)
  include MakeCustomMap(Key)(Value)(Node)
end

module MakeCustomSet
    (Key: KEY)
    (Node:NODE with type 'a key = Key.t and type ('key,'map) value = unit)
: SET with type elt = Key.t and type 'a BaseMap.t = 'a Node.t = struct
  module HKey = HeterogeneousKeyFromKey(Key)
  module S = MakeCustomHeterogeneousSet(HKey)(Node)
  include S
  type key = Key.t
  type elt = key

  let iter (f: elt -> unit) set = S.iter {f} set
  let fold (f: key -> 'acc -> 'acc) set acc = S.fold {f} set acc
  let filter (f: key -> bool) set = S.filter {f} set
  let for_all (f: key -> bool) set = S.for_all {f} set

  let pretty ?pp_sep (f : Format.formatter -> key -> unit) fmt s =
    S.pretty ?pp_sep {f} fmt s

  let is_singleton m = match BaseMap.is_singleton m with
    | None -> None
    | Some(KeyValue(k,())) -> Some k
  let unsigned_min_elt t = let Any x = unsigned_min_elt t in x
  let unsigned_max_elt t = let Any x = unsigned_max_elt t in x
  let pop_unsigned_minimum t = Option.map (fun (Any x, t) -> (x,t)) (pop_unsigned_minimum t)
  let pop_unsigned_maximum t = Option.map (fun (Any x, t) -> (x,t)) (pop_unsigned_maximum t)

  let to_seq m = Seq.map (fun (BaseMap.KeyValue(elt,())) -> elt) (BaseMap.to_seq m)
  let to_rev_seq m = Seq.map (fun (BaseMap.KeyValue(elt,())) -> elt) (BaseMap.to_rev_seq m)
  let add_seq s m = BaseMap.add_seq (Seq.map (fun (elt) -> BaseMap.KeyValue(elt,())) s) m

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list s = List.of_seq (to_seq s)
end

module MakeSet(Key: KEY) = MakeCustomSet(Key)(SetNode(HeterogeneousKeyFromKey(Key)))

module MakeHashconsedHeterogeneousMap(Key:HETEROGENEOUS_KEY)(Value:HETEROGENEOUS_HASHED_VALUE)() = struct
  module Node = HashconsedNode(Key)(Value)()
  include MakeCustomHeterogeneousMap(Key)(Value)(Node)

  let equal = Node.equal
  let compare = Node.compare
  let to_int = Node.to_int
end

module MakeHashconsedHeterogeneousSet(Key:HETEROGENEOUS_KEY)() = struct
  module Node = HashconsedSetNode(Key)()
  include MakeCustomHeterogeneousSet(Key)(Node)

  let equal = Node.equal
  let compare = Node.compare
  let to_int = Node.to_int
end

module MakeHashconsedSet(Key : KEY)() = struct
  module Node = HashconsedSetNode(HeterogeneousKeyFromKey(Key))()
  include MakeCustomSet(Key)(Node)
  let equal = Node.equal
  let compare = Node.compare
  let to_int = Node.to_int
end

module MakeHashconsedMap(Key: KEY)(Value: HASHED_VALUE)() = struct
  module HetValue = HeterogeneousHashedValueFromHashedValue(Value)
  module Node = HashconsedNode(HeterogeneousKeyFromKey(Key))(HetValue)()
  include MakeCustomMap(Key)(Value)(Node)

  let equal = Node.equal
  let compare = Node.compare
  let to_int = Node.to_int
end
