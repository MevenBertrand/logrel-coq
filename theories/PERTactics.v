From Coq Require Import CRelationClasses.
From LogRel Require Import Utils.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require FMap FSet Constr.
Import FSet.Tags.

(* Prerequisites *)

Ltac2 array_extend (v : 'a array) (default : 'a) :=
  let old_size := Array.length v in
  let size := Int.add  1 (Int.mul old_size 2) in
  Control.assert_bounds "UFBase.extend" (Int.le old_size size) ;
  let table := Array.make size default in
  Array.lowlevel_blit v 0 table 0 old_size ;
  table.

Ltac2 unif (c : constr) (id : ident) : bool :=
  let c' := Control.hyp id in
  Control.once_plus
    (fun () => Unification.unify_with_full_ts c c' ; true)
    (fun _ => false).

Ltac2 mem_unif (c : constr) (ids : ident list)  : ident option :=
  List.find_opt (unif c) ids.

Ltac2 ident_of_constr (c : constr) : ident :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var h => h
  | _ =>
    let h := Fresh.in_goal @pt in
    Std.pose (Some h) c ;
    h
  end.

Ltac2 Type exn ::= [Panic(string)].

Ltac2 default_panic (msg : string) (x : 'a option) : 'a :=
  match x with
  | Some a => a
  | None => Control.throw (Panic msg)
  end.

Ltac2 match_rel (r : constr -> constr -> constr) c :=
  Control.once_plus (fun () =>
    let a := open_constr:(_) in
    let b := open_constr:(_) in
    Unification.unify_with_full_ts c (r a b) ;
    Some (a,b))
    (fun _ => None).

Module BiMap.
  Ltac2 Type ('a,'b) t := ('a * 'b) list.

  Ltac2 empty : ('a,'b) t := [].

  Ltac2 assoc (eqa : 'a -> 'a -> bool) (a : 'a) (m : ('a,'b) t) : 'b option :=
    Option.map snd (List.find_opt (fun (a', _) => eqa a a') m).

  Ltac2 assoc_inv (eqb : 'b -> 'b -> bool) (b : 'b) (m : ('a,'b) t) : 'a option :=
    Option.map fst (List.find_opt (fun (_, b') => eqb b b') m).

  Ltac2 assoc_dflt (eqa : 'a -> 'a -> bool) dflt (a : 'a) (m : ('a,'b) t) : 'b :=
    Option.default dflt (assoc eqa a m).

  Ltac2 assoc_inv_dflt (eqb : 'b -> 'b -> bool) dflt (b : 'b) (m : ('a,'b) t) : 'a :=
    Option.default dflt (assoc_inv eqb b m).

  Ltac2 mem (eqa : 'a -> 'a -> bool) (a : 'a) (m : ('a,'b) t) : bool :=
    match (assoc eqa a m) with | Some _ => true | _ => false end.

  Ltac2 mem_inv (eqb : 'b -> 'b -> bool) (b : 'b) (m : ('a,'b) t) : bool :=
    match (assoc_inv eqb b m) with | Some _ => true | _ => false end.

  Ltac2 push (a : 'a) (b : 'b) (m : ('a,'b) t) : ('a,'b) t :=
    (a,b) :: m.

  Ltac2 domain (m : ('a,'b) t) : 'a list := List.map fst m.
  Ltac2 image (m : ('a,'b) t) : 'b list := List.map snd m.

End BiMap.



Module UF.

(* Representation of the elements of the disjoint-union structure
  should always be >= 0, -1 representing an absence of data/root node *)
Ltac2 Type elt := int.

(* Representation of witnesses of relatedness between elements x -> y
  cannot be 0, negative values correspond to the reverse witness y -> x *)
Ltac2 Type witness := int.

Ltac2 Type st := {
    mutable last : int ;
    mutable table : (elt * witness list) array ;
    mutable numwits : int ;
  }.

Ltac2 make (size : int) : st :=
  Control.assert_valid_argument "union find size should be positive" (Int.ge size 0) ;
  { last := 0; numwits := 0; table := Array.make size (-1, []) }.

Ltac2 extend (x : st) : unit :=
  x.(table) := array_extend (x.(table)) (-1, []).

Ltac2 add (x : st) : elt :=
  (if Int.equal (x.(last)) (Array.length (x.(table)))
  then extend x else ()) ;
  let r := x.(last) in
  x.(last) := Int.add r 1 ;
  r.

Ltac2 rec root (x : st) (k : int) : elt * witness list :=
  let (i, wski) := Array.get (x.(table)) k in
  if Int.equal i (-1)
  then
    Control.assert_bounds "BaseUF.root non-empty witness list" (Int.equal (List.length wski) 0) ;
    k, []
  else
    let (r, wsir)  := root x i in
    let b := Int.equal r i in
    let wskr := if b then wski else List.append wsir wski in
    (if b then () else Array.set (x.(table)) k (r, wskr)) ;
    r, wskr.

Ltac2 inverse_path (l : witness list) : witness list :=
  List.rev_map Int.neg l.

Ltac2 unify (x : st) k l : witness option :=
  let (r1, wskr1) := root x k in
  let (r2, wslr2) := root x l in
  if Int.equal r1 r2
  then None
  else
    let wkl := Int.add (x.(numwits)) 1 in
    x.(numwits) := wkl ;
    let wsr1r2 := List.append wslr2 (wkl :: inverse_path wskr1) in
    Array.set (x.(table)) r1 (r2, wsr1r2) ;
    Some wkl.

Ltac2 rec drop_prefix p q :=
  match p, q with
  | x :: xs, y :: ys =>
    if Int.equal x y
    then drop_prefix xs ys
    else (p, q)
  | _, _ => (p, q)
  end.

(*normalizes a path from k -> l given paths k -> r and l -> r *)
Ltac2 normalize_path (wskr : witness list) (wslr : witness list) : witness list :=
  let (wski, wsli) := drop_prefix wskr wslr in
  List.append (inverse_path wsli) wski.

Ltac2 conv (x : st) (k : elt) (l : elt) : witness list option :=
  if Int.equal k l
  then Some []
  else
    let (r1, wskr1) := root x k in
    let (r2, wslr2) := root x l in
    if Int.equal r1 r2
    then Some (normalize_path wskr1 wslr2)
    else None.

End UF.


Module PER.

Ltac2 lrfl c := preterm:(lrefl $preterm:c).
Ltac2 urfl c := preterm:(urefl $preterm:c).
Ltac2 trans c1 c2 := preterm:(transitivity $preterm:c1 $preterm:c2).
Ltac2 symm c := preterm:(symmetry $preterm:c).

Ltac2 Type st := {
  mutable pts_id_bimap : (ident, UF.elt) BiMap.t ;
  mutable id_qrefl : (ident, preterm) FMap.t ;
  mutable id_to_wits : (UF.witness, preterm) FMap.t ;
  st : UF.st ;
}.

Ltac2 id_of_pt (x : st) (h : ident) : UF.elt :=
  BiMap.assoc_dflt Ident.equal (-1) h (x.(pts_id_bimap)).

Ltac2 pt_of_id (x : st) (pt : UF.elt) : ident :=
  BiMap.assoc_inv_dflt Int.equal (@foo) pt (x.(pts_id_bimap)).

(* Ltac2 qrefl_of_id (x : st) (i : ident) : preterm :=
  Option.get (FMap.find_opt i (x.(id_qrefl))). *)

Ltac2 witness_of_id (x : st) (i : UF.witness) : preterm :=
  Option.get (FMap.find_opt i (x.(id_to_wits))).

Ltac2 make n := {
  pts_id_bimap := BiMap.empty ;
  id_qrefl := FMap.empty FSet.Tags.ident_tag ;
  id_to_wits := FMap.empty FSet.Tags.int_tag ;
  st := UF.make n ;
}.

Ltac2 add_pt (x : st) (h : ident) : unit :=
  if BiMap.mem Ident.equal h (x.(pts_id_bimap)) then ()
  else x.(pts_id_bimap) := BiMap.push h (UF.add (x.(st))) (x.(pts_id_bimap)).

Ltac2 get_pt_cstr (x : st) (c : constr) : ident option :=
  (* shortcut the case where c = Var h ? *)
  mem_unif c (BiMap.domain (x.(pts_id_bimap))).

Ltac2 add_pt_cstr (x : st) (c : constr) : ident :=
  match get_pt_cstr x c with
  | Some h => h
  | None =>
    let h := ident_of_constr c in
    add_pt x h;
    h
  end.

Ltac2 add_qrefl (x : st) (h : ident) (pf : preterm) :=
  if FMap.mem h (x.(id_qrefl)) then () else x.(id_qrefl) := FMap.add h pf (x.(id_qrefl)).


Ltac2 add_witness (x : st) c1 c2 pf :=
  let h1 := add_pt_cstr x c1 in
  let h2 := add_pt_cstr x c2 in
  let k1 := id_of_pt x h1 in
  let k2 := id_of_pt x h2 in
  add_qrefl x h1 (lrfl pf) ;
  add_qrefl x h2 (urfl pf) ;
  match UF.unify (x.(st)) k1 k2 with
  | None => ()
  | Some n =>
    x.(id_to_wits) := FMap.add n pf (x.(id_to_wits))
  end.

Ltac2 build_witness (x : st) h l :=
  let map i :=
    if Int.le i 0
    then symm (witness_of_id x (Int.neg i))
    else witness_of_id x i
  in
  (* printf "building witness from %t" (Control.hyp h) ; *)
  match List.map map l with
  | [] => default_panic "build_witness/qrefl" (FMap.find_opt h (x.(id_qrefl)))
  | [c] => c
  | c :: cs => List.fold_left (fun c1 c2 => trans c2 c1) c cs
  end.

Ltac2 equiv (x : st) cx cy :=
  Option.default false
    (Option.bind (get_pt_cstr x cx) (fun hx =>
      Option.bind (get_pt_cstr x cy) (fun hy =>
        Option.map (fun _ => true)
           (UF.conv (x.(st)) (id_of_pt x hx) (id_of_pt x hy))))).

Ltac2 get_witness (x : st) h1 h2 :=
  match BiMap.assoc Ident.equal h1 (x.(pts_id_bimap)),
    BiMap.assoc Ident.equal h2 (x.(pts_id_bimap)) with
  | Some k1, Some k2 =>
    let postprocess w := (* Constr.pretype *) (build_witness x h1 w) in
    Option.map postprocess (UF.conv (x.(st)) k1 k2)
    (* Option.map postprocess (Control.time (Some "Conv:") (fun () => UF.conv (x.(st)) k1 k2)) *)
  | _, _ => None
  end.

Ltac2 get_witness_cstr st (cx, cy) :=
  Option.bind (get_pt_cstr st cx) (fun hx =>
    Option.bind (get_pt_cstr st cy) (fun hy =>
      get_witness st hx hy)).

Ltac2 repr (x : st) (c : constr) : (constr * preterm) option :=
  Option.bind (get_pt_cstr x c) (fun h =>
    let (hr, w) := UF.root (x.(st)) (id_of_pt x h) in
    Some (Control.hyp (pt_of_id x hr), build_witness x h w)).

Ltac2 qrefl st (c : constr) :=
  (* Option.map Constr.pretype *) (Option.bind (get_pt_cstr st c) (fun i =>
    FMap.find_opt i (st.(id_qrefl)))).

Ltac2 add_rel (st : st) (f : ident  -> constr -> (constr * constr * preterm) list)  (hyp : ident * constr option * constr) : unit :=
  let (hpf, _, c) := hyp in
  List.iter (fun (a,b, pf) => add_witness st a b pf) (f hpf c).

Ltac2 init_with extractor (n : int) : constr * constr -> constr option :=
  let st := make n in
  List.iter (add_rel st extractor) (Control.hyps ()) ;
  fun cs => Option.map Constr.pretype (get_witness_cstr st cs).

Ltac2 solve_with extractor matcher n :=
  let solver := init_with extractor n in
  match matcher (Control.goal ()) with
  | None => Control.throw (Tactic_failure (Some (fprintf "Goal does not match.")))
  | Some (cx, cy) =>
    match solver (cx, cy) with
    | None => Control.throw (Tactic_failure (Some (fprintf "No equivalence found between %t and %t." cx cy)))
    | Some w => Control.refine (fun _ => w)
    end
  end.

Ltac2 lift_matcher matcher h c :=
  match matcher c with | None => [] | Some (cx, cy) => [cx, cy, let c := Control.hyp h in preterm:($c)] end.

Ltac2 solve0 n :=
  match! goal with
  | [|- ?r _ _ ] =>
    let matchr := match_rel (fun cx cy => open_constr:($r $cx $cy)) in
    solve_with (lift_matcher matchr) matchr n
  end.

Ltac2 solve1 extractor n :=
  match! goal with
  | [|- ?r _ _ ] =>
    let matchr := match_rel (fun cx cy => open_constr:($r $cx $cy)) in
    solve_with extractor matchr n
  end.


Module Notations.
  Ltac2 Notation "per" "with" extractor(tactic(6)) :=
    solve1 extractor 5.
  Ltac2 Notation "per" := solve0 5.
End Notations.

End PER.

