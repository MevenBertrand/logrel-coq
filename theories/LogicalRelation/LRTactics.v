From Ltac2 Require Import Ltac2 Printf.
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation PERTactics.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity Weakening Neutral Reduction InstKripke NormalRed.


Definition packed_TmLR `{GenericTypingProperties} Γ l :=
  packed_iper (LRAdequate Γ (LogRel l)) (fun _ _ RA => RA.(LRPack.eqTm)).

Instance packed_TmLR_PER `{GenericTypingProperties} Γ l : PER (packed_TmLR Γ l) :=
  packed_iper_per.

Definition mkPTmLR  `{GenericTypingProperties} {Γ l A B} {RA : [Γ ||-<l> A ≅ B]} {t u}
  : [Γ ||-<l> t ≅ u : _ | RA] -> packed_TmLR Γ l ⦇ A ; t ⦈ ⦇ B ; u ⦈ :=
  mk_packed_iper ⦇ A ; t ⦈ ⦇ B ; u ⦈ RA.

Ltac2 mkPTm c := constr:(mkPTmLR $c).


Ltac2 tyLR_matcher ty pfopt :=
  lazy_match! ty with
  | LRAdequate ?g ?rec ?a ?a' => Some (g, g'), pfopt
  | typeValidity ?g ?g' (VAd.pack ?vg) _ _ _ => Some (g, g'), Some vg
  | termEqValidity ?g ?g' _ _ _ ?vg _ _ _ => Some (g, g'), Some vg
  | _ => None, None
  end.

Ltac2 valid_ctx_rel h c :=
  match valid_ctx_matcher c (Some (Control.hyp h)) with
  | Some (g, g'), Some vg => [g,g',vg]
  | _, _ => []
  end.

Ltac2 valid_ty_matcher ty pfopt :=
  lazy_match! ty with
  | typeValidity ?g ?g' (VAd.pack ?vg) ?l ?a ?a' => Some (g, g', vg, a, a', l), pfopt
  | termEqValidity ?g ?g' ?l ?a ?a' ?vg ?va _ _ => Some (g, g', vg, a, a', l), Some va
  | _ => None, None
  end.

Ltac2 valid_ty_rel st h c :=
  match valid_ty_matcher c (Some (Control.hyp h)) with
  | Some (g, _g', vg, a, a', _l), Some va =>
    let (g0, wgg0) := Option.get_bt (PER.repr st g) in
    let va0 := mkvty constr:(irrValidTy (VΓ0:=$vg) (VΓ1:=urefl $wgg0) $wgg0 $va) in
    [pair g0 a, pair g0 a',  va0 ]
  | _, _ => []
  end.


Ltac2 valid_tm_matcher ty pfopt :=
  lazy_match! ty with
  | termEqValidity ?g ?g' ?_l ?a ?a' ?_vg ?va ?t ?t' => Some (pair g a, pair g' a', mkvty va, t, t'), pfopt
  | _ => None, None
  end.

Definition ureflValidTy `{GenericTypingProperties} {Γ Γ' l A B} {VΓ : [||-v Γ ≅ Γ']} (VΓ' := urefl VΓ) :
  [Γ ||-v<l> A ≅ B | VΓ] -> [_ ||-v<l> B ≅ B | VΓ'].
Proof. apply ureflValidTy. Defined.

Ltac2 valid_tm_rel st h c :=
  lazy_match! c with
  | termEqValidity ?g ?_g' ?_l ?a ?_a' ?_vg ?va ?t ?t' =>
    let h := Control.hyp h in
    let (g0, wgg0) := Option.get_bt (PER.repr st g) in
    (* let va0 := mkvty constr:(irrValidTy (VΓ0:=$vg) (VΓ1:=urefl $wgg0) $wgg0 $va) in *)
    let (ga0, waa0) := Option.get_bt (PER.repr st (pair g0 a)) in
    let vaa0 := constr:(convValidTy' _ $wgg0 (dsnd $waa0)) in
    let vt0 := mkvtm constr:(irrValidTm $wgg0 $va (ureflValidTy $vaa0) $vaa0 $h) in
    [pair ga0 t, pair ga0 t', vt0]
  | _ => []
  end.

Ltac2 fail s := Control.throw (Tactic_failure (Some (Message.of_string s))).

Ltac2 solve_ctx st g g' :=
  match PER.get_witness_cstr st (g, g') with
  | Some w => Control.refine (fun _ => w)
  | None => fail "Contexts are not convertibles"
  end.

Ltac2 solve_ty st g _g' vg _l a a' :=
  let (g0, wgg0) := Option.get_bt (PER.repr st g) in
  match PER.get_witness_cstr st (pair g0 a, pair g0 a') with
  | Some w => Control.refine (fun _ => constr:(irrValidTy (VΓ1:=$vg) (symmetry $wgg0) (dsnd $w)))
  | None => fail "Types are not convertibles"
  end.

Ltac2 solve_tm st g _g' vg a _a' va _l t t' :=
  let (g0, wgg0) := Option.get_bt (PER.repr st g) in
  let (ga0, waa0) := Option.get_bt (PER.repr st (pair g0 a)) in
  match PER.get_witness_cstr st (pair ga0 t, pair ga0 t') with
  | Some w =>
    let va0a := constr:(convValidTy _ (symmetry $wgg0) (dsnd (symmetry $waa0))) in
    Control.refine (fun _ => constr:(irrValidTm (VΓ1:=$vg) (symmetry $wgg0) _ $va $va0a (dsnd $w)))
  | None => fail "Terms are not convertibles"
  end.

Ltac2 solve_any st g :=
  lazy_match! g with
  | VAdequate VR ?g ?g' => solve_ctx st g g'
  | typeValidity ?g ?g' (VAd.pack ?vg) ?l ?a ?a' => solve_ty st g g' vg l a a'
  | termEqValidity ?g ?g' ?l ?a ?a' ?vg ?va ?t ?t' => solve_tm st g g' vg a a' va l t t'
  | _ => fail "Term does not match"
  end.

Ltac2 init n :=
  let st := PER.make n in
  List.iter (PER.add_rel st valid_ctx_rel) (Control.hyps ()) ;
  List.iter (PER.add_rel st (valid_ty_rel st)) (Control.hyps ()) ;
  List.iter (PER.add_rel st (valid_tm_rel st)) (Control.hyps ()) ; st.

Ltac2 irrValid () := let st := init 42 in solve_any st (Control.goal ()).

Ltac irrValid := ltac2:(Control.enter irrValid).



