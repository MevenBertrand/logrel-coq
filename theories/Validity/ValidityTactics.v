From Ltac2 Require Import Ltac2 Printf.
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.Validity Require Import Validity Irrelevance Properties PERTactics.


Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.


#[projections(primitive)]
Record nprod {A B : Type} := pair { nfst : A ; nsnd : B }.
Arguments nprod : clear implicits.
Arguments pair {_ _} _ _.
Notation "x <&> y" := (nprod x y) (at level 80, right associativity).

#[projections(primitive)]
Record sum {A : Type} {B : A -> Type} :=
  dpair { dfst : A ; dsnd : B dfst }.
Arguments sum : clear implicits.
Arguments dpair {_ _} _ _.

Notation "'∑&' x .. y , p" := (sum _ (fun x => .. (sum _ (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑&'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition packed_valid_ty `{GenericTypingProperties} l : crelation (context <&> term) :=
  fun p1 p2 => ∑& (VΓ : [||-v nfst p1 ≅ nfst p2]), [_ ||-v<l> nsnd p1 ≅ nsnd p2 | VΓ].

Instance packed_valid_tyPER `{GenericTypingProperties} l : PER (packed_valid_ty l).
Proof.
  constructor.
  - intros ?? []; econstructor; now eapply symValidTy'.
  - intros ??? [? xy] [? yz]; unshelve (econstructor; eapply transValidTy> [exact xy | exact yz]).
    now etransitivity.
Qed.

Definition mkVty `{GenericTypingProperties} {l Γ Γ' A A'} {VΓ : [||-v Γ ≅ Γ']} (VA : [_ ||-v<l> A ≅ A' | VΓ]) :
  packed_valid_ty l (pair Γ A) (pair Γ' A') :=
  dpair VΓ VA.

Definition packed_valid_tm `{GenericTypingProperties} l : crelation ((context <&> term) <&> term) :=
  fun p1 p2 => ∑& (VΓA : packed_valid_ty l (nfst p1) (nfst p2)), [_ ||-v<l> nsnd p1 ≅ nsnd p2 : _ | dfst VΓA | dsnd VΓA].

Instance packed_valid_tmPER `{GenericTypingProperties} l : PER (packed_valid_tm l).
Proof.
  constructor.
  - intros ?? []; unshelve (econstructor;  now eapply symValidTm); now symmetry.
  - intros ??? [? xy] [? yz].
    unshelve (econstructor; eapply transValidTm > [exact xy | exact yz]).
    now etransitivity.
Qed.


Definition mkVtm `{GenericTypingProperties} {l Γ Γ' A A' t t'} {VΓ : [||-v Γ ≅ Γ']} {VA : [_ ||-v<l> A ≅ A' | VΓ]} (Vt : [_ ||-v<l> t ≅ t' : _ | VΓ | VA]) :
  packed_valid_tm l (pair (pair Γ A) t) (pair (pair Γ' A') t') :=
  dpair (mkVty VA) Vt.

Ltac2 mkvty c := constr:(mkVty $c).
Ltac2 mkvtm c := constr:(mkVtm $c).
Ltac2 pair a b := constr:(pair $a $b).

Ltac2 valid_ctx_matcher ty pfopt :=
  lazy_match! ty with
  | VAdequate VR ?g ?g' => Some (g, g'), pfopt
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


Module Examples.
Section Examples.
Context `{GenericTypingProperties}.

Context {Γ0 Γ1 Γ2} (VΓ01 : [||-v Γ0 ≅ Γ1]) (VΓ02 : [||-v Γ0 ≅ Γ2]).

Lemma VΓ12 : [||-v Γ1 ≅ Γ2].
Proof.
  irrValid ().
Qed.

Context {l A B C D} (VAB : [_ ||-v<l> A ≅ B | VΓ01]) (VDC : [_ ||-v<l> C ≅ D | VΓ12]).

Lemma VBB2 (VΓ22 := urefl VΓ02) : [_ ||-v<l> B |VΓ22].
Proof.
  irrValid ().
Qed.

Lemma VAD10 (VΓ10 := symmetry VΓ01) (VCB : [_ ||-v<l> C ≅ B | VΓ12]) :
  [_ ||-v<l> A ≅ D | VΓ10].
Proof.
  irrValid ().
Qed.

Context {t u v} (Vtu : [_ ||-v<l> t ≅ u : _ | _ | VAB]) (Vvu : [_ ||-v<l> v ≅ u : _ | _ | VBB2]).

Lemma Vtt :  [_ ||-v<l> t ≅ t : _ | _ | VAB].
Proof.
  irrValid ().
Qed.

Lemma Vvt (VCB : [_ ||-v<l> C ≅ B | VΓ12]) : [_ ||-v<l> v ≅ t : _ | _ | VAD10 VCB].
Proof.
  irrValid ().
Qed.

End Examples.
End Examples.

