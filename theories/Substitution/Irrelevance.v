
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Reflexivity Transitivity.

Set Universe Polymorphism.

Section Irrelevances.
Context `{GenericTypingProperties}.

Section VRIrrelevant.
Universes u1 u2 u3 u4 v1 v2 v3 v4.

Lemma VRirrelevant Γ {veqsubst veqsubst'}
  (vr : VR@{u1 u2 u3 u4} Γ veqsubst) (vr' : VR@{v1 v2 v3 v4} Γ  veqsubst') :
  (forall Δ σ σ' wfΔ wfΔ', veqsubst Δ  wfΔ σ σ' <~> veqsubst' Δ wfΔ' σ σ').
Proof.
  revert veqsubst' vr'.  pattern Γ, veqsubst, vr.
  apply VR_rect; clear Γ veqsubst vr.
  - intros ? h; inversion h; intros; split; intros; constructor.
  - intros ?????? ih ? h; inversion h.
    specialize (ih _ VΓad0).
    intros; split; intros []; unshelve econstructor.
    1,2: now eapply ih.
    all: irrelevanceCum.
Qed.

Fail Fail Constraint u1 < v1.
Fail Fail Constraint v1 < u1.
Fail Fail Constraint u2 < v2.
Fail Fail Constraint v2 < u2.
Fail Fail Constraint u3 < v3.
Fail Fail Constraint v3 < u3.
Fail Fail Constraint u4 < v4.
Fail Fail Constraint v4 < u4.

End VRIrrelevant.

Lemma irrelevanceSubst {Γ} (VΓ VΓ' : [||-v Γ]) {σ Δ} (wfΔ wfΔ' : [|- Δ]) :
  [Δ ||-v σ : Γ | VΓ | wfΔ] -> [Δ ||-v σ : Γ | VΓ' | wfΔ'].
Proof.
  eapply VRirrelevant; eapply VAd.adequate.
Qed.

Lemma irrelevanceSubstEq {Γ} (VΓ VΓ' : [||-v Γ]) {σ σ' Δ} (wfΔ wfΔ' : [|- Δ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] -> [Δ ||-v σ ≅ σ' : Γ | VΓ' | wfΔ'].
Proof.
  eapply VRirrelevant; eapply VAd.adequate.
Qed.

Set Printing Primitive Projection Parameters.

(* Lemma reflSubst {Γ} (VΓ : [||-v Γ]) : forall {σ Δ} (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
  [Δ ||-v σ ≅ σ : Γ | VΓ | wfΔ | Vσ].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih. unshelve econstructor.
    1: apply ih.
    exact (validHead Vσ).
Qed. *)

Unset Printing Notations.
Lemma symmetrySubstEq@{u1 u2 u3 u4} {Γ}
                     (VΓ VΓ' : VAdequate@{u3 u4} Γ VR@{u1 u2 u3 u4}) :
  (* (VΓ VΓ' : [||-v Γ]) : *)
  forall {σ σ' Δ} (wfΔ wfΔ' : [|- Δ]),
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] -> [Δ ||-v σ' ≅ σ : Γ | VΓ' | wfΔ'].
Proof.
  revert VΓ'; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros VΓ'. rewrite (invValidityEmpty VΓ'). constructor.
  - intros * ih VΓ'. pose proof (x := invValiditySnoc VΓ').
    destruct x as [lA'[ VΓ'' [VA' ->]]].
    intros ????? [tleq hdeq].
    unshelve econstructor.
    1: now eapply ih.
    symmetry; revert hdeq; apply LRTmEqConv.
    eapply validTyExt.
Qed.

#[global]
Instance substEqSymmetric {Γ Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) :
  Symmetric (VΓ.(VPack.eqSubst) Δ wfΔ).
Proof. intros x y. eapply (symmetrySubstEq VΓ VΓ wfΔ wfΔ). Qed.

Lemma transSubstEq {Γ} (VΓ : [||-v Γ]) :
  forall {σ σ' σ'' Δ} (wfΔ : [|- Δ]),
    [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
    [Δ ||-v σ' ≅ σ'' : Γ | VΓ | wfΔ ] ->
    [Δ ||-v σ ≅ σ'' : Γ | VΓ | wfΔ ].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [] []; unshelve econstructor.
    1:  now eapply ih.
    etransitivity; [irrelevance|].
    eapply LRTmEqConv; tea.
    unshelve eapply LRTyEqSym; tea.
    2: unshelve eapply validTyExt.
    5: eassumption.
    1: tea.
Qed.

#[global]
Instance substEqTransitive {Γ Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) :
  Transitive (VΓ.(VPack.eqSubst) Δ wfΔ).
Proof. intros x y z. eapply (transSubstEq VΓ wfΔ). Qed.

#[global]
Instance substEqPER {Γ Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) :
  PER (VΓ.(VPack.eqSubst) Δ wfΔ).
Proof. constructor; typeclasses eauto. Qed.


Lemma irrelevanceTy {Γ} : forall (VΓ VΓ' : [||-v Γ]) {l A},
  [Γ ||-v<l> A | VΓ] -> [Γ ||-v<l> A | VΓ'].
Proof.
  intros VΓ VΓ' l A [VA VAext]; unshelve econstructor; intros.
  - unshelve (eapply VA; now eapply irrelevanceSubstEq); tea.
  - eapply VAext; eapply irrelevanceSubstEq; eassumption.
Qed.

Lemma irrelevanceTy' {Γ Γ' A A' l} (VΓ : [||-v Γ]) (VΓ' : [||-v Γ']) (VA : [Γ ||-v<l> A | VΓ]) :
  A = A' -> Γ = Γ' -> [Γ' ||-v<l> A' | VΓ'].
Proof.
  intros eqA eqΓ; subst; now eapply irrelevanceTy.
Qed.

Lemma irrelevanceLift {l A F G Γ} (VΓ : [||-v Γ])
  (VF: [Γ ||-v<l> F | VΓ]) (VG: [Γ ||-v<l> G | VΓ])
  (VFeqG : [Γ ||-v<l> F ≅ G | VΓ | VF]) :
  [Γ ,, F ||-v<l> A | validSnoc VΓ VF] ->
  [Γ ,, G ||-v<l> A | validSnoc VΓ VG].
Proof.
  intros [VA VAext]; unshelve econstructor.
  - intros ???? [hd tl]. eapply VA.
    unshelve econstructor. 1: eassumption.
    eapply LRTmEqConv. 2: eassumption.
    eapply LRTyEqSym; unshelve eapply VFeqG; tea; now eapply lrefl.
  - intros ???? [??]. eapply VAext.
Qed.

Lemma irrelevanceTyEq {Γ l l' A B} (VΓ VΓ' : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) (VA' : [Γ||-v<l'> A | VΓ']) :
  [Γ ||-v< l > A ≅ B | VΓ | VA] -> [Γ ||-v< l' > A ≅ B | VΓ' | VA'].
Proof.
  intros [h]; constructor; intros.
  irrelevanceRefl.
  unshelve apply h. 1:eassumption.
  eapply irrelevanceSubstEq; eassumption.
Qed.

Lemma irrelevanceTyEq' {Γ l A A' B} (VΓ VΓ' : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) (VA' : [Γ||-v<l> A' | VΓ']) : A = A' ->
  [Γ ||-v< l > A ≅ B | VΓ | VA] -> [Γ ||-v< l > A' ≅ B | VΓ' | VA'].
Proof.
  intros ->; now eapply irrelevanceTyEq.
Qed.

Lemma symValidTyEq {Γ l l' A B} {VΓ : [||-v Γ]} {VA : [Γ ||-v<l> A | VΓ]} (VB : [Γ ||-v<l'> B | VΓ]) :
  [Γ ||-v<l> A ≅ B | VΓ | VA] -> [Γ ||-v<l'> B ≅ A | VΓ | VB].
Proof.
  intros; constructor; intros.
  eapply LRTyEqSym; now eapply validTyEq.
  Unshelve. 1:tea. now symmetry.
Qed.

Lemma transValidTyEq {Γ l l' A B C} {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]} {VB : [Γ ||-v<l'> B | VΓ]} :
  [Γ ||-v<l> A ≅ B | VΓ | VA] -> [Γ ||-v<l'> B ≅ C | VΓ | VB] -> [Γ ||-v<l> A ≅ C | VΓ | VA].
Proof.
  constructor; intros; eapply LRTransEq; now eapply validTyEq.
  Unshelve. 1: tea. now eapply urefl.
Qed.


Lemma irrelevanceTm'' {Γ l l' t A} (VΓ VΓ' : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) (VA' : [Γ||-v<l'> A | VΓ']) :
  [Γ ||-v<l> t : A | VΓ | VA] -> [Γ ||-v<l'> t : A | VΓ' | VA'].
Proof.
  intros [h2]; unshelve econstructor.
  intros. irrelevanceRefl.
  unshelve apply h2. 1:eassumption.
  now eapply irrelevanceSubstEq.
Qed.

Lemma irrelevanceTm' {Γ l l' t A A'} (VΓ VΓ' : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) (VA' : [Γ||-v<l'> A' | VΓ']) :
  A = A' -> [Γ ||-v<l> t : A | VΓ | VA] -> [Γ ||-v<l'> t : A' | VΓ' | VA'].
Proof.
  intros ->; now eapply irrelevanceTm''.
Qed.

Lemma irrelevanceTm {Γ l t A} (VΓ VΓ' : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) (VA' : [Γ||-v<l> A | VΓ']) :
  [Γ ||-v<l> t : A | VΓ | VA] -> [Γ ||-v<l> t : A | VΓ' | VA'].
Proof.
  now eapply irrelevanceTm''.
Qed.



Lemma irrelevanceTmLift {l t A F G Γ} (VΓ : [||-v Γ])
  (VF: [Γ ||-v<l> F | VΓ]) (VG: [Γ ||-v<l> G | VΓ])
  (VFeqG : [Γ ||-v<l> F ≅ G | VΓ | VF])
  (VA : [Γ ,, F ||-v<l> A | validSnoc VΓ VF])
  (VA' : [Γ ,, G ||-v<l> A | validSnoc VΓ VG])  :
  [Γ ,, F ||-v<l> t : A | validSnoc VΓ VF | VA] ->
  [Γ ,, G ||-v<l> t : A | validSnoc VΓ VG | VA'].
Proof.
  intros [Vtext]; unshelve econstructor.
  intros ???? [hd tl]. irrelevanceRefl.
  unshelve eapply Vtext; tea.
  unshelve econstructor; tea.
  eapply LRTmEqConv; tea.
  eapply LRTyEqSym; unshelve eapply VFeqG; tea.
  now eapply lrefl.
Qed.

Lemma irrelevanceTmEq {Γ l t u A} (VΓ VΓ' : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) (VA' : [Γ||-v<l> A | VΓ']) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA] -> [Γ ||-v<l> t ≅ u : A | VΓ' | VA'].
Proof.
  intros [h]; constructor; intros; irrelevanceRefl.
  unshelve apply h; tea.
  eapply irrelevanceSubstEq; eassumption.
Qed.

Lemma irrelevanceTmEq' {Γ l t u A A'} (VΓ VΓ' : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) (VA' : [Γ||-v<l> A' | VΓ']) :
  A = A' -> [Γ ||-v<l> t ≅ u : A | VΓ | VA] -> [Γ ||-v<l> t ≅ u : A' | VΓ' | VA'].
Proof.
  intros ->; now eapply irrelevanceTmEq.
Qed.

Lemma symValidTmEq {Γ l t u A} {VΓ : [||-v Γ]} {VA : [Γ ||-v<l> A | VΓ]} :
  [Γ ||-v<l> t ≅ u : A| VΓ | VA] -> [Γ ||-v<l> u ≅ t : A | VΓ | VA].
Proof.
  intros; constructor; intros.
  eapply LRTmEqSym; eapply LRTmEqConv.
  2: now eapply validTmEq.
  eapply validTyExt.
  Unshelve. 1: tea. now symmetry.
Qed.

Lemma transValidTmEq {Γ l t u v A} {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]} :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA] ->
  [Γ ||-v<l> u ≅ v : A | VΓ | VA] ->
  [Γ ||-v<l> t ≅ v : A | VΓ | VA].
Proof.
  constructor; intros; etransitivity.
  1: now eapply validTmEq.
  eapply LRTmEqConv.
  2: now eapply validTmEq.
  eapply LRTyEqSym; eapply validTyExt.
  Unshelve. 1,6-8:tea. now eapply urefl.
Qed.

#[global]
Instance validTmEqSymmetric {Γ l A} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
  Symmetric (fun t u => [Γ ||-v<l> t ≅ u : _ | VΓ | VA]).
Proof. intros x y; eapply symValidTmEq. Qed.

#[global]
Instance validTmEqTransitive {Γ l A} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
  Transitive (fun t u => [Γ ||-v<l> t ≅ u : _ | VΓ | VA]).
Proof. intros x y z. eapply transValidTmEq. Qed.

(* Lemma irrelevanceSubstExt {Γ} (VΓ : [||-v Γ]) {σ σ' Δ} (wfΔ : [|- Δ]) :
  σ =1 σ' -> [Δ ||-v σ : Γ | VΓ | wfΔ] -> [Δ ||-v σ' : Γ | VΓ | wfΔ].
Proof.
  revert σ σ'; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros ????? ih ?? eq.  unshelve econstructor.
    + eapply ih. 2: now eapply eqTail.
      now rewrite eq.
    + rewrite <- (eq var_zero).
      pose proof (eqHead X).
      irrelevance. now rewrite eq.
Qed. *)

Lemma irrelevanceSubstEqExt {Γ} (VΓ : [||-v Γ]) {σ1 σ1' σ2 σ2' Δ}
  (wfΔ : [|- Δ]) (eq1 : σ1 =1 σ1') (eq2 : σ2 =1 σ2') :
  [Δ ||-v σ1 ≅ σ2 : Γ | VΓ | wfΔ ] ->
  [Δ ||-v σ1' ≅ σ2' : Γ | VΓ | wfΔ ].
Proof.
  revert σ1 σ1' σ2 σ2' eq1 eq2; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros ????? ih ???? eq1 eq2 X. unshelve econstructor.
    + eapply irrelevanceSubstEq.
      unshelve eapply ih.
      5: now eapply eqTail.
      all: now rewrite ?eq1, ?eq2.
    + rewrite <- (eq1 var_zero); rewrite <- (eq2 var_zero).
      pose proof (eqHead X).
      irrelevance.
      rewrite eq1; reflexivity.
Qed.

End Irrelevances.

Ltac irrValid :=
  match goal with
  | [_ : _ |- [||-v _]] => idtac
  | [_ : _ |- [ _ ||-v _ : _ | _ | _]] => eapply irrelevanceSubst
  | [_ : _ |- [ _ ||-v _ ≅ _ : _ | _ | _ ]] => eapply irrelevanceSubstEq
  | [_ : _ |- [_ ||-v<_> _ | _]] => eapply irrelevanceTy
  | [_ : _ |- [_ ||-v<_> _ ≅ _ | _ | _]] => eapply irrelevanceTyEq
  | [_ : _ |- [_ ||-v<_> _ : _ | _ | _]] => eapply irrelevanceTm
  | [_ : _ |- [_ ||-v<_> _ ≅ _ : _ | _ | _]] => eapply irrelevanceTmEq
  end; eassumption.