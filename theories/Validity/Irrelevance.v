From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Irrelevances.
Context `{GenericTypingProperties}.

Section VRIrrelevant.
Universes u1 u2 u3 u4 v1 v2 v3 v4.

Set Printing Universes.
Lemma VRirrelevant@{} Γ Γ' {veqsubst : forall Δ (h :[|-Δ]) (σ σ' : nat -> term), Type@{u3}} {veqsubst' : forall Δ (h :[|-Δ]) (σ σ' : nat -> term), Type@{v3}}
  (vr : VR@{u1 u2 u3 u4} Γ Γ' veqsubst) (vr' : VR@{v1 v2 v3 v4} Γ Γ'  veqsubst') :
  (forall Δ σ σ' wfΔ wfΔ', veqsubst Δ  wfΔ σ σ' <~> veqsubst' Δ wfΔ' σ σ').
Proof.
  revert veqsubst' vr'.  pattern Γ, Γ', veqsubst, vr.
  apply VR_rect; clear Γ Γ' veqsubst vr.
  - intros ? h; inversion h; intros; split; intros; constructor.
  - intros ???????? ih ? h; inversion h as [|?????? VΓad' VA' ]; subst.
    specialize (ih _ VΓad').
    intros; split; intros []; unshelve econstructor.
    1,2: now eapply ih.
    all: now eapply irrLR.
Qed.

Succeed Constraint u1 < v1.
Succeed Constraint v1 < u1.
Succeed Constraint u2 < v2.
Succeed Constraint v2 < u2.
Succeed Constraint u3 < v3.
Succeed Constraint v3 < u3.
Succeed Constraint u4 < v4.
Succeed Constraint v4 < u4.

End VRIrrelevant.


Lemma irrelevanceSubst {Γ Γ'} (VΓ VΓ' : [||-v Γ ≅ Γ']) {σ σ' Δ} (wfΔ wfΔ' : [|- Δ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] -> [Δ ||-v σ ≅ σ' : Γ | VΓ' | wfΔ'].
Proof.
  eapply VRirrelevant; eapply VAd.adequate.
Qed.

Unset Printing Notations.
Lemma symSubst@{u1 u2 u3 u4} {Γ Γ'}
                     (VΓ  : VAdequate@{u3 u4} VR@{u1 u2 u3 u4} Γ Γ')
                     (VΓ'  : VAdequate@{u3 u4} VR@{u1 u2 u3 u4} Γ' Γ) :
  (* (VΓ VΓ' : [||-v Γ]) : *)
  forall {σ σ' Δ} (wfΔ wfΔ' : [|- Δ]),
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] -> [Δ ||-v σ' ≅ σ : _ | VΓ' | wfΔ'].
Proof.
  revert VΓ'; induction Γ, Γ', VΓ using validity_rect; intros VΓ'.
  - rewrite (invValidityEmpty VΓ'). constructor.
  - pose proof (x := invValiditySnoc VΓ').
    destruct x as [lA'[ VΓ'' [VA' ->]]].
    intros ????? [tleq hdeq].
    pose (tleq' := IHVΓ VΓ'' _ _ _ wfΔ wfΔ' tleq).
    exists tleq'; now eapply symLR, irrLR.
Qed.

Lemma symValidTy {Γ Γ' l A B} {VΓ : [||-v Γ ≅ Γ']} (VΓ' : [||-v Γ' ≅ Γ]) :
  [Γ ||-v<l> A ≅ B | VΓ] -> [Γ' ||-v<l> B ≅ A | VΓ'].
Proof.
  intros; constructor; intros; symmetry.
  now unshelve (eapply validTyExt; tea; now eapply symSubst).
Qed.

Lemma symValid {Γ Γ'} : [||-v Γ ≅ Γ'] -> [||-v Γ' ≅ Γ].
Proof.
  intros VΓ; induction Γ, Γ', VΓ using validity_rect.
  - apply validEmpty.
  - now eapply (validSnoc IHVΓ), symValidTy.
Qed.


Lemma convSubst {Γ Γ' Γ''}
  (VΓ : [||-v Γ ≅ Γ']) (VΓ' : [||-v Γ ≅ Γ'']) :
  forall {Δ} (wfΔ : [|- Δ]) {σ σ'},
  [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ ] ->
  [Δ ||-v σ ≅ σ' : _ | VΓ' | wfΔ ].
Proof.
  revert Γ' VΓ; indValid VΓ'.
  - constructor.
  - intros * ih ? VΓ0 *; pose proof (invValidity VΓ0) as (?&?&?&?&?&e&h); subst; cbn in h; subst.
    intros [tl hd]; pose proof (tl' := ih _ _ _ _ _ _ tl).
    exists tl'; now eapply irrLREqCum.
Qed.

Lemma convSubst' {Γ Γ' Γ''}
  (VΓ : [||-v Γ' ≅ Γ]) (VΓ' : [||-v Γ'' ≅ Γ]) :
  forall {Δ} (wfΔ : [|- Δ]) {σ σ'},
  [Δ ||-v σ ≅ σ' : _ | VΓ' | wfΔ ] ->
  [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ ].
Proof.
  intros; unshelve (eapply symSubst, convSubst, symSubst; tea);
  tea; now eapply symValid.
Qed.

Lemma convValidTy {Γ Γ' Γ''}
  (VΓ : [||-v Γ ≅ Γ']) (VΓ' : [||-v Γ ≅ Γ'']) {l A B} :
  [_ ||-v<l> A ≅ B | VΓ] -> [_ ||-v<l> A ≅ B | VΓ'].
Proof. intros VA; constructor; intros; eapply validTyExt; tea; now eapply convSubst. Qed.

Lemma convValidTy' {Γ Γ' Γ''}
  (VΓ : [||-v Γ ≅ Γ']) (VΓ' : [||-v Γ'' ≅ Γ']) {l A B} :
  [_ ||-v<l> A ≅ B | VΓ] -> [_ ||-v<l> A ≅ B | VΓ'].
Proof.
  intros ?%(symValidTy (symValid VΓ)).
  unshelve now eapply symValidTy, convValidTy.
  now apply symValid.
Qed.


Lemma transSubst {Γ Γ' Γ''}
  (VΓ : [||-v Γ ≅ Γ']) (VΓ' : [||-v Γ' ≅ Γ'']) (VΓ'' : [||-v Γ ≅ Γ'']) :
  forall {σ σ' σ'' Δ} (wfΔ : [|- Δ]),
    [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ ] ->
    [Δ ||-v σ' ≅ σ'' : _ | VΓ' | wfΔ ] ->
    [Δ ||-v σ ≅ σ'' : _ | VΓ'' | wfΔ ].
Proof.
  revert  Γ' VΓ VΓ'; indValid VΓ''.
  - constructor.
  - intros ????? VΓ VA ih ? VΓ0'.
    pose proof (invValidity VΓ0') as (?&?&?&?&?&e&?); subst; cbn in *.
    intros VΓ'; pose proof (invValiditySnoc VΓ') as (?&?&?&?); subst.
    intros ???? wfΔ [tl hd] [tl' hd'].
    pose (tl'' := ih _ _ _ _ _ _ _ _ tl tl').
    exists tl''; etransitivity; [now eapply irrLR|].
    eapply irrLRCum; tea; symmetry; now eapply validTyExt.
Qed.

Lemma ureflValidTy {Γ Γ' l A B} (VΓ : [||-v Γ ≅ Γ']) (VΓ' : [||-v Γ' ≅ Γ']) :
  [Γ ||-v<l> A ≅ B | VΓ] -> [Γ' ||-v<l> B ≅ B | VΓ'].
Proof.
  constructor; intros; etransitivity.
  2: eapply validTyExt; tea; now eapply convSubst'.
  symmetry; eapply validTyExt; tea.
  unshelve eapply convSubst'; [| tea|].
  unshelve (eapply transSubst; tea; now eapply symSubst); tea.
Qed.

Lemma ureflValid {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) : [||-v Γ' ≅ Γ'].
Proof.
  indValid VΓ; [apply validEmpty|].
  intros ????? ? VA ih; eapply (validSnoc ih).
  now eapply ureflValidTy.
Qed.

Lemma irrLvlValidTy {Γ Γ' l l' A B C} (VΓ : [||-v Γ ≅ Γ']) :
  [Γ ||-v<l> A ≅ B | VΓ ] -> [Γ ||-v<l'> B ≅ C | VΓ] -> [Γ ||-v<l> B ≅ C | VΓ].
Proof.
  constructor; intros.
  eapply transLR; [eapply urefl|];  eapply validTyExt; tea.
  unshelve (eapply transSubst; [|eapply convSubst, symSubst]; tea).
  2: now eapply symValid.
  now eapply ureflValid.
Qed.

Lemma transValidTy {Γ Γ' Γ'' l l' A B C}
  (VΓ : [||-v Γ ≅ Γ']) (VΓ' : [||-v Γ' ≅ Γ'']) (VΓ'' : [||-v Γ ≅ Γ'']) :
  [Γ ||-v<l> A ≅ B | VΓ ] -> [Γ' ||-v<l'> B ≅ C | VΓ'] -> [Γ ||-v<l> A ≅ C | VΓ''].
Proof.
  constructor; intros; etransitivity; eapply validTyExt; tea.
  2: eapply irrLvlValidTy; [now eapply convValidTy|now eapply convValidTy'].
  eapply transSubst; tea.
  unshelve now eapply convSubst, symSubst.
  now eapply symValid.
  Unshelve. now apply symValid.
Qed.

Lemma transValid {Γ Γ' Γ''} : [||-v Γ ≅ Γ'] -> [||-v Γ' ≅ Γ''] -> [||-v Γ ≅ Γ''].
Proof.
  intros VΓ; revert Γ''; indValid VΓ.
  - easy.
  - intros * VA ih ? VΓ0.
    pose proof (invValidity VΓ0) as (?&?&?&VΓ'&?&e&?); subst; cbn in *; subst.
     eapply (validSnoc (ih _ VΓ')), transValidTy; tea.
Qed.


Instance perValid : PER (VAdequate VR).
Proof.
  constructor; red; intros; [now apply symValid|now eapply transValid].
Qed.

Instance perSubst {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) {Δ} (wfΔ : [|- Δ]) : PER (VΓ.(VPack.eqSubst) _ wfΔ).
Proof.
  constructor; red; intros.
  - unshelve now eapply symSubst, convSubst, convSubst'.
    all: first [now symmetry| now eapply urefl].
  - unshelve now eapply transSubst; tea; eapply convSubst'.
    now eapply urefl.
Qed.

Instance perValidTy {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : PER (typeValidity _ _ VΓ l).
Proof.
  constructor; red; intros.
  - unshelve now eapply symValidTy, convValidTy, convValidTy'.
    all: first [now symmetry| now eapply urefl].
  - unshelve now eapply transValidTy; tea; eapply convValidTy'.
    now eapply urefl.
Qed.

Instance iperValidTy l : IPER (VAdequate VR) (fun _ => term) (fun _ _ VΓ => typeValidity _ _ VΓ l).
Proof.
  constructor.
  - intros; now eapply symValidTy.
  - intros; now eapply transValidTy.
Defined.

Lemma irrSubst {Γ0 Γ0' Γ1 Γ1'} {VΓ0 : [||-v Γ0 ≅ Γ0']} {VΓ1 : [||-v Γ1 ≅ Γ1']} :
  [||-v Γ0 ≅ Γ1] ->
  forall {Δ} (wfΔ : [|- Δ]) {σ σ'},
  [Δ ||-v σ ≅ σ' : _ | VΓ0 | wfΔ ] ->
  [Δ ||-v σ ≅ σ' : _ | VΓ1 | wfΔ ].
Proof.
  intros; unshelve now eapply convSubst', convSubst.
  now etransitivity.
Qed.

Lemma irrValidTy  {Γ0 Γ0' Γ1 Γ1' l A B}
  {VΓ0 : [||-v Γ0 ≅ Γ0']}
  {VΓ1 : [||-v Γ1 ≅ Γ1']}
  : [||-v Γ0 ≅ Γ1] -> [Γ0 ||-v<l> A ≅ B | VΓ0] -> [Γ1 ||-v<l> A ≅ B | VΓ1].
Proof.
  intros; unshelve now eapply convValidTy, convValidTy'.
  etransitivity; [|tea]; now symmetry.
Qed.

Lemma irrValidTyRfl {Γ Γ' l A B}
  {VΓ VΓ' : [||-v Γ ≅ Γ']}
  : [Γ ||-v<l> A ≅ B | VΓ] -> [Γ ||-v<l> A ≅ B | VΓ'].
Proof.
  eapply irrValidTy; now eapply lrefl.
Qed.

Lemma symValidTy' {Γ Γ' l A B} {VΓ : [||-v Γ ≅ Γ']} :
  [_ ||-v<l> A ≅ B | VΓ] -> [_ ||-v<l> B ≅ A | symValid VΓ].
Proof. eapply symValidTy. Qed.



(* Still useful ?*)
Lemma irrelevanceLift {l A F G Γ} (VΓ : [||-v Γ])
  (VFG : [Γ ||-v<l> F ≅ G | VΓ]) :
  [Γ ,, F ||-v<l> A | validSnoc VΓ VFG] ->
  [Γ ,, G ||-v<l> A | validSnoc VΓ (symmetry VFG)].
Proof.
  intros; eapply irrValidTy; tea; now eapply validSnoc.
Qed.

Lemma irrValidTm {Γ0 Γ0' Γ1 Γ1' l l0 l1 A0 A0' A1 A1' t u}
  {VΓ0 : [||-v Γ0 ≅ Γ0']}
  {VΓ1 : [||-v Γ1 ≅ Γ1']}
  (VΓ01 : [||-v Γ0 ≅ Γ1])
  (VA0 : [_ ||-v<l0> A0 ≅ A0' | VΓ0])
  (VA1 : [_ ||-v<l1> A1 ≅ A1' | VΓ1]) :
  [_ ||-v<l> A0 ≅ A1 | VΓ01] ->
  [_ ||-v<l0> t ≅ u : _ | _ | VA0] ->
  [_ ||-v<l1> t ≅ u :  _ | _ | VA1].
Proof.
  intros VA Vt; constructor; intros.
  assert [VΓ0 | _ ||-v σ ≅ σ' : _ | wfΔ]
  by (eapply irrSubst; tea; now symmetry).
  eapply irrLRCum.
  2: now unshelve now eapply validTmExt.
  eapply validTyExt; tea.
  now eapply lrefl, convSubst.
Qed.

Lemma irrValidTmRfl {Γ Γ' l A A' B B' t u}
  {VΓ VΓ' : [||-v Γ ≅ Γ']}
  {VA : [Γ ||-v<l> A ≅ B | VΓ]}
  {VA' : [Γ ||-v<l> A' ≅ B' | VΓ']} :
  A = A' ->
  [_ ||-v<l> t ≅ u : _ | _ | VA] -> [_ ||-v<l> t ≅ u : _ | _ | VA'].
Proof.
  intros ?; subst.
  unshelve now eapply irrValidTm; eapply convValidTy; eapply lrefl.
  now eapply lrefl.
Qed.


Instance perValidTm {Γ Γ' l A A'} (VΓ : [||-v Γ ≅ Γ']) (VA : [_ ||-v<l> A ≅ A' | VΓ]) :
  PER (termEqValidity _ _ _ _ _ VΓ VA).
Proof.
  constructor; red; intros; constructor; intros.
  - eapply symLR, irrLRConv.
    2: (unshelve now eapply validTmExt) ; tea; now symmetry.
    eapply validTyExt; tea; now eapply urefl.
  - unshelve now etransitivity; eapply irrLR; eapply validTmExt.
    all: first [eassumption | now eapply lrefl].
Qed.

Lemma symValidTm {Γ Γ' l A A' t t'}
  {VΓ : [||-v Γ ≅ Γ']} (VΓ' : [||-v Γ' ≅ Γ])
  {VA : [Γ ||-v<l> A ≅ A' | VΓ]} (VA' : [_ ||-v<l> A' ≅ A | VΓ']) :
  [_ ||-v<l> t ≅ t' : _ | _ | VA] -> [_ ||-v<l> t' ≅ t : _ | _ | VA'].
Proof. intros; symmetry; now eapply irrValidTm. Qed.

Lemma symValidTm' {Γ Γ' l A A' t t'}
  {VΓ : [||-v Γ ≅ Γ']} {VA : [_ ||-v<l> A ≅ A' | VΓ]} :
  [_ ||-v<l> t ≅ t' : _ | _ | VA] -> [_ ||-v<l> t' ≅ t : _ | _ | symValidTy' VA ].
Proof. now apply symValidTm. Qed.

Lemma transValidTm {Γ Γ' Γ'' l A A' A'' t t' t''}
  {VΓ : [||-v Γ ≅ Γ']} (VΓ' : [||-v Γ' ≅ Γ'']) (VΓ'' : [||-v Γ ≅ Γ''])
  {VA : [Γ ||-v<l> A ≅ A' | VΓ]} (VA' : [_ ||-v<l> A' ≅ A'' | VΓ']) (VA'' : [_ ||-v<l> A ≅ A'' | VΓ'']) :
  [_ ||-v<l> t ≅ t' : _ | _ | VA] ->
  [_ ||-v<l> t' ≅ t'' : _ | _ | VA'] ->
  [_ ||-v<l> t ≅ t'' : _ | _ | VA''].
Proof.
  intros; etransitivity; eapply irrValidTm.
  2,4: tea.
  1: eapply irrValidTy, lrefl; tea; now eapply lrefl.
  symmetry; eapply irrValidTy; tea.
  Unshelve. 1: now eapply lrefl. now symmetry.
Qed.


Lemma irrelevanceSubstEqExt {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) {σ1 σ1' σ2 σ2' Δ}
  (wfΔ : [|- Δ]) (eq1 : σ1 =1 σ1') (eq2 : σ2 =1 σ2') :
  [Δ ||-v σ1 ≅ σ2 : Γ | VΓ | wfΔ ] ->
  [Δ ||-v σ1' ≅ σ2' : Γ | VΓ | wfΔ ].
Proof.
  revert Δ wfΔ σ1 σ1' σ2 σ2' eq1 eq2; indValid VΓ.
  - constructor.
  - intros ??????? ih ?????? eq1 eq2 [tl hd].
    unshelve eexists (ih _ _ _ _ _ _ _ _ tl).
    1,2: red; intros; eauto.
    rewrite <- (eq1 var_zero); rewrite <- (eq2 var_zero).
    eapply irrLREq; tea; now rewrite eq1.
Qed.

End Irrelevances.

#[global] Existing Instance perValid.
#[global] Existing Instance perSubst.
#[global] Existing Instance perValidTy.
#[global] Existing Instance iperValidTy.
#[global] Existing Instance perValidTm.