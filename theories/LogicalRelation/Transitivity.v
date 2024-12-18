From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance.

Set Universe Polymorphism.

Section Transitivity.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Set Printing Universes.

 Lemma transEq@{i j k l} {Γ A B C lA lB}
  {RA : [LogRel@{i j k l} lA | Γ ||- A]}
  {RB : [LogRel@{i j k l} lB | Γ ||- B]}
  (RAB : [Γ ||-<lA> A ≅ B | RA])
   (RBC : [Γ ||-<lB> B ≅ C | RB]) :
  [Γ ||-<lA> A ≅ C | RA].
Proof. now eapply LRTransEq. Qed.

Lemma transEqTermU@{h i j k} {Γ l UU t u v} {h : [Γ ||-U<l> UU]} :
  [LogRelRec@{i j k} l | Γ ||-U t ≅ u : UU| h] ->
  [LogRelRec@{i j k} l | Γ ||-U u ≅ v : UU| h] ->
  [LogRelRec@{i j k} l | Γ ||-U t ≅ v : UU| h].
Proof.
  intros [rL ?? redL] [? rR] ; exists rL rR redL; tea.
  + etransitivity; tea.
    unshelve erewrite (redtmwf_det _ _ (URedTm.red redR) (URedTm.red redL0))  ; tea.
    all: apply isType_whnf; apply URedTm.type.
  + apply TyEqRecFwd; unshelve eapply transEq@{h i j k}.
    4,5: now apply (TyEqRecFwd h).
Qed.

Lemma transEqTermNeu {Γ A t u v} {RA : [Γ ||-ne A]} :
  [Γ ||-ne t ≅ u : A | RA] ->
  [Γ ||-ne u ≅ v : A | RA] ->
  [Γ ||-ne t ≅ v : A| RA].
Proof.
  intros [tL] [? tR]; exists tL tR; tea.
  etransitivity; tea.
  unshelve erewrite (redtmwf_det _ _ redR redL0); tea.
  all: eapply whnf_whne, convneu_whne; first [eassumption|symmetry; eassumption].
Qed.


Lemma transEqTermΠ {Γ lA A t u v} {ΠA : [Γ ||-Π<lA> A]}
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (t u v : term),
    [PolyRed.shpRed ΠA ρ h | Δ ||- t ≅ u : _] ->
    [PolyRed.shpRed ΠA ρ h | Δ ||- u ≅ v : _] ->
    [PolyRed.shpRed ΠA ρ h | Δ ||- t ≅ v : _])
  (ihcod : forall (Δ : context) (a b: term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
    (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _]) (t u v : term),
    [PolyRed.posRed ΠA ρ h ha | Δ ||- t ≅ u : _] ->
    [PolyRed.posRed ΠA ρ h ha | Δ ||- u ≅ v : _] ->
    [PolyRed.posRed ΠA ρ h ha | Δ ||- t ≅ v : _]) :
  [Γ ||-Π t ≅ u : A | ΠA ] ->
  [Γ ||-Π u ≅ v : A | ΠA ] ->
  [Γ ||-Π t ≅ v : A | ΠA ].
Proof.
  intros [tL] [? tR].
  unshelve epose proof (e := redtmwf_det _ _ (PiRedTmEq.red redR) (PiRedTmEq.red redL)); tea.
  1,2: now apply PiRedTmEq.whnf.
  exists tL tR.
  + etransitivity; tea. now rewrite e.
  + cbn in *; intros. eapply ihcod.
    2: eapply eqApp0.
    irrelevanceRefl.
    rewrite <- e.
    unshelve apply eqApp; [assumption|].
    eapply ihdom; [| eapply LRTmEqSym]; eassumption.
Qed.

Lemma transEqTermΣ {Γ lA A t u v} {ΣA : [Γ ||-Σ<lA> A]}
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (t u v : term),
    [PolyRed.shpRed ΣA ρ h | Δ ||- t ≅ u : _] ->
    [PolyRed.shpRed ΣA ρ h | Δ ||- u ≅ v : _] ->
    [PolyRed.shpRed ΣA ρ h | Δ ||- t ≅ v : _])
  (ihcod : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
    (ha : [PolyRed.shpRed ΣA ρ h | Δ ||- a ≅ b : _]) (t u v : term),
    [PolyRed.posRed ΣA ρ h ha | Δ ||- t ≅ u : _] ->
    [PolyRed.posRed ΣA ρ h ha | Δ ||- u ≅ v : _] ->
    [PolyRed.posRed ΣA ρ h ha | Δ ||- t ≅ v : _]) :
  [Γ ||-Σ t ≅ u : A | ΣA ] ->
  [Γ ||-Σ u ≅ v : A | ΣA ] ->
  [Γ ||-Σ t ≅ v : A | ΣA ].
Proof.
  intros [tL ?? eqfst eqsnd] [? tR ? eqfst' eqsnd'].
  unshelve epose proof (e := redtmwf_det _ _ (SigRedTmEq.red redR) (SigRedTmEq.red redL)); tea.
  1,2: now apply SigRedTmEq.whnf.
  induction e.
  unshelve eexists tL tR _.
  + intros; eapply ihdom ; [eapply eqfst| eapply eqfst'].
  + etransitivity; tea.
  + intros; eapply ihcod.
    1: irrelevanceRefl; eapply eqsnd.
    eapply LRTmEqConv.
    2: eapply eqsnd'.
    irrelevanceRefl; unshelve eapply PolyRed.posExt.
    4: eapply LRTmEqSym, eqfst.
    assumption.
    Unshelve. all:tea.
Qed.


Lemma transNeNfEq {Γ t u v A} :
  [Γ ||-NeNf t ≅ u : A] ->
  [Γ ||-NeNf u ≅ v : A] ->
  [Γ ||-NeNf t ≅ v : A].
Proof.
  intros [] []; econstructor; tea; now etransitivity.
Qed.

Lemma transEqTermNat {Γ A} (NA : [Γ ||-Nat A]) :
  (forall t u,
    [Γ ||-Nat t ≅ u : A | NA] -> forall v,
    [Γ ||-Nat u ≅ v : A | NA] ->
    [Γ ||-Nat t ≅ v : A | NA]) ×
  (forall t u,
    NatPropEq NA t u -> forall v,
    NatPropEq NA u v ->
    NatPropEq NA t v).
Proof.
  apply NatRedEqInduction.
  - intros * ???? ih ? uv; inversion uv; subst.
    destruct (NatPropEq_whnf prop), (NatPropEq_whnf prop0).
    unshelve epose proof (redtmwf_det _ _ redR redL0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    now eapply ih.
  - easy.
  - intros * ? ih ? uv.
    inversion uv ; subst.
    + econstructor; now eapply ih.
    + match goal with H : [_ ||-NeNf _ ≅ _ : _ ] |- _ => destruct H; apply convneu_whne in conv; inv_whne end.
  - intros ?? tu ? uv; inversion uv; subst.
    1,2: destruct tu; symmetry in conv; apply convneu_whne in conv; inv_whne.
    econstructor; now eapply transNeNfEq.
Qed.

Lemma and_two P Q : Q -> (Q -> P) -> (P × Q).
Proof.
  firstorder.
Qed.

Lemma transEqTermEmpty {Γ A} (NA : [Γ ||-Empty A]) :
  (forall t u,
    [Γ ||-Empty t ≅ u : A | NA] -> forall v,
    [Γ ||-Empty u ≅ v : A | NA] ->
    [Γ ||-Empty t ≅ v : A | NA]) ×
  (forall t u,
    EmptyPropEq Γ t u -> forall v,
    EmptyPropEq Γ u v ->
    EmptyPropEq Γ t v).
Proof.
  eapply and_two.
  - intros ?? tu ? uv; inversion uv; subst.
    destruct tu.
    econstructor; now eapply transNeNfEq.
  - intros HH.
    intros t u tu v uv. inversion uv; subst.
    inversion tu; subst.
    unshelve eapply EmptyPropEq_whnf in prop as HH1. 2: tea. destruct HH1.
    unshelve eapply EmptyPropEq_whnf in prop0 as HH2. 2: tea. destruct HH2.
    unshelve epose proof (redtmwf_det _ _ redL redR0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    eapply HH; eauto.
Qed.

Lemma transIdPropEq {Γ l A} (IA : [Γ ||-Id<l> A]) t u v :
  IdPropEq IA t u -> IdPropEq IA u v -> IdPropEq IA t v.
Proof.
  intros [] h; inversion h; subst.
  - now econstructor.
  - match goal with H : [_ ||-NeNf _ ≅ _ : _ ] |- _ => destruct H; apply convneu_whne in conv; inv_whne end.
  - match goal with H : [_ ||-NeNf _ ≅ _ : _ ] |- _ => destruct H; symmetry in conv; apply convneu_whne in conv; inv_whne end.
  - econstructor; now eapply transNeNfEq.
Qed.

Lemma IdPropEq_whnf {Γ l A} (IA : [Γ ||-Id<l> A]) t u : IdPropEq IA t u -> whnf t × whnf u.
Proof.
  intros []; split; constructor; destruct r; eapply convneu_whne; tea; now symmetry.
Qed.

Lemma transTmEqId {Γ l A} (IA : [Γ ||-Id<l> A]) t u v :
  [Γ ||-Id<l> t ≅ u : _ | IA] -> [Γ ||-Id<l> u ≅ v : _| IA] -> [Γ ||-Id<l> t ≅ v : _| IA].
Proof.
  intros [??? red ? prop] [?? red' ?? prop'].
  pose proof prop as [_ wh]%IdPropEq_whnf.
  pose proof prop' as [wh' _]%IdPropEq_whnf.
  pose proof (redtmwf_det wh wh' red red'); subst.
  unshelve econstructor; cycle 2; tea.
  1: now etransitivity.
  now eapply transIdPropEq.
Qed.


Lemma transEqTerm@{h i j k l} {Γ lA A t u v}
  {RA : [LogRel@{i j k l} lA | Γ ||- A]} :
  [Γ ||-<lA> t ≅ u : A | RA] ->
  [Γ ||-<lA> u ≅ v : A | RA] ->
  [Γ ||-<lA> t ≅ v : A | RA].
Proof.
  revert t u v; pattern lA, Γ, A, RA; apply LR_rect_TyUr; clear lA Γ A RA; intros l Γ.
  - intros *; apply transEqTermU@{h i j k}.
  - intros *; apply transEqTermNeu.
  - intros * ?????. apply transEqTermΠ; tea.
  - intros ? NA **; now eapply (fst (transEqTermNat NA)).
  - intros ? NA **; now eapply (fst (transEqTermEmpty NA)).
  - intros * ?????; apply transEqTermΣ; tea.
  - intros; now eapply transTmEqId.
Qed.


Lemma LREqTermSymConv {Γ t u G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG] ->
  [Γ ||-<l> G' ≅ G | RG'] ->
  [Γ ||-<l> u ≅ t : G' | RG'].
Proof.
  intros Rtu RGG'.
  eapply LRTmEqSym; eapply LRTmEqConv; tea.
  now eapply LRTyEqSym.
Qed.

Lemma LREqTermHelper {Γ t t' u u' G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG] ->
  [Γ ||-<l> t' ≅ u' : G' | RG'] ->
  [Γ ||-<l> G ≅ G' | RG] ->
  [Γ ||-<l> u ≅ u' : G | RG] ->
  [Γ ||-<l> t ≅ t' : G | RG].
Proof.
  intros Rtu Rtu' RGG' Ruu'.
  do 2  (eapply transEqTerm; tea).
  now eapply LREqTermSymConv.
Qed.

End Transitivity.

#[global]
Instance LRTmEqTransitive `{GenericTypingProperties} {Γ A l} (RA : [Γ ||-<l> A]): Transitive (RA.(LRPack.eqTm)).
Proof. intros x y z ; apply transEqTerm. Defined.

#[global]
Instance LRTmEqPER@{i j k l} `{GenericTypingProperties} {Γ l A} (RA : [LogRel@{i j k l} l | Γ ||- A]):
  PER (RA.(LRPack.eqTm)).
Proof. econstructor; typeclasses eauto. Qed.
