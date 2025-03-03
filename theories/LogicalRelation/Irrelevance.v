(** * LogRel.LogicalRelation.Irrelevance: symmetry and irrelevance of the logical relation. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.

(** We show a general version of irrelevance, saying that the relation associated to
  two witnesses of reducibility of A (Γ ||-<l1> A ≅ B1 and Γ ||-<l2> A ≅ B2) coincide. *)
(** Interestingly, we also show irrelevance with respect to universe levels, which is crucial
in later parts of the development, where this avoids creating spurious constraints on universe levels.*)

Section Irrelevance.
  Context `{GenericTypingProperties}.

  Universe v.
  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Section Defs.
  Universe i j k l i' j' k' l'.

  Definition cumImpl l := forall Γ A B, [LogRel@{i j k l} l | Γ ||- A ≅ B] -> [LogRel@{i' j' k' l'} l | Γ ||- A ≅ B].
  Definition cum l := forall Γ A B, [LogRel@{i j k l} l | Γ ||- A ≅ B] <≈> [LogRel@{i' j' k' l'} l | Γ ||- A ≅ B].

  Definition irr {Γ l1 l2 A B1 B2} (RA1 : [Γ ||-<l1> A ≅ B1]) (RA2 : [Γ ||-<l2> A ≅ B2]) :=
    forall t u, [LogRel@{i j k l} l1 | Γ ||- t ≅ u : _ | RA1] <≈> [LogRel@{i' j' k' l'} l2 | Γ ||- t ≅ u : _ | RA2].

  End Defs.

  Lemma irrImplU@{h i j k l h' i' j' k' l' } {l1 l2}
    (ih : forall l, l << l1 -> l << l2 -> cumImpl@{h i j k h' i' j' k'} l)
    {Γ A B1 B2} (h : [Γ ||-U<l1> A ≅ B1]) (h' : [Γ ||-U<l2> A ≅ B2]) {t u} :
    [LogRel@{i j k l} l1 | _ ||- t ≅ u : _ | LRU_ h] -> [LogRel@{i' j' k' l'} l2 | _ ||- t ≅ u : _| LRU_ h'].
  Proof.
    assert (eq : h.(URedTy.level) = h'.(URedTy.level)) by now destruct h.(URedTy.lt), h'.(URedTy.lt).
    cbn ; intros [].
    eapply redTyRecFwd in relEq.
    unshelve econstructor.
    4: eapply redTyRecBwd.
    1-3: destruct h, h'; cbn in *; subst; tea; cbn.
    eapply ih ; [|eapply URedTy.lt|].
    all: rewrite <-eq; tea; eapply URedTy.lt.
  Qed.


  Universe i j k l i' j' k' l'.

  Let irr {Γ l1 l2 A B1 B2} (RA1 : [Γ ||-<l1> A ≅ B1]) (RA2 : [Γ ||-<l2> A ≅ B2]) :=
    Eval unfold irr in irr@{i j k l i' j' k' l'} RA1 RA2.

  Lemma irrU@{h h'} {l1 l2}
    (ih : forall l, l << l1 -> l << l2 -> cum@{h i j k h' i' j' k'} l)
    {Γ A B1 B2} (h : [Γ ||-U<l1> A ≅ B1]) (h' : [Γ ||-U<l2> A ≅ B2]) : irr (LRU_ h) (LRU_ h').
  Proof.
    intros ??; split; eapply irrImplU;
    intros ? lt1 lt2 ???; [apply (fst (ih _ lt1 lt2 _ _ _) ) | apply (snd (ih _ lt2 lt1 _ _ _) )].
  Qed.

  Section IrrΠ.
  Context {l1 l2 Γ A B1 B2} (ΠA: [Γ ||-Π< l1 > A ≅ B1]) (ΠA': [Γ ||-Π< l2 > A ≅ B2])
    (ihdom: forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) B2 (R2 : [Δ ||-< l2 > (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ B2]),
      irr (PolyRed.shpRed ΠA ρ h) R2)
    (ihcod: forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ]) (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _ ]) B2
      (R2 : [Δ ||-< l2 > (ParamRedTy.codL ΠA)[a .: ρ >> tRel] ≅ B2]), irr (PolyRed.posRed ΠA ρ h ha) R2)
    (eqdom: ParamRedTy.domL ΠA' = ParamRedTy.domL ΠA)
    (eqcod: ParamRedTy.codL ΠA' = ParamRedTy.codL ΠA).

  Lemma irrIsLRFun : forall t, isLRFun ΠA' t <≈> isLRFun ΠA t.
  Proof.
    destruct ΠA, ΠA'; cbn in *; subst.
    intros ? ; split ; intros [|]; constructor; tea; cbn in *.
    1,2: unshelve (intros; eapply ihcod;  apply e); tea; now eapply ihdom.
  Qed.

  Lemma irrPiRedTm0 {t} : PiRedTm ΠA' t <≈> PiRedTm ΠA t.
  Proof.
    split; intros [? red]; econstructor.
    2,4: now eapply irrIsLRFun.
    all: revert red; cbn; now rewrite eqdom, eqcod.
  Defined.

  Lemma irrΠ : irr (LRPi' ΠA) (LRPi' ΠA').
  Proof.
    intros ?? ; split ; intros [rL rR].
    - exists (snd irrPiRedTm0 rL) (snd irrPiRedTm0 rR); cbn.
      1: now rewrite eqdom, eqcod.
      intros; destruct ΠA, ΠA'; cbn in *; subst.
      (unshelve eapply ihcod, eqApp); tea; now eapply ihdom.
    - exists (fst irrPiRedTm0 rL) (fst irrPiRedTm0 rR); cbn.
      1: now rewrite <-eqdom, <-eqcod.
      intros; destruct ΠA, ΠA'; cbn in *; subst.
      (unshelve eapply ihcod, eqApp); tea; now eapply ihdom.
  Qed.

  End IrrΠ.

  Section IrrΣ.
  Context {l1 l2 Γ A B1 B2} (ΣA: [Γ ||-Σ< l1 > A ≅ B1]) (ΣA': [Γ ||-Σ< l2 > A ≅ B2])
    (ihdom: forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) B2 (R2 : [Δ ||-< l2 > (ParamRedTy.domL ΣA)⟨ρ⟩ ≅ B2]), irr (PolyRed.shpRed ΣA ρ h) R2)
    (ihcod: forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ]) (ha : [PolyRed.shpRed ΣA ρ h | Δ ||- a ≅ b : _]) B2
      (R2 : [Δ ||-< l2 > (ParamRedTy.codL ΣA)[a .: ρ >> tRel] ≅ B2]), irr (PolyRed.posRed ΣA ρ h ha) R2)
    (eqdom: ParamRedTy.domL ΣA' = ParamRedTy.domL ΣA)
    (eqcod: ParamRedTy.codL ΣA' = ParamRedTy.codL ΣA).

  Lemma irrIsLRPair : forall t, isLRPair ΣA' t <≈> isLRPair ΣA t.
  Proof.
    destruct ΣA, ΣA'; cbn in *; subst.
    intros ? ; split ; intros [|].
    2,4: constructor; tea; cbn in *.
    1,2: unshelve eapply PairLRPair; tea; cbn in *.
    1,2: now unshelve (intros; now eapply ihdom).
    all: now unshelve (intros; eapply ihcod; eauto).
  Qed.

  Lemma irrRedSigTm0 : forall t, SigRedTm ΣA' t <≈> SigRedTm ΣA t.
  Proof.
    intros; split; intros [? red ?%irrIsLRPair]; econstructor; tea.
    all: revert red; cbn; now rewrite eqdom, eqcod.
  Defined.

  Lemma irrΣ : irr (LRSig' ΣA) (LRSig' ΣA').
  Proof.
    intros ??; split; intros []; unshelve econstructor.
    1,2,4,5: now eapply irrRedSigTm0.
    all: cbn in *; destruct ΣA, ΣA'; cbn in *; subst; tea.
    1,2: now unshelve (intros; eapply ihdom; eauto).
    1,2: now unshelve (intros; eapply ihcod; eauto).
  Qed.

  End IrrΣ.

  Section IrrId.
  Context {l1 l2 Γ A B1 B2} (IA: [Γ ||-Id< l1 > A ≅ B1]) (IA': [Γ ||-Id< l2 > A ≅ B2])
    (ih: forall B2 (R2 : [Γ ||-< l2 > IdRedTy.tyL IA ≅ B2]), irr (IdRedTy.tyRed IA) R2)
    (eqty: IdRedTy.tyL IA' = IdRedTy.tyL IA)
    (eqlhs: IdRedTy.lhsL IA' = IdRedTy.lhsL IA)
    (eqrhs: IdRedTy.rhsL IA' = IdRedTy.rhsL IA).

  Lemma irrId : irr (LRId' IA) (LRId' IA').
  Proof.
    intros ??; split.
    + intros [????? prop]; unshelve econstructor; cbn.
      3-5: rewrite eqty, eqlhs, eqrhs; cbn; tea.
      destruct prop; constructor; tea; cbn in *.
      all:rewrite ?eqty, ?eqlhs, ?eqrhs; cbn; tea.
      all: destruct IA, IA'; cbn in *; subst; now eapply ih.
    + intros [?? rL rR eq prop]; unshelve econstructor; cbn in *.
      3-5: now rewrite eqty, eqlhs, eqrhs in rL, rR, eq.
      destruct prop; constructor; tea; cbn in *.
      all:rewrite <-?eqty, <-?eqlhs, <-?eqrhs; cbn; tea.
      all: destruct IA, IA'; cbn in *; subst; now eapply ih.
  Qed.

  End IrrId.


  Lemma irrLR_rec@{h h'}
    {l1 l2}
    (ih : forall l, l << l1 -> l << l2 -> cum@{h i j k h' i' j' k'} l)
    {Γ A B1 B2} (R1 : [Γ ||-<l1> A ≅ B1]) (R2 : [Γ ||-<l2> A ≅ B2]) : irr R1 R2.
  Proof.
    pose (i := invLREqL_whred R1 R2).
    revert B2 R2 i ih; indLR R1.
    - intros h B2 R2 [h'] ih; subst; now eapply irrU.
    - intros neA ?? [neB [? eq]] _; subst; intros ??; split; cbn.
      + intros []; econstructor; now rewrite eq.
      + intros [??]; econstructor; now rewrite eq in *.
    - intros ΠA ihdom ihcod ?? [ΠA' [? eqdom eqcod]] ?; subst; cbn in *.
      now eapply irrΠ.
    - intros NA ?? [NA' ?] ?; subst; intros ??; split; now cbn.
    - intros EA ?? [EA' ?] ?; subst; intros ??; split; now cbn.
    - intros ΣA ihdom ihcod ?? [ΣA' [? eqdom eqcod]] ?; subst; cbn in *.
      now eapply irrΣ.
    - intros IA ih ?? [IA' [? eqty eqlhs eqrhs]] ?; subst.
      now eapply irrId.
  Qed.


#[local]
Lemma cumPolyRed@{h h'} {lA}
  (ih : forall l, l << lA -> cum@{h i j k h' i' j' k'} l)
  (Γ : context) (shp shp' pos pos' : term)
  (PA : PolyRed@{i j k l} Γ lA shp shp' pos pos')
  (IHshp : forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] ->
    [LogRel@{i' j' k' l'} lA | Δ ||- shp⟨ρ⟩ ≅ shp'⟨ρ⟩])
  (IHpos : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
          [PolyRed.shpRed PA ρ h | _ ||- a ≅ b : _] ->
          [LogRel@{i' j' k' l'} lA | Δ ||- pos[a .: ρ >> tRel] ≅ pos'[b .: ρ >> tRel]]) :
  PolyRed@{i' j' k' l'} Γ lA shp shp' pos pos'.
Proof.
  unshelve econstructor.
  + intros ; now eapply IHshp.
  + intros; cbn; unshelve eapply IHpos; tea; now eapply irrLR_rec.
Qed.


Lemma cumLR_rec@{h h'} {lA}
  (ih : forall l, l << lA -> cum@{h i j k h' i' j' k'} l)
  {Γ A B} (lr : [ LogRel@{i j k l} lA | Γ ||- A ≅ B ]) :
  [ LogRel@{i' j' k' l'} lA | Γ ||- A ≅ B ].
Proof.
  revert ih; indLR lr.
  - intros [] ? ; eapply LRU_; now econstructor.
  - intros; now eapply LRne_.
  - intros [] IHdom IHcod ?; cbn in *.
    eapply LRPi'; econstructor.
    5: now eapply cumPolyRed.
    all: tea.
  - intros; now eapply LRNat_.
  - intros; now eapply LREmpty_.
  - intros [] IHdom IHcod ?; cbn in *.
    eapply LRSig'; econstructor.
    5: now eapply cumPolyRed.
    all: tea.
  - intros [] IHPar ?; cbn in *.
    eapply LRId'; unshelve econstructor.
    8-10: tea.
    1: now eapply IHPar.
    1,2: now apply  (irrLR_rec (fun l lt _ => ih l lt) tyRed).
    constructor.
    + intros ?? ?%(irrLR_rec (fun l lt _ => ih l lt) tyRed).
      apply (irrLR_rec (fun l lt _ => ih l lt) tyRed); now symmetry.
    + intros ??? ?%(irrLR_rec (fun l lt _ => ih l lt) tyRed) ?%(irrLR_rec (fun l lt _ => ih l lt) tyRed).
      apply (irrLR_rec (fun l lt _ => ih l lt) tyRed); now etransitivity.
Qed.

End Irrelevance.

Lemma cumLR0@{i j k l i' j' k' l' v} `{GenericTypingProperties} :
  cum@{v i j k l i' j' k' l'} zero.
Proof.
  intros; split; eapply cumLR_rec;
  intros ? h; inversion h.
Qed.



Theorem irrLR@{i j k l i' j' k' l' v} `{GenericTypingProperties} {l1 l2}
  {Γ A B1 B2} (R1 : [Γ ||-<l1> A ≅ B1]) (R2 : [Γ ||-<l2> A ≅ B2]) :
    irr@{v i j k l i' j' k' l'} R1 R2.
Proof.
  split; eapply irrLR_rec; intros l [] ?; exact cumLR0.
Qed.

Theorem cumLR@{i j k l i' j' k' l'} `{GenericTypingProperties} {lA}
  {Γ A B} (lr : [ LogRel@{i j k l} lA | Γ ||- A ≅ B ]) :
  [ LogRel@{i' j' k' l'} lA | Γ ||- A ≅ B ].
Proof.
  eapply cumLR_rec; tea; intros ? []; exact cumLR0.
Qed.
