(** * LogRel.LogicalRelation.Irrelevance: symmetry and irrelevance of the logical relation. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape.
 (* ShapeView Reflexivity . *)

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.


Section Irrelevance.
  Context `{GenericTypingProperties}.

  Universe v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).


  Let irr {Γ l1 l2 A B1 B2} (RA1 : [Γ ||-<l1> A ≅ B1]) (RA2 : [Γ ||-<l2> A ≅ B2]) :=
    forall t u, [Γ ||-<l1> t ≅ u : _ | RA1] <≈> [Γ ||-<l2> t ≅ u : _ | RA2].

  Let irrImpl {Γ l1 l2 A B1 B2} (RA1 : [Γ ||-<l1> A ≅ B1]) (RA2 : [Γ ||-<l2> A ≅ B2]) :=
    forall t u, [Γ ||-<l1> t ≅ u : _ | RA1] -> [Γ ||-<l2> t ≅ u : _ | RA2].

  Lemma irrImplU {l1 l2} {Γ A B1 B2} (h : [Γ ||-U<l1> A ≅ B1]) (h' : [Γ ||-U<l2> A ≅ B2]) : irrImpl (LRU_ h) (LRU_ h').
  Proof.
    assert (eq : h.(URedTy.level) = h'.(URedTy.level)) by now destruct h.(URedTy.lt), h'.(URedTy.lt).
    cbn ; intros ?? [].
    eapply redTyRecFwd in relEq.
    unshelve econstructor.
    4: eapply redTyRecBwd.
    all: destruct h, h'; cbn in *; subst; tea; cbn.
  Qed.

  Lemma irrU {l1 l2} {Γ A B1 B2} (h : [Γ ||-U<l1> A ≅ B1]) (h' : [Γ ||-U<l2> A ≅ B2]) : irr (LRU_ h) (LRU_ h').
  Proof. intros ??; split; eapply irrImplU. Qed.

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

  Lemma irrPiRedTm {t} : PiRedTm ΠA' t <≈> PiRedTm ΠA t.
  Proof.
    split; intros [? red]; econstructor.
    2,4: now eapply irrIsLRFun.
    all: revert red; cbn; now rewrite eqdom, eqcod.
  Defined.

  Lemma irrΠ : irr (LRPi' ΠA) (LRPi' ΠA').
  Proof.
    intros ?? ; split ; intros [rL rR].
    - exists (snd irrPiRedTm rL) (snd irrPiRedTm rR); cbn.
      1: now rewrite eqdom, eqcod.
      intros; destruct ΠA, ΠA'; cbn in *; subst.
      (unshelve eapply ihcod, eqApp); tea; now eapply ihdom.
    - exists (fst irrPiRedTm rL) (fst irrPiRedTm rR); cbn.
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

  Lemma irrRedSigTm : forall t, SigRedTm ΣA' t <≈> SigRedTm ΣA t.
  Proof.
    intros; split; intros [? red ?%irrIsLRPair]; econstructor; tea.
    all: revert red; cbn; now rewrite eqdom, eqcod.
  Defined.

  Lemma irrΣ : irr (LRSig' ΣA) (LRSig' ΣA').
  Proof.
    intros ??; split; intros []; unshelve econstructor.
    1,2,4,5: now eapply irrRedSigTm.
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


  Theorem irrLR {l1 l2}
    {Γ A B1 B2} (R1 : [Γ ||-<l1> A ≅ B1]) (R2 : [Γ ||-<l2> A ≅ B2]) : irr R1 R2.
  Proof.
    pose (i := invLREqL_whred R1 R2).
    revert B2 R2 i; indLR R1.
    - intros h B2 R2 [h']; subst; eapply irrU.
    - intros neA ?? [neB [? eq]]; subst; intros ??; split; cbn.
      + intros []; econstructor; now rewrite eq.
      + intros [??]; econstructor; now rewrite eq in *.
    - intros ΠA ihdom ihcod ?? [ΠA' [? eqdom eqcod]]; subst; cbn in *.
      now eapply irrΠ.
    - intros NA ?? [NA' ?]; subst; intros ??; split; now cbn.
    - intros EA ?? [EA' ?]; subst; intros ??; split; now cbn.
    - intros ΣA ihdom ihcod ?? [ΣA' [? eqdom eqcod]]; subst; cbn in *.
      now eapply irrΣ.
    - intros IA ih ihkr ?? [IA' [? eqty eqlhs eqrhs]]; subst.
      now eapply irrId.
  Qed.

End Irrelevance.



Section Symmetry.
  Context `{GenericTypingProperties}.

  Universe v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record sym {Γ l A B} {R : [Γ ||-<l> A ≅ B]} :=
    { symRed : [Γ ||-<l> B ≅ A] ;
      symRedTm : forall {t u}, [Γ ||-<l> t ≅ u : _ | symRed] <≈> [Γ ||-<l> u ≅ t : _ | R] }.

  Arguments sym : clear implicits.
  Arguments sym {_ _ _ _}.

  Definition symPoly {Γ l A A' B B'} (ΠA : PolyRed Γ l A A' B B')
    (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΠA ρ h))
    (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
      (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _]), sym (PolyRed.posRed ΠA ρ h ha))
      : PolyRed Γ l A' A B' B.
  Proof.
    unshelve econstructor.
    * intros; now unshelve eapply symRed, ihdom.
    * intros; (unshelve eapply symRed, ihcod); tea.
      now eapply symRedTm.
  Defined.

  Definition symParamRedTy {T Γ l A A'} (ΠA : ParamRedTy T Γ l A A')
    (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΠA ρ h))
    (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
      (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _]), sym (PolyRed.posRed ΠA ρ h ha))
      : ParamRedTy T Γ l A' A.
  Proof.
    destruct ΠA; cbn in *; unshelve econstructor.
    5,6: eassumption.
    1,2: now symmetry.
    now eapply symPoly.
  Defined.

  Section SymΠ.
    Context {Γ l A A'} (ΠA : [Γ ||-Π<l> A ≅ A'])
      (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΠA ρ h))
      (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
        (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _]), sym (PolyRed.posRed ΠA ρ h ha)).

    Let symΠ := symParamRedTy ΠA ihdom ihcod.

    Definition symIsLRFun {t} : isLRFun ΠA t <≈> isLRFun symΠ t.
    Proof.
      split.
      - intros [???? Rbody|].
        * constructor; tea.
          1: etransitivity; tea; eapply ParamRedTy.eqdom.
          intros; eapply ihcod, Rbody.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
      - intros [???? Rbody|].
        * constructor; tea.
          1: etransitivity; tea; eapply ParamRedTy.eqdom.
          intros ? a b ρ h ha.
          unshelve eapply ihcod, irrLR, Rbody; tea.
          now eapply ihdom.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
    Qed.

    Definition symPiRedTm {t} : PiRedTm ΠA t <≈> PiRedTm symΠ t.
    Proof.
      split; intros [?? ?%symIsLRFun]; econstructor; tea.
      all: eapply redtmwf_conv; tea; apply ParamRedTy.eq.
    Defined.

    Definition symPiRedTmEq {t u} : PiRedTmEq ΠA t u <≈> PiRedTmEq symΠ u t.
    Proof.
      split; intros []; unshelve econstructor; try now eapply symPiRedTm.
      1,3: cbn; eapply convtm_conv; [now symmetry| eapply PiRedTy.eq].
      all: cbn; intros; unshelve eapply ihcod, irrLR, eqApp; tea; now eapply ihdom.
    Qed.

    Definition symLRΠ : sym (LRPi' ΠA).
    Proof. exists (LRPi' symΠ); intros; cbn; split; eapply symPiRedTmEq. Qed.
  End SymΠ.


  Lemma symNe {Γ A B} : [Γ ||-ne A ≅ B] -> [Γ ||-ne B ≅ A].
  Proof.
    intros []; unshelve econstructor.
    3,4: tea.
    now symmetry.
  Defined.

  Lemma symNeNf {Γ t u A} : [Γ ||-NeNf t ≅ u : A] -> [Γ ||-NeNf u ≅ t : A].
  Proof.
    intros []; econstructor; tea; now symmetry.
  Qed.

  Lemma symNatRedTmEq {Γ} :
    (forall t u, NatRedTmEq Γ t u -> NatRedTmEq Γ u t) ×
    (forall t u, NatPropEq Γ t u -> NatPropEq Γ u t).
  Proof.
    eapply NatRedEqInduction.
    - intros; econstructor; tea; now symmetry.
    - constructor.
    - intros; now constructor.
    - intros; constructor; now eapply symNeNf.
  Qed.

  Lemma eq_subst_scons {Γ} a B : B[a..] = B[a⟨@wk_id Γ⟩ .: @wk_id Γ >> tRel].
  Proof. now bsimpl. Qed.


  Section SymΣ.
    Context {Γ l A A'} (ΣA : [Γ ||-Σ<l> A ≅ A'])
      (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΣA ρ h))
      (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
        (ha : [PolyRed.shpRed ΣA ρ h | Δ ||- a ≅ b : _]), sym (PolyRed.posRed ΣA ρ h ha)).

    Let symΣ := symParamRedTy ΣA ihdom ihcod.

    Definition symIsLRPair {t} : isLRPair ΣA t <≈> isLRPair symΣ t.
    Proof.
      split.
      - intros [???????? r1 r2|].
        * unshelve eapply PairLRPair; tea.
          2: etransitivity; tea; eapply ParamRedTy.eqdom.
          + intros; now eapply ihdom.
          + etransitivity; tea; erewrite 2!eq_subst_scons.
            symmetry; eapply escapeEq.
            unshelve eapply PolyRed.posRed, r1; gtyping.
          + intros; (unshelve now eapply ihcod, irrLR); tea.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
      - intros [???????? r1 r2|].
        * unshelve eapply PairLRPair; tea.
          2: etransitivity; tea; eapply ParamRedTy.eqdom.
          + intros; now eapply ihdom.
          + etransitivity; tea; erewrite 2!eq_subst_scons.
            symmetry; eapply escapeEq.
            unshelve eapply PolyRed.posRed, r1; gtyping.
          + intros; (unshelve now eapply ihcod, irrLR); tea.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
    Qed.

    Definition symSigRedTm {t} : SigRedTm ΣA t <≈> SigRedTm symΣ t.
    Proof.
      split; intros [?? ?%symIsLRPair]; econstructor; tea.
      all: eapply redtmwf_conv; tea; apply ParamRedTy.eq.
    Defined.

    Definition symSigRedTmEq {t u} : SigRedTmEq ΣA t u <≈> SigRedTmEq symΣ u t.
    Proof.
      split; intros []; unshelve econstructor; try now eapply symSigRedTm.
      3,5: cbn; eapply convtm_conv; [now symmetry| eapply PiRedTy.eq].
      1,2: cbn; intros; now eapply ihdom.
      all: cbn; intros; unshelve (now eapply ihcod, irrLR); tea.
    Qed.

    Definition symLRΣ : sym (LRSig' ΣA).
    Proof. exists (LRSig' symΣ); intros; cbn; split; eapply symSigRedTmEq. Qed.
  End SymΣ.

  Section SymId.
  Context {Γ l A B} (IA: [Γ ||-Id< l > A ≅ B])
    (ihdom:  sym (IdRedTy.tyRed IA))
    (ihkr: forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]), sym (IdRedTy.tyKripke IA ρ wfΔ)).

  Lemma symId : [Γ ||-Id<l> B ≅ A].
  Proof.
    destruct IA; unshelve econstructor.
    9,10: tea.
    * now eapply ihdom.
    * intros; now eapply ihkr.
    * now symmetry.
    * now eapply ihdom.
    * now eapply ihdom.
    * constructor.
      1: intros ?? ?%ihdom; eapply ihdom; cbn in *; now symmetry.
      intros ??? ?%ihdom ?%ihdom; eapply ihdom; cbn in *; now etransitivity.
    * intros * ? ?%ihkr; eapply ihkr; cbn in *; now eapply tyKripkeTmEq.
  Defined.

  #[local] Instance : PER _ := IA.(IdRedTy.tyPER).
  #[local] Instance : PER _ := symId.(IdRedTy.tyPER).

  Lemma symIdPropEq {t u} : IdPropEq IA t u <≈> IdPropEq symId u t.
  Proof.
    pose proof (escapeEq (IA.(IdRedTy.tyRed))).
    split; intros []; constructor; tea.
    - etransitivity; tea; now symmetry.
    - etransitivity; tea; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.lhsRed]; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.lhsRed]; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.rhsRed]; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.rhsRed]; now symmetry.
    - eapply symNeNf, NeNf.conv_; tea; eapply IdRedTy.eq.
    - etransitivity; tea.
    - etransitivity; tea.
    - eapply ihdom; etransitivity; [|apply symId.(IdRedTy.lhsRed)]; now symmetry.
    - eapply ihdom; etransitivity;[| apply symId.(IdRedTy.lhsRed)]; now symmetry.
    - eapply ihdom; etransitivity;[| apply symId.(IdRedTy.rhsRed)]; now symmetry.
    - eapply ihdom; etransitivity;[| apply symId.(IdRedTy.rhsRed)]; now symmetry.
    - eapply symNeNf, NeNf.conv_; tea; eapply IdRedTy.eq.
  Qed.

  Lemma symIdRedTmEq {t u} : IdRedTmEq IA t u <≈> IdRedTmEq symId u t.
  Proof.
    split; intros [????? ?%symIdPropEq]; econstructor; tea.
    3,6: eapply convtm_conv; [now symmetry|]; eapply IdRedTy.eq.
    all: eapply redtmwf_conv; tea; eapply IdRedTy.eq.
  Qed.

  Lemma symLRId : sym (LRId' IA).
  Proof.
    exists (LRId' symId).
    intros; split; eapply symIdRedTmEq.
  Qed.

  End SymId.


  Theorem symLR_rec {l}
    (ih : forall l', l' << l -> forall {Γ A B} (R : [Γ ||-<l'> A ≅ B]), sym R)
    {Γ A B} (R : [Γ ||-<l> A ≅ B]) : sym R.
  Proof.
    revert ih; indLR R.
    - intros h ih; unshelve econstructor.
      + destruct h; apply LRU_; now unshelve econstructor.
      + cbn; intros ??; split; intros []; cbn in *.
        all: unshelve econstructor; tea;[now symmetry|]; cbn.
        1,2: eapply redTyRecBwd.
        1,2: unshelve eapply symRed, ih, URedTy.lt.
        1,2: now eapply redTyRecFwd.
    - intros h _ ; unshelve econstructor.
      1: now eapply LRne_, symNe.
      + pose proof (convty_term (convtm_convneu UnivPos (neRedTy.eq h))).
        cbn; intros ??; split; intros []; cbn in *.
        all: unshelve econstructor; cbn.
        5,6,8,9: eapply redtmwf_conv;tea; now symmetry.
        1,2: eapply convneu_conv; [now symmetry|]; tea; now symmetry.
    - intros ΠA ihdom ihcod ih.
      eapply symLRΠ.
      all: intros; eauto.
    - intros NA _; unshelve econstructor.
      + eapply LRNat_; destruct NA; now econstructor.
      + intros; cbn; split; eapply symNatRedTmEq.
    - intros EA _; unshelve econstructor.
      + eapply LREmpty_; destruct EA; now econstructor.
      + intro; cbn; split; intros []; econstructor; tea; now eapply symNeNf.
    - intros ΣA ihdom ihcod ih; eapply symLRΣ; intros; eauto.
    - intros IA ihdom ihkr ih; eapply symLRId; eauto.
  Qed.

  (* Universe Issue with ltInd.. should be fixable *)
  (* Theorem symLR : forall {l Γ A B} (R : [Γ ||-<l> A ≅ B]), sym R.
  Proof.  intros l. pattern l. eapply ltInd. intros; eapply symLR_rec; intros; eapply X. eapply (ltInd _ l). refine (ltInd _ (@symLR_rec)). *)

  Theorem symLR0 : forall {Γ A B} (R : [Γ ||-<zero> A ≅ B]), sym R.
  Proof.
    eapply symLR_rec; intros ? h; inversion h.
  Qed.

  Theorem symLR : forall {l Γ  A B} (R : [Γ ||-<l> A ≅ B]), sym R.
  Proof.
    intros []; [intros; eapply symLR0| apply symLR_rec].
    intros ? h; inversion h; intros; eapply symLR0.
  Qed.

End Symmetry.






(** We show a general version of irrelevance, saying that if A and A' are reducible (at levels logical relation levels lA, lA')
and A' is reducibly convertible to A, then the reducibility predicates they decode to are equivalent.
From this, both a simpler version of irrelevance and symmetry follow, by using reflexivity
in the right places. *)
(** Interestingly, we also show irrelevance with respect to universe levels, which is crucial
in later parts of the development, where this avoids creating spurious constraints on universe levels.*)

Lemma subst_wk_id_tail Γ P t : P[t .: @wk_id Γ >> tRel] = P[t..].
Proof. setoid_rewrite id_ren; now bsimpl. Qed.


Section Irrelevances.
Context `{GenericTypingProperties}.

Section EquivLR.
  Universe j k j' k' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record equivLR {kA : RedRel@{j k}} {kA' : RedRel@{j' k'}} {Γ A A'} := {
    lrConvL : forall C, [kA | Γ ||- A ≅ C] <≈> [kA' | Γ ||- A' ≅ C] ;
    lrConvR : forall C, [kA | Γ ||- C ≅ A] <≈> [kA' | Γ ||- C ≅ A'] ;
    lrTmL : forall C C' t u (RA : [kA | Γ ||- A ≅ C]) (RA' : [kA' | Γ ||- A' ≅ C']),
      [RA | _ ||- t ≅ u : _] <≈> [RA' | _ ||- t ≅ u : _] ;
    lrTmR : forall C C' t u (RA : [kA | Γ ||- C ≅ A]) (RA' : [kA' | Γ ||- C' ≅ A']),
      [RA | _ ||- t ≅ u : _] <≈> [RA' | _ ||- t ≅ u : _] ;
  }.

End EquivLR.

Arguments equivLR : clear implicits.

Record implLR@{j k j' k'} {kA : RedRel@{j k}} {kA' : RedRel@{j' k'}} {Γ A A'} := {
    ilrConvL : forall C, [kA | Γ ||- A ≅ C] -> [kA' | Γ ||- A' ≅ C] ;
    ilrConvR : forall C, [kA | Γ ||- C ≅ A] -> [kA' | Γ ||- C ≅ A'] ;
    ilrTmL : forall C C' t u (RA : [kA | Γ ||- A ≅ C]) (RA' : [kA' | Γ ||- A' ≅ C']),
      [RA | _ ||- t ≅ u : _] -> [RA' | _ ||- t ≅ u : _] ;
    ilrTmR : forall C C' t u (RA : [kA | Γ ||- C ≅ A]) (RA' : [kA' | Γ ||- C' ≅ A']),
      [RA | _ ||- t ≅ u : _] -> [RA' | _ ||- t ≅ u : _] ;
}.
Arguments implLR : clear implicits.

Lemma impl_equivLR@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A' :
  implLR@{j k j' k'} kA kA' Γ A A' -> implLR@{j' k' j k} kA' kA Γ A' A ->
  equivLR@{j k j' k' v} kA kA' Γ A A'.
Proof.
  intros [] []; constructor; intros; split; eauto.
Defined.

Lemma equiv_implLR1@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A' :
  equivLR@{j k j' k' v} kA kA' Γ A A' ->
  implLR@{j k j' k'} kA kA' Γ A A'.
Proof.
  intros e; constructor; intros.
  - edestruct e as [[]]; eauto.
  - edestruct e as [? []]; eauto.
  - edestruct e as [?? []]; eauto.
  - edestruct e as [??? []]; eauto.
Defined.

Lemma equiv_implLR2@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A' :
  equivLR@{j k j' k' v} kA kA' Γ A A' ->
  implLR@{j' k' j k} kA' kA Γ A' A.
Proof.
  intros e; constructor; intros.
  - edestruct e as [[]]; eauto.
  - edestruct e as [? []]; eauto.
  - edestruct e as [?? []]; eauto.
  - edestruct e as [??? []]; eauto.
Defined.


Lemma transImplLR@{j k j' k' j'' k''} kA kA' kA'' Γ A A' A''
  (h : implLR@{j k j' k'} kA kA' Γ A A')
  (h' : implLR@{j' k' j'' k''} kA' kA'' Γ A' A'') :
  implLR@{j k j'' k''} kA kA'' Γ A A''.
Proof.
  constructor; intros.
  - do 2 (eapply ilrConvL; tea).
  - do 2 (eapply ilrConvR; tea).
  - unshelve (do 2 (eapply ilrTmL; tea)).
    2: now eapply ilrConvL.
  - unshelve (do 2 (eapply ilrTmR; tea)).
    2: now eapply ilrConvR.
Qed.



Lemma ureflConvEquivLR@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A'
  (RAA' : [kA | Γ ||- A ≅ A'])
  (h : equivLR@{j k j' k' v} kA kA' Γ A A') : [kA' | Γ ||- A' ≅ A'].
Proof. now eapply h.(lrConvL). Qed.

Lemma lreflConvEquivLR@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A'
  (RAA' : [kA | Γ ||- A ≅ A'])
  (h : equivLR@{j k j' k' v} kA' kA Γ A A') : [kA' | Γ ||- A ≅ A].
Proof. now eapply h.(lrConvR). Qed.

Lemma symConvEquivLR@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A'
  (RAA' : [kA | Γ ||- A ≅ A'])
  (h : equivLR@{j k j' k' v} kA kA' Γ A A') :
  [kA | Γ ||- A' ≅ A].
Proof. now eapply h.(lrConvR), ureflConvEquivLR. Qed.

Lemma symConvEquivLR'@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A'
  (RAA' : [kA | Γ ||- A ≅ A'])
  (h : equivLR@{j k j' k' v} kA' kA Γ A A') :
  [kA | Γ ||- A' ≅ A].
Proof. now eapply h.(lrConvL), lreflConvEquivLR. Qed.

Lemma symEquivLR@{j k j' k' v} (kA : RedRel@{j k}) (kA' : RedRel@{j' k'}) Γ A A' :
  equivLR@{j k j' k' v} kA kA' Γ A A' -> equivLR@{j' k' j k v} kA' kA Γ A' A.
Proof.
  intros h. eapply impl_equivLR;
   [now apply equiv_implLR2| now apply equiv_implLR1].
Qed.

Lemma transEquivLR@{j k j' k' j'' k'' v} kA kA' kA'' Γ A A' A''
  (h : equivLR@{j k j' k' v} kA kA' Γ A A')
  (h' : equivLR@{j' k' j'' k'' v} kA' kA'' Γ A' A'') :
  equivLR@{j k j'' k'' v} kA kA'' Γ A A''.
Proof.
  eapply impl_equivLR; eapply transImplLR; first [now eapply equiv_implLR1| now eapply equiv_implLR2].
Qed.

Notation "[ R | Γ ||-≅]" := (fun A B  => [R | Γ ||- A ≅ B]) (R at level 50).


Lemma convEquivLRSym@{j k j' k' v} k k' Γ
  (h : forall A B, [k | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B) :
  Symmetric@{Set v} ([k | Γ ||-≅]).
Proof.
  intros A B RAB; eapply symConvEquivLR; tea; now apply h.
Qed.

Lemma convEquivLRSym'@{j k j' k' v} k k' Γ
  (h : forall A B, [k' | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B) :
  Symmetric@{Set v} ([k' | Γ ||-≅]).
Proof.
  intros A B RAB; eapply symConvEquivLR'; tea; now apply h.
Qed.

Lemma convEquivLRDiag@{j k j' k' v} k k' Γ
  (h : forall A B, [k | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B)
  (h' : forall A B, [k' | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B) :
  forall A B, [k | Γ ||- A ≅ B] -> equivLR@{j k j k v} k k Γ A B.
Proof.
  intros ?? R.
  eapply transEquivLR.
  1: now apply h.
  apply symEquivLR.
  apply h'; eapply ureflConvEquivLR; tea; eauto.
Qed.

Lemma convEquivLRDiag'@{j k j' k' v} k k' Γ
  (h : forall A B, [k | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B)
  (h' : forall A B, [k' | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B) :
  forall A B, [k' | Γ ||- A ≅ B] -> equivLR@{j k j k v} k' k' Γ A B.
Proof.
  pose proof (convEquivLRSym' _ _ _ h').
  intros ?? R. eapply (symmetry (R:=[k' | Γ ||-≅])) in R.
  eapply transEquivLR; eapply symEquivLR.
  1: now eapply h'.
  apply symEquivLR.
  apply h ; eapply lreflConvEquivLR; tea; eauto.
Qed.


Lemma convEquivLRDiagPER@{j k v} k Γ  (h : forall A B, [k | Γ ||- A ≅ B] -> equivLR@{j k j k v} k k Γ A B) :
  PER@{Set v} ([k | Γ ||-≅]).
Proof.
  constructor; [ now eapply convEquivLRSym |].
  intros A B C RAB RBC; now eapply (h _ _ RAB).(lrConvL).
Qed.

Lemma convEquivLRPER@{j k j' k' v} k k' Γ
  (h : forall A B, [k | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B)
  (h' : forall A B, [k' | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B) :
  PER@{Set v} ([k | Γ ||-≅]).
Proof.
  apply convEquivLRDiagPER; now eapply convEquivLRDiag.
Qed.

Lemma convEquivLRPER'@{j k j' k' v} k k' Γ
  (h : forall A B, [k | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B)
  (h' : forall A B, [k' | Γ ||- A ≅ B] -> equivLR@{j k j' k' v} k k' Γ A B) :
  PER@{Set v} ([k' | Γ ||-≅]).
Proof.
  apply convEquivLRDiagPER; now eapply convEquivLRDiag'.
Qed.

(* Lemma equivLR_irrTmL :
    forall C C' t u (RA : [kA | Γ ||- A ≅ C]) (RA' : [kA' | Γ ||- C' ≅ A']),
      [RA | _ ||- t ≅ u : _] <≈> [RA' | _ ||- t ≅ u : _] ; *)


(* Section EquivLR.
  Universe i j k l i' j' k' l' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record equivLR {Γ lA A Γ' lA' A'} := {
    lrConvL : forall C, [LogRel@{i j k l} lA | Γ ||- A ≅ C] <≈> [LogRel@{i' j' k' l'} lA' | Γ' ||- A' ≅ C] ;
    lrConvR : forall C, [LogRel@{i j k l} lA | Γ ||- C ≅ A] <≈> [LogRel@{i' j' k' l'} lA' | Γ' ||- C ≅ A'] ;
    lrTmL : forall C t u (RA : [LogRel@{i j k l} lA | Γ ||- A ≅ C]) (RA' : [LogRel@{i' j' k' l'} lA' | Γ' ||- A' ≅ C]),
      [RA | _ ||- t ≅ u : _] <≈> [RA' | _ ||- t ≅ u : _] ;
    lrTmR : forall C t u (RA : [LogRel@{i j k l} lA | Γ ||- C ≅ A]) (RA' : [LogRel@{i' j' k' l'} lA' | Γ' ||- C ≅ A']),
      [RA | _ ||- t ≅ u : _] <≈> [RA' | _ ||- t ≅ u : _] ;
  }.

End EquivLR.

Arguments equivLR : clear implicits.


Lemma ureflConvEquivLR@{i j k l i' j' k' l' v} Γ lA A Γ' lA' A' (RAA' : [LogRel@{i j k l} lA | Γ ||- A ≅ A'])
  (h : equivLR@{i j k l i' j' k' l' v} Γ lA A Γ' lA' A') : [LogRel@{i j k l} lA' | Γ' ||- A' ≅ A'].
Proof. now eapply h.(lrConvL). Qed.

Lemma symConvEquivLR@{i j k l i' j' k' l' v} Γ lA A Γ' lA' A' (RAA' : [LogRel@{i j k l} lA | Γ ||- A ≅ A'])
  (h : equivLR@{i j k l i' j' k' l' v} Γ lA A Γ' lA' A') : [LogRel@{i j k l} lA | Γ ||- A' ≅ A].
Proof. now eapply h.(lrConvR), ureflConvEquivLR. Qed.

Lemma symEquivLR@{i j k l i' j' k' l' v} Γ lA A Γ' lA' A' (h : equivLR@{i j k l i' j' k' l' v} Γ lA A Γ' lA' A') :
  equivLR@{ i' j' k' l' i j k l v}  Γ' lA' A' Γ lA A.
Proof.
  constructor; intros; split; try first [apply h.(lrConvL)|apply h.(lrConvR)| apply h.(lrTmL)| apply h.(lrTmR)].
Qed.

Lemma transEquivLR@{i j k l i' j' k' l' i'' j'' k'' l'' v} Γ lA A Γ' lA' A' Γ'' lA'' A''
  (h : equivLR@{i j k l i' j' k' l' v} Γ lA A Γ' lA' A')
  (h' : equivLR@{i' j' k' l' i'' j'' k'' l'' v} Γ' lA' A' Γ'' lA'' A'') :
  equivLR@{i j k l i'' j'' k'' l'' v} Γ lA A Γ'' lA'' A''.
Proof.
  constructor; intros; split; intros;
    try first [eapply h.(lrConvL)|eapply h.(lrConvR)| eapply h.(lrTmL)| eapply h.(lrTmR)];
    try first [eapply h'.(lrConvL)|eapply h'.(lrConvR)| eapply h'.(lrTmL)| eapply h'.(lrTmR)]; tea;
    try first [eapply h.(lrConvL)|eapply h.(lrConvR)| eapply h.(lrTmL)| eapply h.(lrTmR)]; tea.
    Unshelve. all: now first [eapply h.(lrConvL)|eapply h.(lrConvR)].
Qed.

Lemma convEquivLRPER@{i j k l v} Γ l  (h : forall A B, [LogRel@{i j k l} l | Γ ||- A ≅ B] -> equivLR@{i j k l i j k l v} Γ l A Γ l B) :
  PER@{Set l} (fun A B => [LogRel@{i j k l} l | Γ ||- A ≅ B]).
Proof.
  constructor.
  - intros A B RAB; eapply symConvEquivLR; tea; now apply h.
  - intros A B C RAB RBC; now eapply (h _ _ RAB).(lrConvL).
Qed. *)

Section NeIrrelevance.
Import neRedTy.

#[local]
Instance nePER {Γ} : PER (neRedTy Γ).
Proof.
  constructor.
  - intros ?? []; econstructor; tea; now symmetry.
  - intros ??? Rxy Ryz.
    pose proof (whredty_det _ _ (whredR Rxy) (whredL Ryz)).
    destruct Rxy, Ryz; cbn in *; subst; econstructor; tea; now etransitivity.
Qed.

#[local]
Instance neTmPER@{k} {Γ A B} (h : [Γ ||-ne A ≅ B]) : PER@{Set k} (fun t u=> neRedTmEq t u h).
Proof.
  constructor.
  - intros ?? []; econstructor; tea; now symmetry.
  - intros ??? Rxy Ryz.
    pose proof (whredtm_det _ _ _ _ (neRedTmEq.whredR Rxy) (neRedTmEq.whredL Ryz)).
    destruct Rxy, Ryz; cbn in *; subst; econstructor; tea; now etransitivity.
Qed.


Lemma neIrrelevanceImpl {Γ lA lB A B} : [Γ ||-ne A ≅ B] -> implLR (LogRel lA) (LogRel lB) Γ A B.
Proof.
  intros Rne; pose (RlA:= LRne_ lA Rne).
  (* ; pose (RlB:= LRne_ lB (symmetry Rne)). *)
  constructor.
  - intros ? R ; pose proof (invLREqL_whred RlA R) as []; subst.
    apply LRne_; etransitivity; tea; now symmetry.
  - intros ? R ; pose proof (invLREqR_whred RlA R) as [] ; subst.
    apply LRne_; now etransitivity.
  - intros ???? RA RB.
    pose proof (invLREqBothL_whred RlA RA RB) as [[RAne [->]] [RBne [->]]]; cbn in *.
    assert ([Γ |- RAne.(tyL) ≅ RBne.(tyL)]).
    1:{
      replace RAne.(tyL) with Rne.(tyL); tea.
      replace RBne.(tyL) with Rne.(tyR); tea.
      destruct Rne; gtyping.
    }
    cbn; intros []; cbn; econstructor.
    1,2: eapply redtmwf_conv; tea.
    now eapply convneu_conv.
  - intros ???? RA RB.
    pose proof (invLREqBothR_whred RlA RA RB) as [[RAne [-> ?]] [RBne [-> ?]]].
    assert ([Γ |- RAne.(tyL) ≅ RBne.(tyL)]).
    1:{
      destruct RAne, RBne, Rne; cbn in *; subst.
      eapply convty_term, convtm_convneu.
      1: constructor.
      do 2 (etransitivity; tea); now symmetry.
    }
    cbn; intros []; cbn; econstructor.
    1,2: eapply redtmwf_conv; tea.
    now eapply convneu_conv.
Qed.

Lemma neIrrelevance {Γ lA lB A B} (h : [Γ ||-ne A ≅ B]) :
  equivLR (LogRel lA) (LogRel lB) Γ A B.
Proof.
  eapply impl_equivLR; eapply neIrrelevanceImpl; tea; now symmetry.
Qed.

End NeIrrelevance.



Section LRIrrelevant.
Universe (*u *) v.
(** u is a small universe level that may be instanciated to Set. v is a large universe level *)

Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

Section LRIrrelevantInductionStep.

Universe i j k l i' j' k' l'.


#[local]
Definition IHStatement lA lA' :=
  forall l0 (ltA : l0 << lA) (ltA' : l0 << lA') Γ,
    (forall A B, [LogRelRec@{i j k} lA l0 ltA | Γ ||- A ≅ B] ->
      equivLR@{j k j' k' v} (LogRelRec@{i j k} lA l0 ltA) (LogRelRec@{i' j' k'} lA' l0 ltA') Γ A B)
    × (forall A B, [LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- A ≅ B] ->
      equivLR@{j k j' k' v} (LogRelRec@{i j k} lA l0 ltA) (LogRelRec@{i' j' k'} lA' l0 ltA')  Γ A B).

(* Lemma eqTmUPER {Γ A B lA lA'} (h: [Γ ||-U< lA > A ≅ B]) : IHStatement lA lA' ->
  PER (fun t u : term => [LogRelRec lA | Γ ||-U t ≅ u : A ≅ B | h]).
Proof.
  destruct h as [l0 ltA]. cbn.
  intros. split.
  - intros ?? []; cbn in *. *)


Definition IHCoroL {lA lA'} : IHStatement lA lA' ->
  forall l0 (ltA : l0 << lA) (ltA' : l0 << lA') Γ A B,
    [LogRelRec@{i j k} lA l0 ltA | Γ ||- A ≅ B] ->
    equivLR@{j k j' k' v} (LogRelRec@{i j k} lA l0 ltA) (LogRelRec@{i' j' k'} lA' l0 ltA')  Γ A A.
Proof.
  intros ih l0 ltA ltA' Γ ?? RAB; specialize (ih l0 ltA ltA' Γ) as [e e'].
  pose proof (convEquivLRPER _ _ _ e e').
  apply e.
  eapply (transitivity (R:=[LogRelRec@{i j k} lA l0 ltA|Γ||-≅])).
  2: eapply (symmetry (R:=[LogRelRec@{i j k} lA l0 ltA|Γ||-≅])).
  all: tea.
Qed.

Definition IHCoroR {lA lA'} : IHStatement lA lA' ->
  forall l0 (ltA : l0 << lA) (ltA' : l0 << lA') Γ A B,
    [LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- A ≅ B] ->
    equivLR@{j k j' k' v} (LogRelRec@{i j k} lA l0 ltA) (LogRelRec@{i' j' k'} lA' l0 ltA')  Γ A A.
Proof.
  intros ih l0 ltA ltA' Γ ?? RAB; specialize (ih l0 ltA ltA' Γ) as [e e'].
  pose proof (convEquivLRPER' _ _ _ e e').
  apply e'.
  eapply (transitivity (R:=[LogRelRec@{i' j' k'} lA' l0 ltA'|Γ||-≅])).
  2: eapply (symmetry (R:=[LogRelRec@{i' j' k'} lA' l0 ltA'|Γ||-≅])).
  all: tea.
Qed.


#[local]
Lemma UnivIrrelevanceLRPack
  {Γ lA lB A A' B B'}
  (IH : IHStatement lA lB)
  (hUA : [Γ ||-U<lA> A ≅ A'])
  (hUB : [Γ ||-U<lB> B ≅ B'])
  (hAB : [Γ ||-U<lA> A ≅ B])
  : equivLR@{k l k' l' v} (LogRel@{i j k l} lA) (LogRel@{i' j' k' l'} lB) Γ A B
    × PER (fun t u : term => [LogRelRec lA | Γ ||-U t ≅ u : A ≅ B | hAB]).
Proof.
  pose (RA := LRU_ hUA).
  pose (RB := LRU_ hUB).
  pose proof (level_unique hUA hUB hAB).
  pose proof (level_unique hAB hUB hAB).
  destruct hUA as [? ltA], hUB as [? ltB]; cbn in *; subst.
  split; [constructor|].
  + intros; split; intros lr.
    all: (destruct (invLR_whred RA lr) + destruct (invLR_whred RB lr)).
    all: apply LRU_; subst; now econstructor.
  + intros; split; intros lr.
    all: (destruct (invLRr_whred RA lr) + destruct (invLRr_whred RB lr)).
    all: apply LRU_; now econstructor.
  + intros ?? T U RA' RB'.
    pose proof (invLREqL_whred RA RA') as [hA']; subst.
    pose proof (invLREqL_whred RB RB') as [hB']; subst.
    pose proof (h := level_unique hA' hB' hAB); destruct hA' as [? lt1], hB' as [l1 lt2].
    cbn in *; subst; split; intros []; unshelve econstructor; cbn in *; tea.
    1: now apply (IHCoroL IH l1 lt1 lt2 Γ T U relEq).
    now apply (IHCoroR IH l1 lt1 lt2 Γ T U relEq).
  + intros ?? T U RA' RB'.
    pose proof (invLREqR_whred RA RA') as [hA']; subst.
    pose proof (invLREqR_whred RB RB') as [hB']; subst.
    pose proof (h := level_unique' hA' hB' hAB); destruct hA' as [? lt1], hB' as [l1 lt2].
    cbn in *; subst; split; intros []; unshelve econstructor; cbn in *; tea.
    1: now apply (IHCoroL IH l1 lt1 lt2 Γ T U relEq).
    now apply (IHCoroR IH l1 lt1 lt2 Γ T U relEq).
  + specialize (IH _ (URedTy.lt hAB) ltB Γ) as [e e'].
    pose proof (convEquivLRPER _ _ _ e e').
    constructor.
    * intros ?? []; econstructor.
      1: now symmetry.
      now eapply (@symmetry _ _ X.(PER_Symmetric)).
    * intros ??? [? redR1] [redL2 ]; econstructor.
      1: etransitivity; tea.
      epose proof (h := whredtm_det _ _ _ _ (URedTm.whred redR1) (URedTm.whred redL2)).
      now replace (URedTm.te redR1) with (URedTm.te redL2) by (symmetry ; apply h).
      now eapply (@transitivity _ _ X.(PER_Transitive)).
Qed.

(** ** The main theorem *)

#[local]
Lemma LRconvEquiv {lA lB}
  (IH : IHStatement lA lB)
  (Γ : context) (A A' B B' : term)
  (RA : [LogRel@{i j k l} lA | Γ ||- A ≅ A'])
  (RB : [LogRel@{i' j' k' l'} lB | Γ ||- B ≅ B'])
  (* {l} *)
  (RAB : [LogRel@{i j k l} lA | Γ ||- A ≅ B]) :
  (* (l = lA \/ l = lB) -> *)
  equivLR (LogRel@{i j k l} lA) (LogRel@{i' j' k' l'} lB) Γ A B × PER (RAB.(LRPack.eqTm)).
Proof.
  revert (*lA*) lB A' RA B' RB IH; indLR RAB.
  - intros; eapply UnivIrrelevanceLRPack; tea.
    (* + unshelve eapply (invLR RA _ (whredR (LRU_ h))); cbn; destruct h; gtyping. *)
    + unshelve eapply (invLR RB _ (whredR (LRU_ h))); cbn; destruct h; gtyping.
  - intros neA **; split.
    + now eapply neIrrelevance.
    + now eapply neTmPER.
  - intros ΠA ihdom ihcod **.
    pose (R0 := LRPi' ΠA).
    pose proof (invLREqBothL_whred R0 RA RB) as [[hA' []] [hB' []]]; subst; cbn in *.
    unshelve epose proof (ihdom' := fun Δ ρ h => ihdom Δ ρ h (*lA*) lB (ParamRedTy.domR hA')⟨ρ⟩ _ (ParamRedTy.domR hB')⟨ρ⟩ _ IH).
    1: rewrite <-e0; now eapply hA'.(PolyRed.shpRed).
    1: rewrite <-e3; now eapply hB'.(PolyRed.shpRed).
    unshelve epose proof (ihcod' := fun Δ a b ρ h Rab => ihcod Δ a b ρ h Rab (*lA*) lB (ParamRedTy.codR hA')[b .: ρ >> tRel] _ (ParamRedTy.codR hB')[b .: ρ >> tRel] _ IH).
    1:{
      rewrite <-e1; unshelve eapply hA'.(PolyRed.posRed); tea.
      set (PolyRed.shpRed ΠA ρ h) in Rab.
      set (PolyRed.shpRed hA' ρ h).
      pose proof (e':= fst (ihdom' _ ρ h)).
      pose proof (e := fst (ihdom' _ ρ h)).
      rewrite <- e0 in e'.
      unshelve eapply e'.(lrTmL).
      2: now eapply e.(lrConvL).
      eapply e.(lrTmL).
      exact Rab.
    }
    1:{
      rewrite <-e4; unshelve eapply hB'.(PolyRed.posRed); tea.
      set (PolyRed.shpRed ΠA ρ h) in Rab.
      set (PolyRed.shpRed hB' ρ h).
      destruct (ihdom' _ ρ h) as [e domPER].
      pose proof (e':= fst (ihdom' _ ρ h)).
      rewrite <- e3 in e'.
      unshelve eapply e'.(lrTmL).
      2: eassumption.
      unshelve eapply urefl. 2: eassumption.
    }
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

#[local]
Lemma IrrRec0 : IHStatement zero zero.
Proof.
  intros ? ltA; inversion ltA.
Qed.

(** Safety check: we did not add constraints we did not mean to *)
Fail Fail Constraint i < i'.
Fail Fail Constraint i' < i.
Fail Fail Constraint j < j'.
Fail Fail Constraint j' < j.
Fail Fail Constraint k < k'.
Fail Fail Constraint k' < k.
Fail Fail Constraint l < l'.
Fail Fail Constraint l' < l.

End LRIrrelevantInductionStep.


#[local]
Theorem IrrRec@{i j k l i' j' k' l' v} {lA} {lA'} :
  IHStatement@{i j k l i' j' k' l' v} lA lA'.
Proof.
  intros l0 ltA ltA'.
  destruct ltA. destruct ltA'. cbn in *; intros.
  split; intros ?? R; unshelve eapply (fst (LRconvEquiv IrrRec0 Γ A _ B A R _ R)).
  - intros. eapply
  - intros Γ t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' k' u i j k}).
  - intros Γ t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'} Γ t t
                (lr1 : LRPackAdequate (LogRel@{u i j k} zero) lr1)
                (lr2 : LRPackAdequate (LogRel@{u i' j' k'} zero) lr2)
                (reflLRTyEq lr1)) as [tyEq _].
    exact (tyEq u).
Qed.




#[local]
Lemma LRIrrelevantPreds {lA lB}
  (IH : IHStatement lA lB)
  (Γ : context) (A A' B B' : term)
  (* (RA : [LogRel@{i j k l} lA | Γ ||- A ≅ A']) *)
  (RB : [LogRel@{i' j' k' l'} lB | Γ ||- B ≅ B']) :
  [LogRel@{i j k l} lA | Γ ||- A ≅ B] ->
  equivLR (LogRel@{i j k l} lA) (LogRel@{i' j' k' l'} lB) Γ A B.
Proof.
  intros RAB; revert lB IH A' B' RB; indLR RAB.
  - intros; eapply UnivIrrelevanceLRPack; tea.
    unshelve eapply (invLR RB _ (whredR (LRU_ h))); gtyping.
  - intros neA **; constructor; intros; split.
















(* Definition localConvL@{i j k l} Γ lA A (X Y : sigT@{Set l} (fun (C : term) => [LogRel@{i j k l} lA | Γ ||- A ≅ C])) : Type@{l} :=
  [LogRel@{i j k l} lA | Γ ||- projT1@{Set l} X ≅ projT1@{Set l} Y]. *)

(* Lemma convEquivLRPer@{i j k l i' j' k' l' v} Γ lA A A' (h : equivLR@{i j k l i' j' k' l' v} Γ lA A Γ lA A') : PER@{l l} (localConvL@{i j k l} Γ lA A).
Proof.
  constructor.
  - intros [x ax] [y ay] xy. *)

(** *** Equivalences of LRPack *)

Section EquivLRPack.
  Universe i i' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Definition equivLRPack {Γ Γ' A A'} (P: LRPack@{i} Γ A) (P': LRPack@{i'} Γ' A'):=
    prod@{v v}
      (forall B, [P | Γ ||- A ≅ B] <≈> [P' | Γ' ||- A' ≅ B])
      (* (forall t, [P | Γ ||- t : A] <≈> [P' | Γ' ||- t : A']) *)
      (forall t u, [P | Γ ||- t ≅ u : A] <≈> [P' | Γ' ||- t ≅ u : A']).
End EquivLRPack.

Lemma symLRPack@{i i' v} {Γ Γ' A A'} {P: LRPack@{i} Γ A} {P': LRPack@{i'} Γ' A'} :
    equivLRPack@{i i' v} P P' -> equivLRPack@{i' i v} P' P.
Proof.
  intros [eqT eqTm]; constructor;split ; apply eqT + apply eqTm.
Qed.


Record equivPolyRed@{i j k l i' j' k' l' v}
  {Γ l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} Γ l shp pos}
  {PA' : PolyRed@{i' j' k' l'} Γ l' shp' pos'} :=
  {
    eqvShp : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ]),
          equivLRPack@{k k' v} (PolyRed.shpRed PA ρ wfΔ) (PolyRed.shpRed PA' ρ wfΔ) ;
    eqvPos : forall {Δ a b} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ])
          (ha : [PolyRed.shpRed PA ρ wfΔ| Δ ||- a ≅ b : _])
          (ha' : [PolyRed.shpRed PA' ρ wfΔ | Δ ||- a ≅ b : _]),
          equivLRPack@{k k' v}
            (PolyRed.posRed PA ρ wfΔ ha)
            (PolyRed.posRed PA' ρ wfΔ ha')
  }.

Arguments equivPolyRed : clear implicits.
Arguments equivPolyRed {_ _ _ _ _ _ _} _ _.

Lemma equivPolyRedSym@{i j k l i' j' k' l' v}
  {Γ l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} Γ l shp pos}
  {PA' : PolyRed@{i' j' k' l'} Γ l' shp' pos'} :
  equivPolyRed@{i j k l i' j' k' l' v} PA PA' ->
  equivPolyRed@{i' j' k' l' i j k l v} PA' PA.
Proof.
  intros eqv; unshelve econstructor; intros.
  - eapply symLRPack; eapply eqv.(eqvShp).
  - eapply symLRPack; eapply eqv.(eqvPos).
Qed.

(** *** Lemmas for product types *)

(** A difficulty is that we need to show the equivalence right away, rather than only an implication,
because of contravariance in the case of Π types. To save up work, we factor out some lemmas to
avoid having to basically duplicate their proofs. *)

Section ΠIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {Γ lA A lA' A'}
  (ΠA : ParamRedTy@{i j k l} tProd Γ lA A)
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd Γ lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom)])
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy)])
  (eqv : equivPolyRed ΠA ΠA').

Lemma ΠIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros  [????? []] ; cbn in *; econstructor; [| | |econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΠA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros; now apply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos).
    2: eauto.
    now eapply eqv.(eqvShp).
Qed.

Lemma ΠIrrelevanceTm t : PiRedTm ΠA t -> PiRedTm ΠA' t.
Proof.
  intros []; cbn in *; econstructor; tea.
  - now eapply redtmwf_conv.
  - destruct isfun as [A₀ t₀|n Hn].
    + constructor; tea.
      * etransitivity; tea; now symmetry.
      * intros; unshelve eapply eqv.(eqvPos); [|eauto].
        now apply eqv.(eqvShp).
    + constructor; now eapply convneu_conv.
Defined.

Lemma ΠIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΠIrrelevanceTm.
  - now eapply convtm_conv.
  - unfold PiRedTmEq.appRed in *; intros; unshelve eapply eqv.(eqvPos).
    2: now auto.
    now apply eqv.(eqvShp).
Qed.

End ΠIrrelevanceLemmas.

Lemma ΠIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'}
  (ΠA : ParamRedTy@{i j k l} tProd Γ lA A)
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd Γ lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom)])
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy) ])
  (eqv : equivPolyRed ΠA ΠA')
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (equivPolyRedSym eqv).
  constructor.
  - split; now apply ΠIrrelevanceTyEq.
  - split; now apply ΠIrrelevanceTmEq.
Qed.


(** *** Lemmas for dependent sum types *)

Section ΣIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {Γ lA A lA' A'}
  (ΣA : ParamRedTy@{i j k l} tSig Γ lA A)
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig Γ lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom)])
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy)])
  (eqv : equivPolyRed ΣA ΣA').

Lemma ΣIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros  [????? []] ; cbn in *; econstructor; [| | |econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΣA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros; now apply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos).
    2: eauto.
    now eapply eqv.(eqvShp).
Qed.

Lemma ΣIrrelevanceTm t : SigRedTm ΣA t -> SigRedTm ΣA' t.
Proof.
  intros []; cbn in *; unshelve econstructor; tea.
  - now eapply redtmwf_conv.
  - destruct ispair as [A₀ B₀ a b|n Hn].
    + unshelve econstructor; tea.
      2,3: etransitivity; tea;  symmetry; tea.
      * intros; now unshelve eapply eqv.(eqvShp).
      * assert (wfΓ : [|-Γ]) by gen_typing.
        pose proof (h := rfst Γ wk_id wfΓ).
        rewrite wk_id_ren_on in h.
        pose proof (h' := ΣA.(PolyRed.posExt) _ _ h).
        eapply eqv.(eqvPos), escapeEq in h'.
        rewrite 2!subst_wk_id_tail in h'.
        now symmetry.
        Unshelve. now eapply eqv.(eqvShp).
      (* * etransitivity; tea; now symmetry. *)
      (* * intros; now eapply eqv.(eqvShp). *)
      (* * intros; unshelve eapply eqv.(eqvPos); [|now eauto].
        now unshelve eapply eqv.(eqvShp). *)
      * intros; now eapply eqv.(eqvPos).
    + constructor; now eapply convneu_conv.
Defined.

Lemma ΣIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΣIrrelevanceTm.
  - intros; unshelve eapply eqv.(eqvShp); auto.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqv.(eqvPos); auto.
Qed.

End ΣIrrelevanceLemmas.

Lemma ΣIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'}
  (ΣA : ParamRedTy@{i j k l} tSig Γ lA A)
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig Γ lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom)])
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy) ])
  (eqv : equivPolyRed ΣA ΣA')
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (equivPolyRedSym eqv).
  constructor.
  - split; now apply ΣIrrelevanceTyEq.
  - split; now apply ΣIrrelevanceTmEq.
Qed.

(** *** Lemmas for conversion of reducible neutral terms at arbitrary types *)

Lemma NeNfEqconv {Γ k k' A A'} : [Γ |- A'] -> [Γ |- A ≅ A'] -> [Γ ||-NeNf k ≅ k' : A] -> [Γ ||-NeNf k ≅ k' : A'].
Proof.
  intros ?? []; econstructor; tea; gen_typing.
Qed.

(** *** Irrelevance for Identity types *)

Section IdIrrelevance.
  Universe i j k l i' j' k' l' v.
  Context {Γ lA A lA' A'}
    (IA : IdRedTy@{i j k l} Γ lA A)
    (IA' : IdRedTy@{i' j' k' l'} Γ lA' A')
    (RA := LRId' IA)
    (RA' := LRId' IA')
    (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy)])
    (eqv : equivLRPack@{k k' v} IA.(IdRedTy.tyRed) IA'.(IdRedTy.tyRed))
    (eqty : [Γ |- IA.(IdRedTy.ty) ≅  IA'.(IdRedTy.ty)])
    (lhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.lhs) ≅  IA'.(IdRedTy.lhs) : _ ])
    (rhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.rhs) ≅  IA'.(IdRedTy.rhs) : _]).

  Let APer := IA.(IdRedTy.tyPER).
  #[local]
  Existing Instance APer.

  Lemma IdIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
  Proof.
    intros  [????] ; cbn in *; econstructor; tea; try now apply eqv.
    - etransitivity; tea; now symmetry.
    - apply eqv; etransitivity; tea; now symmetry.
    - apply eqv; etransitivity; tea; now symmetry.
  Qed.

  Lemma IdIrrelevancePropEq t u : IdPropEq IA t u -> IdPropEq IA' t u.
  Proof.
    intros []; constructor ; tea; cycle -1.
    1: eapply NeNfEqconv; tea; unfold_id_outTy ; destruct IA'; escape; cbn in *; gen_typing.
    1,2: etransitivity; tea; now symmetry.
    all: try (apply eqv; tea).
    all: etransitivity; [now symmetry|]; tea.
  Qed.

  Lemma IdIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
  Proof.
    intros []; cbn in *; unshelve econstructor; unfold_id_outTy.
    3,4: now eapply redtmwf_conv.
    - now eapply convtm_conv.
    - now eapply IdIrrelevancePropEq.
  Qed.

End IdIrrelevance.

Lemma IdIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'}
  (IA : IdRedTy@{i j k l} Γ lA A)
  (IA' : IdRedTy@{i' j' k' l'} Γ lA' A')
  (RA := LRId' IA)
  (RA' := LRId' IA')
  (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy)])
  (eqv : equivLRPack@{k k' v} IA.(IdRedTy.tyRed) IA'.(IdRedTy.tyRed))
  (tyconv : [IA.(IdRedTy.tyRed) | _ ||- IA.(IdRedTy.ty) ≅ IA'.(IdRedTy.ty)])
  (lhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.lhs) ≅  IA'.(IdRedTy.lhs) : _ ])
  (rhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.rhs) ≅  IA'.(IdRedTy.rhs) : _])
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (IA.(IdRedTy.tyPER)).
  pose proof (symLRPack eqv).
  assert (eqId' : [Γ |- IA'.(IdRedTy.outTy) ≅ IA.(IdRedTy.outTy)]) by now symmetry.
  assert [Γ |- IA.(IdRedTy.ty) ≅ IA'.(IdRedTy.ty)] by now eapply escapeEq.
  assert [Γ |- IA'.(IdRedTy.ty) ≅ IA.(IdRedTy.ty)] by now symmetry.
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.lhs) ≅  IA.(IdRedTy.lhs) : _ ] by (apply eqv; now symmetry).
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.rhs) ≅  IA.(IdRedTy.rhs) : _ ] by (apply eqv; now symmetry).
  constructor.
  - split; now apply IdIrrelevanceTyEq.
  - split; now apply IdIrrelevanceTmEq.
Qed.

(** *** Irrelevance for neutral types *)

Lemma NeIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ A A'} lA lA'
  (neA : [Γ ||-ne A])
  (neA' : [Γ ||-ne A'])
  (RA := LRne_@{i j k l} lA neA)
  (RA' := LRne_@{i' j' k' l'} lA' neA')
  (eqAA' : [Γ ||-ne A ≅ A' | neA ])
  : equivLRPack@{k k' v} RA RA'.
Proof.
  destruct neA as [ty], neA' as [ty'], eqAA' as [ty0']; cbn in *.
  assert (ty0' = ty'); [|subst].
  { eapply redtywf_det; tea; constructor; eapply convneu_whne; first [eassumption|symmetry; eassumption]. }
  assert [Γ |- ty ≅ ty'] as convty by gen_typing.
  split.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    all: etransitivity ; [| tea]; tea; now symmetry.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    1,2,4,5: now eapply redtmwf_conv.
    all: now eapply convneu_conv; first [eassumption|symmetry; eassumption|gen_typing].
Qed.



Section NatIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {Γ lA lA' A A'} (NA : [Γ ||-Nat A]) (NA' : [Γ ||-Nat A'])
    (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA').

  Lemma NatIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma NatIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'])
    × (forall t u, NatPropEq NA t u -> NatPropEq NA' t u).
  Proof.
    apply NatRedEqInduction; now econstructor.
  Qed.
End NatIrrelevant.

Lemma NatIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA lA' A A'} (NA : [Γ ||-Nat A]) (NA' : [Γ ||-Nat A'])
  (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply NatIrrelevanceTyEq.
  - split; apply NatIrrelevanceTmEq.
Qed.

Section EmptyIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {Γ lA lA' A A'} (NA : [Γ ||-Empty A]) (NA' : [Γ ||-Empty A'])
    (RA := LREmpty_@{i j k l} lA NA) (RA' := LREmpty_@{i' j' k' l'} lA' NA').

  Lemma EmptyIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma EmptyIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA']).
  Proof.
    intros t u Htu. induction Htu. now econstructor.
  Qed.
End EmptyIrrelevant.

Lemma EmptyIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA lA' A A'} (NA : [Γ ||-Empty A]) (NA' : [Γ ||-Empty A'])
  (RA := LREmpty_@{i j k l} lA NA) (RA' := LREmpty_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply EmptyIrrelevanceTyEq.
  - split; apply EmptyIrrelevanceTmEq.
Qed.

(** The main proof *)

Section LRIrrelevant.
Universe u v.
(** u is a small universe level that may be instanciated to Set. v is a large universe level *)

Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

Section LRIrrelevantInductionStep.

Universe i j k l i' j' k' l'.

#[local]
Definition IHStatement lA lA' :=
  (forall l0 (ltA : l0 << lA) (ltA' : l0 << lA'),
      prod@{v v}
        (forall Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
        (forall Γ t
           (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ])
           (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
           u,
            [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ] <≈>
            [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ≅ u | lr2 ])).



#[local]
Lemma UnivIrrelevanceLRPack
  {Γ lA lA' A A'}
  (IH : IHStatement lA lA')
  (hU : [Γ ||-U<lA> A]) (hU' : [Γ ||-U<lA'> A'])
  (RA := LRU_@{i j k l} hU) (RA' := LRU_@{i' j' k' l'} hU') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  revert IH; destruct hU as [_ []], hU' as [_ []]; intro IH; destruct (IH zero Oi Oi) as [IHty IHeq].
  constructor.
  + intros; cbn; split; intros []; now constructor.

  + cbn ; intros ? ?;
    destruct (IHty Γ t) as [tfwd tbwd];
    destruct (IHty Γ u) as [ufwd ubwd].
    split; intros [[] []]; cbn in *; unshelve econstructor.
    3: apply tfwd; assumption.
    5: apply tbwd; assumption.
    6: apply ufwd; assumption.
    8: apply ubwd; assumption.
    all: cbn.
    6: refine (fst (IHeq _ _ _ _ _) _); eassumption.
    7: refine (snd (IHeq _ _ _ _ _) _); eassumption.
    (* Regression here: now/eassumption adds universe constraints that we do not want to accept but can't prevent *)
    1-4:econstructor; cycle -1; [|tea..]; tea.
    all: cbn; tea.
Qed.


(** ** The main theorem *)

#[local]
Lemma LRIrrelevantPreds {lA lA'}
  (IH : IHStatement lA lA')
  (Γ : context) (A A' : term)
  {eqTyA : term -> Type@{k}}
  {eqTyA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ A eqTyA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ A' eqTyA' eqTmA')
  (RA := Build_LRPack Γ A eqTyA eqTmA)
  (RA' := Build_LRPack Γ A' eqTyA'  eqTmA') :
  eqTyA A' ->
  equivLRPack@{k k' v} RA RA'.
Proof.
  intros he.
  set (s := ShapeViewConv lrA lrA' he).
  induction lrA as [? ? h1 | ? ? neA | ? A ΠA HAad IHdom IHcod | ?? NA | ?? NA|? A ΠA HAad IHdom IHcod | ?? IAP IAad IHPar]
    in RA, A', RA', eqTyA', eqTmA', lrA', he, s |- *.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now apply UnivIrrelevanceLRPack.
  - destruct lrA'  ; try solve [destruct s] ; clear s.
    now unshelve eapply NeIrrelevanceLRPack.
  - destruct lrA' as [| | ? A' ΠA' HAad'| | | |] ; try solve [destruct s] ; clear s.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codRed]], ΠA' as [dom1 cod1];
    assert (tProd dom0 cod0 = tProd dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    eapply (ΠIrrelevanceLRPack PA PA'); [| |unshelve econstructor].
    + eassumption.
    + eassumption.
    + intros; unshelve eapply IHdom.
      2: eapply (LRAd.adequate (PolyRed.shpRed PA' _ _)).
      eapply domRed.
    + intros. unshelve eapply IHcod.
      2: eapply (LRAd.adequate (PolyRed.posRed PA' _ _ _)).
      eapply codRed.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now unshelve eapply NatIrrelevanceLRPack.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now unshelve eapply EmptyIrrelevanceLRPack.
  - destruct lrA' as [| | | | |? A' ΠA' HAad'|] ; try solve [destruct s] ; clear s.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codRed]], ΠA' as [dom1 cod1];
    assert (tSig dom0 cod0 = tSig dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    eapply (ΣIrrelevanceLRPack PA PA'); [| |unshelve econstructor].
    + eassumption.
    + eassumption.
    + intros; unshelve eapply IHdom.
      2: eapply (LRAd.adequate (PolyRed.shpRed PA' _ _)).
      eapply domRed.
    + intros; unshelve eapply IHcod.
      2: eapply (LRAd.adequate (PolyRed.posRed PA' _ _ _)).
      eapply codRed.
  - destruct lrA' as [| | | | | | ? A' IAP' IAad'] ; try solve [destruct s] ; clear s.
    pose (IA := IdRedTy.from IAad); pose (IA' := IdRedTy.from IAad').
    assert (IA'.(IdRedTy.outTy) = he.(IdRedTyEq.outTy)) as eId.
    1: eapply whredty_det; constructor; try constructor; [apply IA'.(IdRedTy.red)| apply he.(IdRedTyEq.red)].
    inversion eId; destruct he, IAP'; cbn in *. subst; clear eId.
    eapply (IdIrrelevanceLRPack IA IA'); tea.
    eapply IHPar; tea.
    apply IA'.(IdRedTy.tyRed).
    (* unshelve eapply escapeEq.  2: apply IdRedTy.tyRed.  now cbn. *)
Qed.


#[local]
Lemma LRIrrelevantCumPolyRed {lA}
  (IH : IHStatement lA lA)
  (Γ : context) (shp pos : term)
  (PA : PolyRed@{i j k l} Γ lA shp pos)
  (IHshp : forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] -> [Δ ||-< lA > shp⟨ρ⟩])
  (IHpos : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
          [PolyRed.shpRed PA ρ h | _ ||- a ≅ b : _] ->
          [Δ ||-< lA > pos[a .: ρ >> tRel]]) :
  PolyRed@{i' j' k' l'} Γ lA shp pos.
Proof.
  unshelve econstructor.
  + exact IHshp.
  + intros Δ a b ρ tΔ ra. eapply IHpos.
    pose (shpRed := PA.(PolyRed.shpRed) ρ tΔ).
    destruct (LRIrrelevantPreds IH _ _ _
             (LRAd.adequate shpRed)
             (LRAd.adequate (IHshp Δ ρ tΔ))
             (reflLRTyEq shpRed)) as [_ irrTmEq].
    now eapply (snd (irrTmEq a b)).
  + now destruct PA.
  + now destruct PA.
  + cbn. intros Δ a b ρ tΔ rab.
    set (p := LRIrrelevantPreds _ _ _ _ _ _ _).
    destruct p as [_ irrTmEq].
    pose (ra' := snd (irrTmEq a b) rab).
    pose (posRed := PA.(PolyRed.posRed) ρ tΔ ra').
    destruct (LRIrrelevantPreds IH _ _ _
                (LRAd.adequate posRed)
                (LRAd.adequate (IHpos Δ a b ρ tΔ ra'))
                (reflLRTyEq posRed)) as [irrTyEq _].
    eapply (fst (irrTyEq (pos[b .: ρ >> tRel]))).
    eapply PolyRed.posExt.
Qed.


Set Printing Universes.
#[local]
Lemma LRIrrelevantCumTy {lA}
  (IH : IHStatement lA lA)
  (Γ : context) (A : term)
  : [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ].
Proof.
  intros lrA; revert IH; pattern lA, Γ, A, lrA; eapply LR_rect_TyUr ; clear lA Γ A lrA.
  all: intros lA Γ A.
  - intros [] ?; eapply LRU_; now econstructor.
  - intros; now eapply LRne_.
  - intros [] IHdom IHcod IH; cbn in *.
    eapply LRPi'; unshelve econstructor.
    3,4,5: tea.
    unshelve eapply LRIrrelevantCumPolyRed; tea.
    + intros; now eapply IHdom.
    + intros; now eapply IHcod.
  - intros; now eapply LRNat_.
  - intros; now eapply LREmpty_.
  - intros [] IHdom IHcod IH; cbn in *.
    eapply LRSig'; unshelve econstructor.
    3,4,5: tea.
    unshelve eapply LRIrrelevantCumPolyRed; tea.
    + intros; now eapply IHdom.
    + intros; now eapply IHcod.
  - intros [] IHPar IHKripke IH.
    specialize (IHPar IH). pose (IHK Δ ρ wfΔ := IHKripke Δ ρ wfΔ IH).
    cbn in *; eapply LRId'.
    assert (eqv: equivLRPack tyRed IHPar).
    1: eapply LRIrrelevantPreds; tea; try eapply reflLRTyEq; now eapply LRAd.adequate.
    assert (eqvK : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), equivLRPack (tyKripke Δ ρ wfΔ) (IHK Δ ρ wfΔ)).
    1: intros; eapply LRIrrelevantPreds; tea; try eapply reflLRTyEq; now eapply LRAd.adequate.
    unshelve econstructor.
    4-7: tea.
    1-2: now apply eqv.
    2-3: intros * ? ?%eqvK; apply eqvK; eauto.
    econstructor.
    + intros ?? ?%eqv; apply eqv; now symmetry.
    + intros ??? ?%eqv ?%eqv; apply eqv; now etransitivity.
Qed.


#[local]
Lemma IrrRec0 : IHStatement zero zero.
Proof.
  intros ? ltA; inversion ltA.
Qed.

(** Safety check: we did not add constraints we did not mean to *)
Fail Fail Constraint i < i'.
Fail Fail Constraint i' < i.
Fail Fail Constraint j < j'.
Fail Fail Constraint j' < j.
Fail Fail Constraint k < k'.
Fail Fail Constraint k' < k.
Fail Fail Constraint l < l'.
Fail Fail Constraint l' < l.

End LRIrrelevantInductionStep.

#[local]
Theorem IrrRec@{i j k l i' j' k' l'} {lA} {lA'} :
  IHStatement@{i j k l i' j' k' l'} lA lA'.
Proof.
  intros l0 ltA ltA'.
  destruct ltA. destruct ltA'. cbn in *.
  split.
  - intros Γ t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' k' u i j k}).
  - intros Γ t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'} Γ t t
                (lr1 : LRPackAdequate (LogRel@{u i j k} zero) lr1)
                (lr2 : LRPackAdequate (LogRel@{u i' j' k'} zero) lr2)
                (reflLRTyEq lr1)) as [tyEq _].
    exact (tyEq u).
Qed.

#[local]
Theorem IrrelevantCum@{i j k l i' j' k' l'}
  (Γ : context) (A A' : term) {lA lA'}
  {eqTyA : term -> Type@{k}}
  {eqTyA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ A eqTyA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ A' eqTyA' eqTmA') :
  eqTyA A' ->
  @prod@{v v} (forall B, eqTyA B <≈> eqTyA' B)
    (forall t u, eqTmA t u <≈> eqTmA' t u).
Proof.
  exact (LRIrrelevantPreds@{i j k l i' j' k' l'} IrrRec Γ A A' lrA lrA').
Qed.

Theorem LRIrrelevantCum@{i j k l i' j' k' l'}
  {Γ : context} {A A' : term} {lA lA'}
  (RA : [ LogRel@{i j k l} lA | Γ ||- A ])
  (RA' : [ LogRel@{i' j' k' l'} lA' | Γ ||- A' ])
  (RAA' : [Γ ||-<lA> A ≅ A' | RA]) :
  equivLRPack@{v v v} RA RA'.
Proof.
  exact (IrrelevantCum _ _ _ RA.(LRAd.adequate) RA'.(LRAd.adequate) RAA').
Qed.

Theorem LRIrrelevantPack@{i j k l}
  (Γ : context) (A A' : term) {lA lA'}
  (RA : [ LogRel@{i j k l} lA | Γ ||- A ])
  (RA' : [ LogRel@{i j k l} lA' | Γ ||- A' ])
  (RAA' : [Γ ||-<lA> A ≅ A' | RA]) :
  equivLRPack@{v v v} RA RA'.
Proof. now apply LRIrrelevantCum. Qed.

Theorem LRTransEq@{i j k l}
  (Γ : context) (A B C : term) {lA lB}
  (RA : [ LogRel@{i j k l} lA | Γ ||- A ])
  (RB : [ LogRel@{i j k l} lB | Γ ||- B ])
  (RAB : [Γ ||-<lA> A ≅ B | RA])
  (RBC : [Γ ||-<lB> B ≅ C | RB]) :
  [Γ ||-<lA> A ≅ C | RA].
Proof.
  pose proof (LRIrrelevantPack Γ A B RA RB RAB) as [h _].
  now apply h.
Defined.


Theorem LRCumulative@{i j k l i' j' k' l'} {lA}
  {Γ : context} {A : term}
  : [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ].
Proof.
  exact (LRIrrelevantCumTy@{i j k l i' j' k' l'} IrrRec Γ A).
Qed.

Corollary LRCumulative' @{i j k l i' j' k' l'} {lA}
  {Γ : context} {A A' : term}
  : A = A' -> [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A' ].
Proof.
  intros ->; apply LRCumulative.
Qed.
End LRIrrelevant.


Corollary LRTyEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A ≅ B | lrA'].
Proof.
  apply (LRIrrelevantCum lrA lrA'), reflLRTyEq.
Qed.

Corollary LRTyEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A | lrA'].
Proof.
  apply (LRIrrelevantCum lrA lrA'), reflLRTyEq.
Qed.

Corollary LRTmEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary LRTyEqSym lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  [Γ ||-< lA > A ≅ A' | lrA] -> [Γ ||-< lA' > A' ≅ A | lrA'].
Proof.
  intros; eapply (LRIrrelevantCum lrA lrA'); tea.
  now eapply reflLRTyEq.
Qed.

Corollary LRTmEqConv lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A' ]) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u: A' | lrA'].
Proof.
  intros; now apply (LRIrrelevantCum lrA lrA').
Qed.

Corollary PolyRedEqSym {Γ l l' shp shp' pos pos'}
  {PA : PolyRed Γ l shp pos}
  (PA' : PolyRed Γ l' shp' pos') :
  PolyRedEq PA shp' pos' -> PolyRedEq PA' shp pos.
Proof.
  intros []; unshelve econstructor.
  - intros; eapply LRTyEqSym; eauto.
  - intros. eapply LRTyEqSym. unshelve eapply posRed; tea.
    eapply LRTmEqConv; tea.
    now eapply LRTyEqSym.
  Unshelve. all: tea.
Qed.

#[deprecated(note="Use LRTmEqConv")]
Corollary LRTmEqRedConv lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof. apply LRTmEqConv.  Qed.

Set Printing Primitive Projection Parameters.

Lemma NeNfEqSym {Γ k k' A} : [Γ ||-NeNf k ≅ k' : A] -> [Γ ||-NeNf k' ≅ k : A].
Proof.
  intros []; constructor; tea; now symmetry.
Qed.

Lemma LRTmEqSym@{h i j k l} lA Γ A (lrA : [LogRel@{i j k l} lA | Γ ||- A]) : forall t u,
  [Γ ||-<lA> t ≅ u : A |lrA] -> [Γ ||-<lA> u ≅ t : A |lrA].
Proof.
  pattern lA, Γ, A, lrA. apply LR_rect_TyUr; clear lA Γ A lrA.
  - intros * []. unshelve econstructor; try eassumption.
    1: symmetry; eassumption.
    now eapply TyEqRecFwd, LRTyEqSym@{h i j k h i j k}, TyEqRecFwd.
  - intros * []. unshelve econstructor.
    3,4: eassumption.
    symmetry; eassumption.
  - intros * ihdom ihcod * []. unshelve econstructor.
    1,2: eassumption.
    1: symmetry; eassumption.
    unfold PiRedTmEq.appRed in *. intros.
    assert (hba := ihdom _ _ _ _ _ hab).
    apply ihcod.
    eapply LRTmEqConv.
    2: eapply eqApp with (hab:=hba).
    eapply PolyRed.posExt.
  - intros ??? NA.
    set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA u t)) by apply h.
    subst G; apply NatRedEqInduction.
    1-3: now econstructor.
    intros; constructor; now eapply NeNfEqSym.
  - intros ??? NA.
    intros t u [? ? ? ? ? ? ? prop]. destruct prop. econstructor; eauto.
    2: econstructor; now eapply NeNfEqSym.
    symmetry; eassumption.
  - intros * ihshp ihpos * []; unshelve econstructor; tea.
    + intros; now eapply ihshp.
    + now symmetry.
    + intros; eapply ihpos.
      eapply LRTmEqConv.
      2: eapply eqSnd.
      now eapply PolyRed.posExt.
      Unshelve. eassumption.
  - intros ??? [] ???? [????? hprop]; unshelve econstructor; unfold_id_outTy; cbn in *.
    3,4: tea.
    1: now symmetry.
    destruct hprop; econstructor; tea.
    now eapply NeNfEqSym.
Qed.


End Irrelevances.


(* Could it be useful to redefine reducible convertibility independently from
  a witness of type reducibility ? *)
Definition LRTyConv `{GenericTypingProperties} Γ l (A B : term) := ∑ (C : term) (RC : [Γ ||-<l> C]), [Γ ||-<l> _ ≅ A | RC] × [Γ ||-<l> _ ≅ B | RC].

Notation "[ Γ ||-< l > A ≅ B ]" := (LRTyConv Γ l A B).

#[global]
Instance LRTmEqSymmetric `{GenericTypingProperties} {Γ A l} (RA : [Γ ||-<l> A]): Symmetric (RA.(LRPack.eqTm)).
Proof. intros x y; apply LRTmEqSym. Defined.

Ltac sym_escape RA H ::=
  let X := fresh "Rr" H in pose proof (X := escapeTerm RA (LRTmEqSym _ _ _ RA _ _ H)).

(** ** Tactics for irrelevance, with and without universe cumulativity *)

Ltac irrelevanceCum0 :=
  lazymatch goal with
  | [|- [_ ||-<_> _]] => (now eapply LRCumulative) + eapply LRCumulative'
  | [|- [_ | _ ||- _ ≅ _ ] ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ | _ ] ] => eapply LRTyEqIrrelevantCum'
  (* | [|- [_ | _ ||- _ : _ ] ] => eapply LRTmRedIrrelevantCum' *)
  (* | [|- [_ ||-<_> _ : _ | _ ] ] => eapply LRTmRedIrrelevantCum' *)
  | [|- [_ | _ ||- _ ≅ _ : _ ] ] => eapply LRTmEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevantCum'
  end.

Ltac irrelevanceCum := irrelevanceCum0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceCumRefl := irrelevanceCum0 ; [reflexivity|].

Ltac irrelevance0 :=
  lazymatch goal with
  | [|- [_ | _ ||- _ ≅ _ ] ] => eapply LRTyEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ | _ ] ] => eapply LRTyEqIrrelevant'
  (* | [|- [_ | _ ||- _ : _ ] ] => eapply LRTmRedIrrelevant' *)
  (* | [|- [_ ||-<_> _ : _ | _ ] ] => eapply LRTmRedIrrelevant' *)
  | [|- [_ | _ ||- _ ≅ _ : _ ] ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevant'
  (* | [|- [_ ||-<_> _ : _ | _] × [_ ||-<_> _≅ _ : _ | _]] => eapply LRTmTmEqIrrelevant' *)
  end.

Ltac irrelevance := irrelevance0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceRefl := irrelevance0 ; [reflexivity|].
