From Coq Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity.
From Equations Require Import Equations.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.
Set Primitive Projections.



Section Weakenings.
  Context `{GenericTypingProperties}.

  Record kripke@{i j k l} {Γ l A B} {RAB : [LogRel@{i j k l} l | Γ ||- A ≅ B]} := {
    wkRed : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩] ;
    wkRedTm : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) {t u},
      [Γ ||-<l> t ≅ u : _ | RAB] -> [Δ ||-<l> t⟨ρ⟩ ≅ u⟨ρ⟩ : _ | wkRed ρ wfΔ] ;
  }.
  Arguments kripke {_ _ _ _} _.

  Definition wkStmt@{i j k l} l := (forall Γ A B (R : [LogRel@{i j k l} l | Γ ||- A ≅ B]), kripke R).

  Lemma wkU {Γ Δ l A B} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (h : [Γ ||-U<l> A ≅ B]) : [Δ ||-U<l> A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof. destruct h; econstructor; tea; change U with U⟨ρ⟩; gen_typing. Defined.

  Lemma wkURedTerm {Γ Δ l t} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) :
    URedTm l Γ t -> URedTm l Δ t⟨ρ⟩.
  Proof.
    intros [te]. exists te⟨ρ⟩; change U with U⟨ρ⟩.
    - gen_typing.
    - apply isType_ren; assumption.
  Defined.

  Lemma wkLRU {l}
    (ih : forall l', l' << l -> wkStmt l')
    {Γ A B} {h : [Γ ||-U<l> A ≅ B]} : kripke (LRU_ h).
  Proof.
    unshelve econstructor.
    1: intros; now eapply LRU_, wkU.
    cbn; intros * [??? ?%redTyRecFwd]; unshelve econstructor.
    1,2: now eapply wkURedTerm.
    1: cbn; change U with U⟨ρ⟩; gtyping.
    eapply redTyRecBwd.
    eapply ih; cbn; tea.
    apply URedTy.lt.
  Qed.


  Lemma wkPoly {Γ l shp shp' pos pos' Δ}  (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    PolyRed Γ l shp shp' pos pos' ->
    PolyRed Δ l shp⟨ρ⟩ shp'⟨ρ⟩ pos⟨wk_up shp ρ⟩ pos'⟨wk_up shp' ρ⟩.
  Proof.
    intros []; opector.
    - intros ? ρ' ?; rewrite 2!wk_comp_ren_on; now eapply shpRed.
    - intros ? a b ρ' **; rewrite <-2!wk_up_ren_subst.
      unshelve eapply posRed; tea; eapply irrLREq; tea; now rewrite wk_comp_ren_on.
  Qed.

  Lemma wkParamTy {T Γ A shp pos Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (wkT : forall A B, (T A B)⟨ρ⟩ = T A⟨ρ⟩ B⟨wk_up A ρ⟩) :
    ParamRedTyPack.ParamTy (T:=T) Γ A shp pos -> ParamRedTyPack.ParamTy (T:=T) Δ A⟨ρ⟩ shp⟨ρ⟩ pos⟨wk_up shp ρ⟩.
  Proof.
    intros []; econstructor.
    1: rewrite <- wkT; gtyping.
    1: gtyping.
    eapply wft_wk; tea; gtyping.
  Qed.

  Lemma wkParamRedTy {T Γ l A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (wkT : forall A B, (T A B)⟨ρ⟩ = T A⟨ρ⟩ B⟨wk_up A ρ⟩) :
    ParamRedTy T Γ l A B -> ParamRedTy T Δ l A⟨ρ⟩ B⟨ρ⟩.
  Proof.
    intros []; econstructor.
    1,2: now eapply wkParamTy.
    1: gtyping.
    1: rewrite <- 2!wkT; gtyping.
    now eapply wkPoly.
  Defined.

  Lemma wkΠ  {Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A ≅ B]) :
    [Δ ||-Π< l > A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof. eapply wkParamRedTy; tea; intros; now rewrite wk_prod. Defined.

  Lemma wkΣ  {Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΣA : [Γ ||-Σ< l > A ≅ B]) :
    [Δ ||-Σ< l > A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof. eapply wkParamRedTy; tea; intros; now rewrite wk_sig. Defined.

  Lemma wk_isLRFun {Γ l A B} (ΠA : [Γ ||-Π< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    isLRFun ΠA t -> isLRFun (wkΠ ρ wfΔ ΠA) t⟨ρ⟩.
  Proof.
    intros * [A' t' wtdom convtydom Ht|]; rewrite <-?wk_lam; constructor; tea; refold.
    + now eapply wft_wk.
    + now eapply convty_wk.
    + intros Ξ a b ρ' wfΞ *; cbn.
      rewrite <-2!wk_up_ren_subst ; eapply irrLREq.
      1: now rewrite <-wk_up_ren_subst.
      unshelve eapply Ht; tea ; eapply irrLREq; tea; cbn; now rewrite wk_comp_ren_on.
    + cbn; rewrite wk_prod; now eapply convneu_wk.
  Qed.

  Lemma wkPiRedTerm {Γ l A B} (ΠA : [Γ ||-Π< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA' := wkΠ ρ wfΔ ΠA) :
    PiRedTm ΠA t -> PiRedTm ΠA' t⟨ρ⟩.
  Proof.
    intros [nf].
    exists (nf⟨ρ⟩); cbn; try change (tProd _ _) with ((outTyL ΠA)⟨ρ⟩).
    + now eapply redtmwf_wk.
    + now apply wk_isLRFun.
  Defined.

  Lemma wkLRΠ {Γ l A B} (ΠA : [Γ ||-Π< l > A ≅ B]) : kripke (LRPi' ΠA).
  Proof.
    unshelve econstructor.
    - intros; now apply LRPi', wkΠ.
    - cbn ; intros * []; unshelve econstructor.
      1,2: now apply wkPiRedTerm.
      1: cbn; rewrite wk_prod; now eapply convtm_wk.
    intros Ξ a b ρ' wfΞ hab; cbn; rewrite 2!wk_comp_ren_on.
    eapply irrLREq; [now rewrite <-wk_up_ren_subst| unshelve eapply eqApp; tea].
      eapply irrLREq; tea; cbn; now rewrite wk_comp_ren_on.
  Qed.

  Lemma wk_up_subst1 {Γ Δ F} t a (ρ : Γ ≤ Δ) : t⟨wk_up F ρ⟩[(a⟨ρ⟩)..] = t[a..]⟨ρ⟩.
  Proof. now bsimpl. Qed.

  Lemma wk_isLRPair {Γ l A B} (ΣA : [Γ ||-Σ< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    isLRPair ΣA t -> isLRPair (wkΣ ρ wfΔ ΣA) t⟨ρ⟩.
  Proof.
  intros * [A' B' a b wtydom convtydom wtycod convtycod Hfst Hsnd|]; unshelve econstructor; tea; refold.
  all: try first [now eapply wft_wk| now eapply convty_wk].
  + refold; intros Ξ ρ' wfΞ.
    rewrite wk_comp_ren_on; eapply irrLREq; [|now unshelve eapply Hfst].
    cbn; now rewrite wk_comp_ren_on.
  + erewrite <- (wk_up_ren_on _ _ _ A'), wk_up_subst1.
    now eapply wft_wk.
  + cbn; erewrite <- (wk_up_ren_on _ _ _ A'), 2!wk_up_subst1.
    now eapply convty_wk.
  + refold; intros Ξ ρ' wfΞ.
    eapply irrLREq.
    2:rewrite wk_comp_ren_on ; now unshelve apply Hsnd.
    cbn; now rewrite <-wk_up_ren_subst, wk_comp_ren_on.
  + cbn; rewrite wk_sig; now eapply convneu_wk.
  Qed.

  Lemma wkSigRedTerm {Γ l A B} (ΣA : [Γ ||-Σ< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    SigRedTm ΣA t -> SigRedTm (wkΣ ρ wfΔ ΣA) t⟨ρ⟩.
  Proof.
    intros [nf].
    unshelve eexists (nf⟨ρ⟩); try (cbn; rewrite wk_sig).
    + now eapply redtmwf_wk.
    + apply wk_isLRPair; assumption.
  Defined.

  Lemma wkLRΣ {Γ l A B} (ΣA : [Γ ||-Σ< l > A ≅ B]) : kripke (LRSig' ΣA).
  Proof.
    unshelve econstructor.
    - intros; now apply LRSig', wkΣ.
    - cbn ; intros * []; unshelve econstructor.
      1,2: now apply wkSigRedTerm.
      2: cbn; rewrite wk_sig; now eapply convtm_wk.
      + intros Ξ ρ' wfΞ ; cbn; rewrite 2!wk_comp_ren_on.
        eapply irrLREq; [now rewrite wk_comp_ren_on| now unshelve eapply eqFst].
      + intros Ξ ρ' wfΞ ; cbn.
        eapply irrLREq.
        2: rewrite 2!wk_comp_ren_on; now unshelve eapply eqSnd.
        cbn; now rewrite <-wk_up_ren_subst, wk_comp_ren_on.
  Qed.

  Lemma wkNat {Γ A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Nat A ≅ B] -> [Δ ||-Nat A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof.
    intros []; constructor.
    all: change tNat with tNat⟨ρ⟩; gtyping.
  Qed.

  Lemma wkEmpty {Γ A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Empty A ≅ B] -> [Δ ||-Empty A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof.
    intros []; constructor; change tEmpty with tEmpty⟨ρ⟩; gtyping.
  Qed.

  Lemma wkId@{i j k l} {Γ l A B} (IA : IdRedTy@{i j k l} Γ l A B)
    (ih : kripke@{i j k l} IA.(IdRedTy.tyRed)) {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    IdRedTy@{i j k l} Δ l A⟨ρ⟩ B⟨ρ⟩.
  Proof.
    unshelve econstructor.
    8,9: erewrite wk_Id; eapply redtywf_wk; tea; apply IA.(IdRedTy.redL) + apply IA.(IdRedTy.redR).
    2: rewrite 2!wk_Id; eapply convty_wk; tea; eapply IA.(IdRedTy.eq).
    - now eapply ih.(wkRed).
    - eapply wkRedTm; now destruct IA.
    - eapply wkRedTm; now destruct IA.
    - apply perLRTm.
  Defined.

  Lemma wkNeNfEq {Γ Δ k k' A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) :
    [Γ ||-NeNf k ≅ k' : A] -> [Δ ||-NeNf k⟨ρ⟩ ≅ k'⟨ρ⟩ : A⟨ρ⟩].
  Proof.
    intros []; constructor; gen_typing.
  Qed.


  Lemma wkLR_rec@{h i j k l} {l} (ih : forall l', l' << l -> wkStmt@{h i j k} l') :
    wkStmt@{i j k l} l.
  Proof.
    intros Γ A B RAB; revert ih; indLR RAB.
    - intros; now apply wkLRU.
    - intros [] _; unshelve econstructor.
      + intros; apply LRne_; econstructor.
        1,2: now eapply redtywf_wk.
        change U with U⟨ρ⟩; gtyping.
      + cbn; intros * []; cbn in *; econstructor; cbn.
        1,2: now eapply redtmwf_wk.
        gtyping.
    - intros; eapply wkLRΠ.
    - intros; unshelve econstructor.
      + intros; now eapply LRNat_, wkNat.
      + intros ???; cbn.
        set (G := _); enough (h : G × (forall t u, NatPropEq Γ t u -> NatPropEq Δ t⟨ρ⟩ u⟨ρ⟩)) by apply h.
        subst G; apply NatRedEqInduction.
        * intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
        * constructor.
        * now constructor.
        * intros; constructor.
          change tNat with tNat⟨ρ⟩.
          now eapply wkNeNfEq.
    - intros; unshelve econstructor.
      + intros; now eapply LREmpty_, wkEmpty.
      + cbn; intros ????? []; econstructor; change tEmpty with tEmpty⟨ρ⟩.
        1,2: now eapply redtmwf_wk.
        now eapply wkNeNfEq.
    - intros; eapply wkLRΣ.
    - intros IA ihty ih; unshelve econstructor.
      + intros ; eapply LRId', wkId; eauto.
      + intros * [????? prop]; econstructor; cbn; rewrite ?wk_Id.
        1,2: now eapply redtmwf_wk.
        1: now eapply convtm_wk.
        destruct prop; constructor; refold; cbn; rewrite ?wk_Id.
        1-4: gtyping.
        1,2: now eapply convty_wk.
        5: now eapply wkNeNfEq.
        all: now eapply ihty.
  Qed.

  Theorem wkLR0@{i j k l} : wkStmt@{i j k l} zero.
  Proof.
    eapply wkLR_rec; intros ? h; inversion h.
  Qed.

  Theorem wkLR@{h i j k l} {l}: wkStmt@{i j k l} l.
  Proof.
    intros; eapply wkLR_rec.
    intros ? h; inversion h. eapply wkLR0.
  Qed.


End Weakenings.
