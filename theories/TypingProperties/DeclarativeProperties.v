(** * LogRel.DeclarativeProperties: basic properties of declarative typing, showing it is an instance of generic typing. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping.

Import DeclarativeTypingData.

(** ** Stability by weakening *)

Lemma shift_up_ren {Γ Δ t} (ρ : Δ ≤ Γ) : t⟨ρ⟩⟨↑⟩ = t⟨↑ >> up_ren ρ⟩.
Proof. now asimpl. Qed.

Section TypingWk.
  
  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩].
  Let PTm (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].



  Theorem typing_wk : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction.
    - trivial.
    - trivial.
    - intros ? ? IH.
      now econstructor.
    - intros Γ A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros ?????? ih ** ; rewrite <- wk_sig.
      constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id.
      constructor; eauto.
    - intros * _ IHA ? * ?.
      econstructor.
      now eapply IHA.
    - intros * _ IHΓ Hnth ? * ?.
      eapply typing_meta_conv.
      1: econstructor ; tea.
      1: eapply in_ctx_wk ; tea.
      reflexivity.
    - intros * _ IHA _ IHB ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      econstructor ; tea.
      econstructor.
      now eapply IHA.
    - intros * _ IHA _ IHt ? ρ ?.
      econstructor.
      1: now eapply IHA.
      eapply IHt with (ρ := wk_up _ ρ).
      econstructor ; tea.
      now eapply IHA.
    - intros * _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply typing_meta_conv.
      1: econstructor.
      1: now eapply IHf.
      1: now eapply IHu.
      now asimpl.
    - intros; now constructor.
    - intros; now constructor.
    - intros; cbn; econstructor; eauto.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      erewrite subst_ren_wk_up; eapply wfTermNatElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now bsimpl.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
      * now eapply ihn.
    - intros; now constructor.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up; eapply wfTermEmptyElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * now eapply ihe.
    - intros ???? ih1 ? ih2 ** ; rewrite <- wk_sig; cbn.
      constructor.
      1: now eapply ih1.
      eapply ih2 ; constructor; eauto.
      now constructor.
    - intros ?????? ihA ? ihB ? iha ? ihb **.
      rewrite <- wk_sig; rewrite <- wk_pair.
      constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up. 
      now eapply ihb.
    - intros; cbn; econstructor; eauto.
    - intros ????? ih **.
      unshelve erewrite subst_ren_wk_up; tea.
      econstructor; now eapply ih.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id.
      constructor; eauto.
    - intros * _ IHA _ IHx **; rewrite <- wk_Id, <- wk_refl.
      constructor; eauto.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      rewrite <- wk_idElim.
      erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
    - intros ?????????? ih **.
      do 2 rewrite <- wk_sig; constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2!wk_Id; constructor; eauto.
    - intros * _ IHA ? ρ ?.
      eapply TypeRefl.
      now eapply IHA.
    - intros * _ IH ? ρ ?.
      econstructor.
      now eapply IH.
    - intros * _ IH ? ρ ?.
      now econstructor ; eapply IH.
    - intros * _ IHA _ IHB ? ρ ?.
      eapply TypeTrans.
      + now eapply IHA.
      + now eapply IHB.
    - intros Γ u t A B _ IHA _ IHt _ IHu ? ρ ?.
      cbn.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHA.
      + eapply IHt with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
      + now eapply IHu.
      + now asimpl.
      + now asimpl. 
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        pose (IHA _ ρ H).
        econstructor; tea; now econstructor.
    - intros Γ u u' f f' A B _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHf.
      + now eapply IHu.
      + now asimpl.
      + now asimpl.
    - intros * _ IHA _ IHA' _ IHA'' _ IHe ? ρ ?.
      cbn; econstructor; try easy.
      apply (IHe _ (wk_up _ ρ)).
      now constructor.
    - intros * _ IHf ? ρ ?.
      cbn.
      rewrite <- shift_upRen.
      now apply TermFunEta, IHf.
    - intros * ? ih **; cbn; constructor; now apply ih.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      erewrite subst_ren_wk_up.
      eapply TermNatElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply ihhz.
        2: reflexivity.
        now bsimpl.
      * rewrite wk_elimSuccHypTy. 
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihhz ? ihhs **.
      erewrite subst_ren_wk_up.
      eapply TermNatElimZero; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now bsimpl.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **.
      erewrite subst_ren_wk_up.
      eapply TermNatElimSucc; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now bsimpl.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up.
      eapply TermEmptyElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * now eapply ihe.
    - intros * ????? ih ** ; do 2 rewrite <- wk_sig.
      constructor; eauto.
      eapply ih; constructor; tea; constructor; eauto.
    - intros * ? ihA₀ ? ihA ? ihA' ? ihB ? ihB' ? iha ? ihb Δ ρ **.
      rewrite <- wk_sig, <- !wk_pair.
      assert [|-[de] Δ,, A⟨ρ⟩] by now constructor.
      constructor; eauto.
      rewrite <- subst_ren_wk_up; now apply ihb.
    - intros * ? ihp Δ ρ **.
      rewrite <- wk_sig, <- wk_pair.
      constructor; rewrite wk_sig; eauto.
    - intros * ? ih **. econstructor; now eapply ih.
    - intros * ??? ihB ** ; rewrite <- wk_fst; rewrite <- wk_pair; constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * ? ih **.
      unshelve erewrite subst_ren_wk_up; tea; cbn.
      econstructor; now eapply ih.
    - intros * ??? ihB **. 
      rewrite <- wk_snd; rewrite <- wk_pair.
      unshelve erewrite subst_ren_wk_up.
      2:constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2! wk_Id; constructor; eauto.
    - intros * _ IHA _ IHx **.
      rewrite <- 2!wk_refl, <- wk_Id; constructor; eauto.
    - intros * _ IHA0 _ IHx0 _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      rewrite <- 2!wk_idElim; erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHA' _ IHz _ IHAA' _ IHxy _ IHxz **.
      rewrite <- wk_idElim; erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHA ? ρ ?.
      now econstructor.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHt' ? ρ ?.
      now econstructor.
  Qed.

End TypingWk.

(** ** A first set of boundary conditions *)

(** These lemmas assert that various boundary conditions, ie that if a certain typing-like relation
holds, some of its components are themselves well-formed. For instance, if [Γ |- t ⤳* u : A] then
[Γ |- t : A ]. The tactic boundary automates usage of these lemmas. *)

(** We cannot prove yet that all boundaries are well-typed: this needs stability of typing
by substitution and injectivity of type constructors, which we get from the logical relation.*)

Section Boundaries.
  Import DeclarativeTypingData.

  Definition boundary_ctx_ctx {Γ A} : [|- Γ,, A] -> [|- Γ].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_ctx_tip {Γ A} : [|- Γ,, A] -> [Γ |- A].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_tm_ctx {Γ} {t A} :
      [ Γ |- t : A ] -> 
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ctx_ctx.
  Qed.

  Definition boundary_ty_ctx {Γ} {A} :
      [ Γ |- A ] -> 
      [ |- Γ ].
  Proof.
    induction 1; now eauto using boundary_tm_ctx.
  Qed.

  Definition boundary_tm_conv_ctx {Γ} {t u A} :
      [ Γ |- t ≅ u : A ] -> 
      [ |- Γ ].
  Proof.
      induction 1 ; now eauto using boundary_tm_ctx, boundary_ty_ctx.
  Qed.

  Definition boundary_ty_conv_ctx {Γ} {A B} :
      [ Γ |- A ≅ B ] -> 
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ty_ctx, boundary_tm_conv_ctx.
  Qed.


  Definition boundary_red_l {Γ t u K} : 
    [ Γ |- t ⤳* u ∈ K] ->
    match K with istype => [ Γ |- t ] | isterm A => [ Γ |- t : A ] end.
  Proof.
    destruct 1; assumption.
  Qed.

  Definition boundary_red_tm_l {Γ t u A} : 
    [ Γ |- t ⤳* u : A] ->
    [ Γ |- t : A ].
  Proof.
    apply @boundary_red_l with (K := isterm A).
  Qed.

  Definition boundary_red_ty_l {Γ A B} : 
    [ Γ |- A ⤳* B ] ->
    [ Γ |- A ].
  Proof.
    apply @boundary_red_l with (K := istype).
  Qed.

End Boundaries.

#[export] Hint Resolve
  boundary_ctx_ctx boundary_ctx_tip boundary_tm_ctx
  boundary_ty_ctx boundary_tm_conv_ctx boundary_ty_conv_ctx
  boundary_red_tm_l
  boundary_red_ty_l : boundary.

(** ** Inclusion of the various reductions in conversion *)

Definition RedConvC {Γ} {t u : term} {K} :
    [Γ |- t ⤳* u ∈ K] -> 
    match K with istype => [Γ |- t ≅ u] | isterm A => [Γ |- t ≅ u : A] end.
Proof.
apply reddecl_conv.
Qed.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⤳* u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
apply @RedConvC with (K := isterm A).
Qed.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⤳* B] -> 
    [Γ |- A ≅ B].
Proof.
apply @RedConvC with (K := istype).
Qed.

(** ** Weakenings of reduction *)

Lemma redtmdecl_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- t ⤳* u : A] -> [Δ |- t⟨ρ⟩ ⤳* u⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - now apply credalg_wk.
  - now apply typing_wk.
Qed.

Lemma redtydecl_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- A ⤳* B] -> [Δ |- A⟨ρ⟩ ⤳* B⟨ρ⟩].
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - now apply credalg_wk.
  - now apply typing_wk.
Qed.

(** ** Derived rules for multi-step reduction *)

Lemma redtmdecl_app Γ A B f f' t :
  [ Γ |- f ⤳* f' : tProd A B ] ->
  [ Γ |- t : A ] ->
  [ Γ |- tApp f t ⤳* tApp f' t : B[t..] ].
Proof.
  intros [] ?; split.
  + now econstructor.
  + now apply redalg_app.
  + econstructor; [tea|now apply TermRefl].
Qed.

Lemma redtmdecl_conv Γ t u A A' : 
  [Γ |- t ⤳* u : A] ->
  [Γ |- A ≅ A'] ->
  [Γ |- t ⤳* u : A'].
Proof.
  intros [] ?; split.
  + now econstructor.
  + assumption.
  + now econstructor.
Qed.

Lemma redtydecl_term Γ A B :
  [ Γ |- A ⤳* B : U] -> [Γ |- A ⤳* B ].
Proof.
  intros []; split.
  + now constructor.
  + assumption.
  + now constructor.
Qed.

#[export] Instance RedTermTrans Γ A : Transitive (red_tm Γ A).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TermTrans.
Qed.

#[export] Instance RedTypeTrans Γ : Transitive (red_ty Γ).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TypeTrans.
Qed.

(** ** Bundling the properties together in an instance *)

Module WeakDeclarativeTypingProperties.
  Export DeclarativeTypingData.

  #[export] Instance ConvNeuConv_WeakDecl : ConvNeuConv de := ConvNeuConvDecl.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-2: now constructor.
    all: boundary. 
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    all: try now econstructor.
    - intros.
      now eapply typing_wk.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    all: try (intros; now econstructor).
    - intros.
      now eapply typing_wk.
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := de) := {}.
  Proof.
  - now econstructor.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now apply typing_wk.
  - intros.
    eapply TypeTrans ; [eapply TypeTrans | ..].
    2: eassumption.
    2: eapply TypeSym.
    all: now eapply RedConvTyC.
  - econstructor.
    now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  Qed.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de) := {}.
  Proof.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - intros.
    econstructor; [|tea].
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - intros * ? H; apply H.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - intros.
    eapply TermTrans; [|now eapply TermFunEta].
    eapply TermTrans; [now eapply TermSym, TermFunEta|].
    constructor; tea.
    all: now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - intros.
    eapply TermTrans; [|now constructor].
    eapply TermTrans; [eapply TermSym; now constructor|].
    constructor; tea; now apply TypeRefl.
  - now do 2 econstructor.
  - now econstructor.
  - now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de) := {}.
  Proof.
  - split; red.
    + intros ?? []; split; tea; now econstructor.
    + intros ??? [] []; split; tea; now econstructor.
  - intros ????? [] ?; split; tea; now econstructor.
  - intros ??????? []; split.
    + now eapply whne_ren.
    + now eapply whne_ren.
    + now eapply typing_wk.
  - now intros ???? [].
  - intros ???; split; now econstructor.
  - intros ??????? [] ?; split; now econstructor.
  - intros ???????????? []; split; now econstructor.
  - intros ?????? []; split; now econstructor.
  - intros ????? []; split; now econstructor.
  - intros ????? []; split; now econstructor.
  - intros * ??????? []; split; now econstructor.
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
  - intros; now eapply redtmdecl_red.
  - intros. now eapply boundary_red_tm_l.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; now eapply redtmdecl_app.
  - intros * ??? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_natElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros * ? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_natEmpty.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_fst.
    + now econstructor.
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_snd.
    + now econstructor.
  - intros **; split; refold.
    + econstructor; tea.
      econstructor. 
      1: econstructor; tea; now econstructor.
      econstructor.
      1: now econstructor.
      1,2: econstructor; tea.
      1: now econstructor.
      eapply TermTrans; tea; now econstructor.
    + eapply redalg_one_step; constructor.
    + now econstructor.
  - intros * ????? []; split; refold.
    + now econstructor.
    + now eapply redalg_idElim.
    + econstructor; tea; now (eapply TypeRefl + eapply TermRefl).
  - intros; now eapply redtmdecl_conv.
  - intros; split.
    + assumption.
    + reflexivity.
    + now econstructor.
  Qed.

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtydecl_wk.
  - intros; now eapply redtydecl_red.
  - intros. now eapply boundary_red_ty_l.
  - intros.
    now eapply redtydecl_term.
  - intros; split.
    + assumption.
    + reflexivity.
    + now constructor.
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ _ _ := {}.

End WeakDeclarativeTypingProperties.