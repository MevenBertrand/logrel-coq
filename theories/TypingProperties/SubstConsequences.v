(** * LogRel.SubstConsequences: consequences of stability by substitution. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All DeclarativeTyping GenericTyping.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition.

(** Many lemmas in this file, prefixed by an underscore, have extraneous premises, which we cannot remove directly because of circular dependencies. The "correct" version is the one without underscore. *)

Set Printing Primitive Projection Parameters.

Import WeakDeclarativeTypingProperties.

Section MoreSubst.

  Context `{!TypingSubst (ta := de)}.

  Lemma ctx_refl Γ :
    [|- Γ] ->
    [|- Γ ≅ Γ].
  Proof.
    induction 1.
    all: constructor; tea.
    now econstructor.
  Qed.

  Lemma subst_wk (Γ Δ Δ' : context) (ρ : Δ' ≤ Δ) σ :
    [|- Δ'] ->
    [Δ |-s σ : Γ] ->
    [Δ' |-s σ⟨ρ⟩ : Γ].
  Proof.
    intros ?.
    induction 1 as [|σ Γ A].
    1: now econstructor.
    econstructor.
    - asimpl ; cbn in * ; asimpl.
      eassumption.
    - asimpl ; cbn in * ; asimpl.
      unfold funcomp.
      eapply typing_meta_conv.
      1: eapply typing_wk ; eassumption.
      asimpl.
      reflexivity.
  Qed.

  Corollary well_subst_up (Γ Δ : context) A σ :
    [Δ |- A] ->
    [Δ |-s σ : Γ] ->
    [Δ ,, A |-s σ⟨↑⟩ : Γ].
  Proof.
    intros HA Hσ.
    eapply subst_wk with (ρ := wk_step A wk_id) in Hσ.
    - eapply well_subst_ext ; [|eassumption].
      bsimpl.
      now reflexivity.
    - econstructor.
      all: gen_typing.
  Qed.

  Lemma id_subst (Γ : context) :
    [|- Γ] ->
    [Γ |-s tRel : Γ].
  Proof.
    induction 1.
    all: econstructor.
    - eapply well_subst_ext.
      2: now eapply well_subst_up.
      now asimpl.
    - eapply typing_meta_conv.
      1: now do 2 econstructor.
      cbn ; now renamify.
  Qed.

  Lemma subst_refl (Γ Δ : context) σ :
    [Γ |-s σ : Δ] ->
    [Γ |-s σ ≅ σ : Δ].
  Proof.
    induction 1.
    all: econstructor ; tea.
    now eapply TermRefl.
  Qed.

  Theorem typing_subst1 Γ T :
  (forall (t : term), [Γ |- t : T] ->
    forall (A : term), [Γ,, T |- A] -> [Γ |- A[t..]]) ×
  (forall (t : term), [Γ |- t : T] ->
    forall (A u : term), [Γ,, T |- u : A] -> [Γ |- u[t..] : A[t..]]) ×
  (forall (t t' : term), [Γ |- t ≅ t' : T] ->
    forall (A B : term), [Γ,, T |- A ≅ B] -> [Γ |- A[t..] ≅ B[t'..]]) ×
  (forall (t t' : term), [Γ |- t ≅ t' : T] ->
    forall (A u v : term), [Γ,, T |- u ≅ v : A] -> [Γ |- u[t..] ≅ v[t'..] : A[t..]]).
  Proof.
    repeat match goal with |- _ × _ => split end.
    all: intros * Ht * Hty.
    all: assert ([|- Γ]) by gen_typing.
    all: assert ([Γ |-s tRel : Γ]) as Hsubst by now eapply id_subst.
    3-4: apply subst_refl in Hsubst.
    all: first [eapply ty_subst| eapply tm_subst | eapply ty_conv_subst | eapply tm_conv_subst] ; tea.
    all: econstructor ; cbn ; refold ; now asimpl.
  Qed.

  Theorem typing_substmap1 Γ T :
  (forall (t : term), [Γ ,, T |- t : T⟨↑⟩] ->
    forall (A : term), [Γ,, T |- A] -> 
      [Γ,, T |- A[t]⇑]) ×
  (forall (t : term), [Γ ,, T |- t : T⟨↑⟩] ->
    forall (A u : term), [Γ,, T |- u : A] -> 
      [Γ,, T |- u[t]⇑ : A[t]⇑]) ×
  (forall (t t' : term), [Γ ,, T |- t ≅ t' : T⟨↑⟩] ->
    forall (A B : term), [Γ,, T |- A ≅ B] ->
      [Γ,, T |- A[t]⇑ ≅ B[t']⇑]) ×
  (forall (t t' : term), [Γ ,, T |- t ≅ t' : T⟨↑⟩] ->
    forall (A u v : term), [Γ,, T |- u ≅ v : A] -> 
      [Γ,, T |- u[t]⇑ ≅ v[t']⇑ : A[t]⇑]).
  Proof.
    repeat match goal with |- _ × _ => split end.
    all: intros * Ht * Hty.
    all: assert ([|- Γ,, T] × [|- Γ]) as [] by (split; repeat boundary).
    all : assert (Hsubst : [Γ ,, T |-s ↑ >> tRel : Γ])
            by (change (?x >> ?y) with y⟨x⟩; eapply well_subst_up; [boundary| now eapply id_subst]).
    3-4: apply subst_refl in Hsubst.
    all: first [eapply ty_subst| eapply tm_subst | eapply ty_conv_subst | eapply tm_conv_subst] ; tea.
    all: econstructor ; cbn ; refold; bsimpl; try rewrite <- rinstInst'_term; tea.
  Qed.

  Lemma scons2_well_subst {Γ A B} : 
    (forall a b, [Γ |- a : A] -> [Γ |- b : B[a..]] -> [Γ |-s (b .: a ..) : (Γ ,, A),, B])
    × (forall a a' b b', [Γ |- a ≅ a' : A] -> [Γ |- b ≅ b' : B[a..]] -> [Γ |-s (b .: a..) ≅ (b' .: a'..) : (Γ ,, A),, B]).
  Proof.
    assert (h : forall (a : term) σ, ↑ >> (a .: σ) =1 σ) by reflexivity.
    assert (h' : forall a σ t, t[↑ >> (a .: σ)] = t[σ]) by (intros; now setoid_rewrite h).
    split; intros; econstructor.
    - asimpl; econstructor.
      2: cbn; rewrite h'; now asimpl.
      asimpl; eapply id_subst; gen_typing.
    - cbn; now rewrite h'.
    - asimpl; econstructor.
      2: cbn; rewrite h'; now asimpl.
      asimpl; eapply subst_refl; eapply id_subst; gen_typing.
    - cbn; now rewrite h'.
  Qed.

  Lemma typing_subst2 {Γ A B} :
    [|- Γ] ->
    (forall P a b, [Γ |- a : A] -> [Γ |- b : B[a..]] -> [Γ,, A,, B |- P] -> [Γ |- P[b .: a ..]])
    × (forall P P' a a' b b', [Γ |- a ≅ a' : A] -> [Γ |- b ≅ b' : B[a..]] -> [Γ,, A ,, B |- P ≅ P'] -> [Γ |- P[b .: a..] ≅ P'[b' .: a'..]]).
  Proof.
    intros;split; intros.
    1: eapply ty_subst ; tea.
    2: eapply ty_conv_subst ; tea.
    all: now eapply scons2_well_subst.
  Qed.

  Lemma conv_well_subst1 (Γ : context) A A' :
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ |- A ≅ A'] ->
    [Γ,, A |-s tRel : Γ,, A'].
  Proof.
    intros HA HA' Hconv.
    econstructor.
    - change (↑ >> tRel) with (tRel⟨↑⟩).
      eapply well_subst_up ; tea.
      now eapply id_subst ; gen_typing.
    - refold.
      eapply wfTermConv.
      1: constructor; [gen_typing|now econstructor].
      rewrite <- rinstInst'_term; do 2 erewrite <- wk1_ren_on; eapply typing_wk; tea.
      gen_typing.
  Qed.

  Theorem _stability1 (Γ : context) A A' :
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ |- A ≅ A'] ->
    (forall (T : term), [Γ,, A' |-[de] T] -> [Γ,, A |-[de] T])
    × (forall (T t : term), [Γ,, A' |-[ de ] t : T] -> [Γ,, A |-[de] t : T])
    × (forall (T T' : term), [Γ,, A' |-[ de ] T ≅ T'] -> [Γ,, A |-[de] T ≅ T'])
    × (forall (T t u : term),
          [Γ,, A' |-[ de ] t ≅ u : T] -> [Γ,, A |-[de] t ≅ u : T]).
  Proof.
    intros * ? ? Hconv.
    eapply (conv_well_subst1 _) in Hconv ; tea.
    pose proof (Hconv' := Hconv).
    apply subst_refl in Hconv'.
    assert [|- Γ,, A] by gen_typing.
    repeat match goal with |- _ × _ => split end.
    all: intros * Hty.
    4: eapply tm_conv_subst in Hty.
    3: eapply ty_conv_subst in Hty.
    2: eapply tm_subst in Hty.
    1: eapply ty_subst in Hty.
    all: repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: eassumption.
  Qed.

  Lemma _conv_well_subst (Γ Δ : context) :
    [|- Γ] ->
    [ |- Γ ≅ Δ] ->
    [Γ |-s tRel : Δ].
  Proof.
    intros HΓ.
    induction 1 as [| * ? HA] in HΓ |- *.
    - now econstructor.
    - assert [Γ |- A] by now inversion HΓ.
      assert [|- Γ] by now inversion HΓ.
      econstructor ; tea.
      + eapply well_subst_ext, well_subst_up ; eauto.
        reflexivity.
      + eapply wfTermConv.
        1: econstructor; [gen_typing| now econstructor].
        rewrite <- rinstInst'_term; do 2 erewrite <- wk1_ren_on.
        now eapply typing_wk.
  Qed.

End MoreSubst.

(** Stability and symmetry with redundant hypothesis on the well-formed contexts *)

Section Stability.

  Context `{!TypingSubst (ta := de)}.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- A].
  Let PTm (Γ : context) (A t : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- t : A].
  Let PTyEq (Γ : context) (A B : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- t ≅ u : A].

  Theorem _stability : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    red; prod_splitter; intros Γ * Hty; red.
    1: easy.
    all: intros ?? Hconv; eapply (_conv_well_subst _) in Hconv ; tea.
    all: pose proof (Hconv' := Hconv); apply  subst_refl in Hconv'.
    4: eapply tm_conv_subst in Hty.
    3: eapply ty_conv_subst in Hty.
    2: eapply tm_subst in Hty.
    1: eapply ty_subst in Hty.
    all: tea.
    all: repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: eassumption.
  Qed.

  Definition _convCtxSym {Γ Δ} : [|- Δ] -> [|- Γ] -> [|- Δ ≅ Γ] -> [|- Γ ≅ Δ].
  Proof.
    induction 3.
    all: constructor; inversion H; inversion H0; subst; refold.
    1: now eauto.
    eapply _stability ; tea.
    1: now symmetry.
    now eauto.
  Qed.

End Stability.

Section ElimSuccHyp.

  Context `{!TypingSubst (ta := de)}.

  Lemma elimSuccHypTy_ty Γ P :
    [|- Γ] ->
    [Γ,, tNat |- P] ->
    [Γ |-[ de ] elimSuccHypTy P].
  Proof.
    intros HΓ HP.
    unfold elimSuccHypTy.
    econstructor.
    1: now econstructor.
    eapply wft_simple_arr.
    1: now eapply HP.
    eapply ty_subst ; eauto.
    1: boundary.
    econstructor.
    - bsimpl.
      eapply well_subst_ext.
      2: eapply well_subst_up.
      3: eapply id_subst ; tea.
      2: now econstructor.
      now bsimpl.
    - cbn.
      econstructor.
      eapply typing_meta_conv.
      1: now do 2 econstructor ; tea ; econstructor.
      reflexivity.
  Qed.

  Lemma elimSuccHypTy_conv Γ P P' :
    [|- Γ] ->
    [Γ,, tNat |- P] ->
    [Γ,, tNat |- P ≅ P' ] ->
    [Γ |- elimSuccHypTy P ≅ elimSuccHypTy P'].
  Proof.
    intros.
    unfold elimSuccHypTy.
    constructor.
    2: constructor.
    1-2: now constructor.
    eapply convty_simple_arr; tea.
    eapply typing_substmap1; tea.
    do 2 constructor; refine (wfVar _ (in_here _ _)).
    constructor; boundary.
  Qed.

End ElimSuccHyp.


(** *** Typing lemmas *)
(** Weak versions necessary to prove the boundary lemmas. Stronger versions follow. *)

Lemma idElimMotiveCtx {Γ A x} : 
[Γ |- A] ->
[Γ |- x : A] ->
[|- (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)].
Proof.
  intros; assert [|- Γ] by boundary.
  assert [|- Γ,, A] by now econstructor.
  econstructor; tea.
  econstructor.
  1: now eapply wft_wk.
  1:  eapply ty_wk; tea; econstructor; tea.
  rewrite wk1_ren_on; now eapply ty_var0.
Qed.

Lemma _idElimMotiveCtxConv `{!TypingSubst (ta := de)} {Γ Γ' A A' x x'} :
[|- Γ ≅ Γ'] ->
[Γ |- A ≅ A'] ->
[Γ |- x ≅ x' : A] ->
[ |- (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)] ->
[ |- (Γ',, A'),, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0)] ->
[ |- (Γ',, A'),, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0) ≅ (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)].
Proof.
  intros.
  assert [|- Γ] by boundary.
  assert [Γ |- A] by boundary.
  assert [Γ' |- A'] by boundary.
  eapply _convCtxSym ; tea.
  econstructor.
  1: econstructor; tea; now eapply ctx_refl.
  erewrite (wk1_irr (t:=A')), (wk1_irr (t:=x')) ; econstructor.
  1,2: eapply typing_wk; tea; gen_typing.
  rewrite wk1_ren_on; eapply TermRefl; now eapply ty_var0.
Qed.

Section Boundary.
  Context `{!TypingSubst (ta := de)}.

  Lemma in_ctx_wf Γ n decl :
    [|- Γ] ->
    in_ctx Γ n decl ->
    [Γ |- decl].
  Proof.
    intros HΓ Hin.
    induction Hin.
    - inversion HΓ ; subst ; cbn in * ; refold.
      renToWk.
      now apply typing_wk.
    - inversion HΓ ; subst ; cbn in * ; refold.
      renToWk.
      now eapply typing_wk.
  Qed.

  Lemma boundary : WfDeclInductionConcl
    (fun _ => True) (fun _ _ => True)
    (fun Γ A t => [Γ |- A])
    (fun Γ A B => [Γ |- A] × [Γ |- B])
    (fun Γ A t u => [× [Γ |- A], [Γ |- t : A] & [Γ |- u : A]]).
  Proof.
    apply WfDeclInduction.
    all: try easy.
    - intros.
      now eapply in_ctx_wf.
    - intros.
      now econstructor.
    - intros.
      now eapply typing_subst1, prod_ty_inv.
    - intros; gen_typing.
    - intros; gen_typing.
    - intros.
      now eapply typing_subst1.
    - intros; gen_typing.
    - intros.
      now eapply typing_subst1.
    - intros; gen_typing.
    - intros. now eapply sig_ty_inv.
    - intros.
      eapply typing_subst1.
      + now econstructor.
      + now eapply sig_ty_inv.
    - intros; now econstructor.
    - intros; eapply typing_subst2; tea.
      1: gen_typing.
      cbn; now rewrite 2!wk1_ren_on, 2!shift_one_eq.
    - intros * ? _ ? [] ? [].
      split.
      all: constructor ; tea.
      eapply _stability1.
      3: now symmetry.
      all: eassumption.
    - intros * ? _ ? [] ? []; split.
      1: gen_typing.
      constructor; tea.
      eapply _stability1. 
      3: now symmetry.
      all: tea.
    - intros; prod_hyp_splitter; split; econstructor; tea; now eapply wfTermConv.
    - intros * ? [].
      split.
      all: now econstructor.
    - intros.
      split.
      + now eapply typing_subst1.
      + econstructor ; tea.
        now econstructor.
      + now eapply typing_subst1.
    - intros * ? _ ? [] ? [].
      split.
      + easy.
      + now econstructor.
      + econstructor ; tea.
        eapply _stability1.
        4: eassumption.
        all: econstructor ; tea.
        now symmetry.
    - intros * ? [] ? [].
      split.
      + eapply typing_subst1.
        1: eassumption.
        now eapply prod_ty_inv.
      + now econstructor.
      + econstructor.
        1: now econstructor.
        eapply typing_subst1.
        1: now symmetry.
        econstructor.
        now eapply prod_ty_inv.
    - intros * ? _ ? [] ? [] ? [].
      split.
      all: econstructor ; tea.
      + econstructor ; tea.
        eapply _stability1 ; [..|eassumption] ; eauto.
        now symmetry.
      + symmetry.
        econstructor ; eauto.
        now econstructor.
      + econstructor ; tea.
        eapply _stability1 ; [..|eassumption] ; eauto.
        now symmetry.
      + symmetry.
        econstructor ; eauto.
        now econstructor.
    - intros * ? ? ; split ; eauto.
      econstructor.
      1: now eapply prod_ty_inv.
      eapply typing_eta ; tea.
      all: now eapply prod_ty_inv.
    - intros * ? [] ; split ; gen_typing.
    - intros * ? [] ? [] ? [] ? []; split.
      + now eapply typing_subst1.
      + gen_typing.
      + eapply ty_conv.
        assert [Γ |-[de] tNat ≅ tNat] by now constructor.
        1: eapply ty_natElim; tea; eapply ty_conv; tea. 
        * eapply typing_subst1; tea; do 2 constructor; boundary.
        * eapply elimSuccHypTy_conv ; tea.
          now boundary.
        * symmetry; now eapply typing_subst1.
    - intros **; split; tea.
      eapply ty_natElim; tea; constructor; boundary.   
    - intros **.
      assert [Γ |- tSucc n : tNat] by now constructor.
      assert [Γ |- P[(tSucc n)..]] by now eapply typing_subst1.
      split; tea.
      2: eapply ty_simple_app.
      1,5: now eapply ty_natElim.
      2: tea.
      1: now eapply typing_subst1.
      replace (arr _ _) with (arr P P[tSucc (tRel 0)]⇑)[n..] by now bsimpl.
      eapply ty_app; tea.
    - intros * ? [] ? []; split.
      + now eapply typing_subst1.
      + gen_typing.
      + eapply ty_conv.
        assert [Γ |-[de] tEmpty ≅ tEmpty] by now constructor.
        1: eapply ty_emptyElim; tea; eapply ty_conv; tea. 
        * symmetry; now eapply typing_subst1.
    - intros * ??? [] ? []; split; tea.
      1: gen_typing.
      constructor; tea.
      eapply _stability1.
      3: symmetry; gen_typing.
      all: gen_typing.
    - intros ** ; prod_hyp_splitter.
      split.
      all: econstructor ; eauto.
      + econstructor ; tea.
        * eapply _stability1 ; [..|eassumption] ; eauto.
          now symmetry.
        * now econstructor.
        * econstructor ; tea.
          eapply typing_subst1 ; tea.
          now econstructor.
      + symmetry.
        econstructor ; eauto.
      + econstructor ; tea.
        * eapply _stability1 ; [..|eassumption] ; eauto.
          now symmetry.
        * now econstructor.
        * econstructor ; tea.
          eapply typing_subst1 ; tea.
      + symmetry.
        econstructor ; eauto.
    - intros.
      split ; eauto.
      econstructor.
      1-2: now eapply sig_ty_inv.
      all: now econstructor.
    - intros * ? []; split; tea.
      1: now eapply sig_ty_inv.
      all: gen_typing.
    - intros * ? _ ? _ ????; split; tea.
      now do 2 econstructor.
    - intros * ? []; split; tea.
      1: eapply typing_subst1; [gen_typing| now eapply sig_ty_inv].
      1: gen_typing.
      econstructor. 1: now econstructor.
      symmetry; eapply typing_subst1.
      1: now eapply TermFstCong.
      econstructor; now eapply sig_ty_inv.
    - intros * ? _ ? _ ????.
      assert [Γ |- tFst (tPair A B a b) : A] by now do 2 econstructor.
      assert [Γ |- tFst (tPair A B a b) ≅ a : A] by now econstructor.
      split.
      + eapply typing_subst1; tea.
      + now do 2 econstructor.
      + econstructor; tea.
        symmetry; eapply typing_subst1; tea.
        now econstructor.
    - intros; prod_hyp_splitter; split; tea; econstructor; tea.
      all: eapply wfTermConv; tea; now econstructor.
    - intros; prod_hyp_splitter; split.
      all: econstructor; tea.
      1: econstructor; tea; now eapply wfTermConv.
      symmetry; now econstructor.
    - intros; prod_hyp_splitter.
      assert [|- Γ] by gen_typing.
      assert [|- Γ,, A'] by now econstructor.
      split.
      1: eapply typing_subst2; tea; cbn; now rewrite 2!wk1_ren_on, 2!shift_one_eq.
      1: now econstructor.
      econstructor.
      1: econstructor; tea; try eapply wfTermConv; refold; tea.
      + eapply _stability ; tea.
        2: eapply _idElimMotiveCtxConv; tea; try now boundary + eapply ctx_refl.
        1,2: eapply idElimMotiveCtx; tea; now eapply wfTermConv.
      + eapply typing_subst2; tea.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
        now econstructor.
      + now econstructor.
      + symmetry; eapply typing_subst2; tea.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq; tea.
    - intros; prod_hyp_splitter.
      assert [|- Γ] by gen_typing.
      assert [Γ |- tRefl A' z : tId A x y].
      1:{
        econstructor.
        1: econstructor; tea; now econstructor.
        symmetry; econstructor; tea; etransitivity; tea; now symmetry.
      }
      split; tea.
      + eapply typing_subst2; tea.
        cbn; now rewrite 2!wk1_ren_on, 2!shift_one_eq.
      + econstructor; tea.
      + econstructor; tea.
        eapply typing_subst2; tea.
        2: now econstructor.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
        now econstructor.
    - intros * ? [] ? [].
      split ; gen_typing.
    - intros * ? [].
      split; gen_typing.
    - intros * ?[]?[].
      split; gen_typing.
  Qed.

  Corollary boundary_tm Γ A t : [Γ |- t : A] -> [Γ |- A].
  Proof.
    now intros ?%boundary.
  Qed.

  Corollary boundary_ty_conv_l Γ A B : [Γ |- A ≅ B] -> [Γ |- A].
  Proof.
    now intros ?%boundary.
  Qed.

  Corollary boundary_ty_conv_r Γ A B : [Γ |- A ≅ B] -> [Γ |- B].
  Proof.
    now intros ?%boundary.
  Qed.

  Corollary boundary_red_ty_r Γ A B : [Γ |- A ⤳* B] -> [Γ |- B].
  Proof.
    now intros ?%RedConvTyC%boundary.
  Qed.

  Corollary boundary_tm_conv_l Γ A t u : [Γ |- t ≅ u : A] -> [Γ |- t : A].
  Proof.
    now intros []%boundary.
  Qed.

  Corollary boundary_tm_conv_r Γ A t u : [Γ |- t ≅ u : A] -> [Γ |- u : A].
  Proof.
    now intros []%boundary.
  Qed.

  Corollary boundary_tm_conv_ty Γ A t u : [Γ |- t ≅ u : A] -> [Γ |- A].
  Proof.
    now intros []%boundary.
  Qed.

  Corollary boundary_red_tm_r Γ A t u : [Γ |- t ⤳* u : A] -> [Γ |- u : A].
  Proof.
    now intros []%RedConvTeC%boundary.
  Qed.

  Corollary boundary_red_tm_ty Γ A t u : [Γ |- t ⤳* u : A] -> [Γ |- A].
  Proof.
    now intros []%RedConvTeC%boundary.
  Qed.

End Boundary.

#[export] Hint Resolve
boundary_tm boundary_ty_conv_l boundary_ty_conv_r
boundary_tm_conv_l boundary_tm_conv_r boundary_tm_conv_ty
boundary_red_tm_l boundary_red_tm_r boundary_red_tm_ty
boundary_red_ty_r : boundary.

Lemma boundary_ctx_conv_l `{!TypingSubst (ta := de)} (Γ Δ : context) :
  [ |- Γ ≅ Δ] ->
  [|- Γ].
Proof.
  destruct 1.
  all: econstructor ; boundary.
Qed.

#[export] Hint Resolve boundary_ctx_conv_l : boundary.

Corollary conv_ctx_refl_l `{!TypingSubst (ta := de)} (Γ Δ : context) :
[ |- Γ ≅ Δ] ->
[|- Γ ≅ Γ].
Proof.
  intros.
  eapply ctx_refl ; boundary.
Qed.

Section Stability.
  Context `{!TypingSubst (ta := de)}.

  Lemma conv_well_subst (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [Γ |-s tRel : Δ].
  Proof.
    intros; eapply _conv_well_subst; tea; boundary.
  Qed.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- A].
  Let PTm (Γ : context) (A t : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- t : A].
  Let PTyEq (Γ : context) (A B : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- t ≅ u : A].

  Theorem stability : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    red; prod_splitter; intros; red;intros; eapply _stability; tea; boundary.
  Qed.


  #[global] Instance ConvCtxSym : Symmetric ConvCtx.
  Proof.
    intros Γ Δ.
    induction 1.
    all: constructor ; tea.
    eapply stability ; tea.
    now symmetry.
  Qed.

  Corollary conv_ctx_refl_r (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [|- Δ ≅ Δ].
  Proof.
    intros H.
    symmetry in H.
    now eapply ctx_refl ; boundary.
  Qed.

  #[global] Instance ConvCtxTrans : Transitive ConvCtx.
  Proof.
    intros Γ1 Γ2 Γ3 H1 H2.
    induction H1 in Γ3, H2 |- *.
    all: inversion H2 ; subst ; clear H2.
    all: constructor.
    1: eauto.
    etransitivity ; tea.
    now eapply stability.
  Qed.

End Stability.

Section TypingStronger.
  Context `{!TypingSubst (ta := de)}.

  Theorem stability1 (Γ : context) A A' :
    [Γ |- A ≅ A'] ->
    (forall (T : term), [Γ,, A' |-[de] T] -> [Γ,, A |-[de] T])
    × (forall (T t : term), [Γ,, A' |-[ de ] t : T] -> [Γ,, A |-[de] t : T])
    × (forall (T T' : term), [Γ,, A' |-[ de ] T ≅ T'] -> [Γ,, A |-[de] T ≅ T'])
    × (forall (T t u : term),
          [Γ,, A' |-[ de ] t ≅ u : T] -> [Γ,, A |-[de] t ≅ u : T]).
  Proof.
    intros.
    apply _stability1 ; tea.
    all: boundary.
  Qed.


  Lemma idElimMotiveCtxConv {Γ Γ' A A' x x'} :
    [|- Γ ≅ Γ'] ->
    [Γ |- A ≅ A'] ->
    [Γ |- x ≅ x' : A] ->
    [ |- (Γ',, A'),, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0) ≅ (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)].
  Proof.
    intros.
    assert [|- Γ] by boundary.
    assert [Γ |- A] by boundary.
    assert [Γ' |- A'].
    {
    eapply stability.
    2: now symmetry.
    now boundary.
    }
    apply _idElimMotiveCtxConv ; eauto.
    - constructor.
      1: constructor ; boundary.
      constructor.
      + eapply typing_wk.
        2: constructor.
        all: boundary.
      + eapply typing_wk.
        2: constructor.
        all: boundary.
      + rewrite wk1_ren_on.
        do 2 constructor.
        all: boundary.
    - constructor.
      1: econstructor ; boundary.
      constructor.
      + eapply typing_wk.
        2: constructor.
        all: boundary.
      + eapply typing_wk.
        2: econstructor ; boundary.
        eapply stability.
        2: now symmetry.
        econstructor ; tea.
        boundary.
      + rewrite wk1_ren_on.
        do 2 constructor.
        all: boundary.
  Qed.

  Lemma termGen' Γ t A :
    [Γ |- t : A] ->
    ∑ A', (termGenData Γ t A') × [Γ |- A' ≅ A].
  Proof.
    intros * H.
    destruct (_termGen _ _ _ H) as [? [? [->|]]].
    2: now eexists.
    eexists ; split ; tea.
    econstructor.
    boundary.
  Qed.

  Lemma typing_eta' (Γ : context) A B f :
    [Γ |- f : tProd A B] ->
    [Γ,, A |- eta_expand f : B].
  Proof.
    intros Hf.
    eapply typing_eta ; tea.
    - eapply prod_ty_inv.
      boundary.
    - eapply prod_ty_inv.
      boundary.
  Qed.

End TypingStronger.