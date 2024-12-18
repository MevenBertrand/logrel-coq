(** * LogRel.DeclarativeSubst: stability of declarative typing by substitution. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance.
From LogRel Require Import LogicalRelation Validity Fundamental.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Transitivity.
From LogRel.Substitution Require Import Properties Irrelevance.

(** Currently, this is obtained as a consequence of the fundamental lemma.
However, it could be alternatively proven much earlier, by a direct induction. *)

Set Printing Primitive Projection Parameters.

Import DeclarativeTypingProperties.

Lemma typing_subst : WfDeclInductionConcl
  (fun _ => True)
  (fun Γ A => forall Δ σ, [|- Δ] -> [Δ |-s σ : Γ] -> [Δ |- A[σ]])
  (fun Γ A t => forall Δ σ, [|- Δ] -> [Δ |-s σ : Γ] -> [Δ |- t[σ] : A[σ]])
  (fun Γ A B => forall Δ σ σ', [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] -> [Δ |- A[σ] ≅ B[σ']])
  (fun Γ A t u => forall Δ σ σ', [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] -> [Δ |- t[σ] ≅ u[σ'] : A[σ]]).
Proof.
  unshelve (repeat split ; [shelve|..]).
  - intros Γ ? Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst in Hσ as [].
    1,3: boundary.
    apply Fundamental in Ht as [VΓ [VA _]].
    unshelve eapply escape, VA ; tea.
    unshelve eapply irrelevanceSubst ; eassumption.
  - intros * Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst in Hσ as [].
    1,3: boundary.
    apply Fundamental in Ht as [VΓ [VA] [Vt]].
    unshelve eapply escapeTerm, Vt ; tea.
    unshelve eapply irrelevanceSubst ; eassumption.
  - intros * Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst_conv in Hσ as [].
    1,3: boundary.
    apply Fundamental in Ht as [VΓ VA ? Vconv] ; cbn in *.
    unshelve eapply escapeEq.
    2: unshelve eapply VA ; tea ; irrValid.
    cbn.
    unshelve eapply transEq.
    4: now apply Vconv.
    2-3: unshelve eapply VB ; tea.
    eapply urefl; now eapply irrelevanceSubstEq.
  - intros * Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst_conv in Hσ as [].
    1,3: boundary.
    apply Fundamental in Ht as [VΓ VA Vtu] ; cbn in *.
    unshelve eapply escapeEqTerm.
    2: now unshelve eapply VA ; tea ; irrValid.
    cbn. unshelve eapply Vtu.
Qed.


Section MoreSubst.

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
    all: eapply typing_subst ; tea.
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
    all: eapply typing_subst ; tea.
    all: econstructor ; cbn ; refold; bsimpl; try rewrite <- rinstInst'_term; tea.
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

  Theorem stability1 (Γ : context) A A' :
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
    all: eapply typing_subst in Hty ; tea.
    all: repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: eassumption.
  Qed.

End MoreSubst.

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
  eapply typing_subst.
  - now eapply HP.
  - boundary.
  - econstructor.
    + bsimpl.
      eapply well_subst_ext.
      2: eapply well_subst_up.
      3: eapply id_subst ; tea.
      2: now econstructor.
      now bsimpl.
    + cbn.
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

Lemma conv_well_subst (Γ Δ : context) :
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

(* Stability and symmetry with redundant hypothesis on the well-formed contexts *)

Section Stability0.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- A].
  Let PTm (Γ : context) (A t : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- t : A].
  Let PTyEq (Γ : context) (A B : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ,
    [|-Δ] -> [|- Δ ≅ Γ] -> [Δ |- t ≅ u : A].

  Theorem stability0 : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    red; prod_splitter; intros Γ * Hty; red.
    1: easy.
    all: intros ?? Hconv; eapply (conv_well_subst _) in Hconv ; tea.
    all: pose proof (Hconv' := Hconv); apply  subst_refl in Hconv'.
    all: eapply typing_subst in Hty; tea.
    all: repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: eassumption.
  Qed.

  Definition convCtxSym0 {Γ Δ} : [|- Δ] -> [|-Γ] -> [|- Δ ≅ Γ] -> [|- Γ ≅ Δ].
  Proof.
    induction 3.
    all: constructor; inversion H; inversion H0; subst; refold.
    1: now eauto.
    eapply stability0 ; tea.
    1: now symmetry.
    now eauto.
  Qed.

End Stability0.