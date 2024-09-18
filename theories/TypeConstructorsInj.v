(** * LogRel.TypeConstructorsInj: injectivity and no-confusion of type constructors, and many consequences, including subject reduction. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance.
From LogRel Require Import LogicalRelation Validity Fundamental DeclarativeSubst.
From LogRel.LogicalRelation Require Import Escape Irrelevance Neutral Induction NormalRed.
From LogRel.Substitution Require Import Escape Poly Reflexivity.

Set Printing Primitive Projection Parameters.

Import DeclarativeTypingProperties.

Section TypeConstructors.

  Definition type_hd_view (Γ : context) {T T' : term} (nfT : isType T) (nfT' : isType T') : Type :=
    match nfT, nfT' with
      | @UnivType s, @UnivType s' => s = s'
      | @ProdType A B, @ProdType A' B' => [Γ |- A' ≅ A] × [Γ,, A' |- B ≅ B']
      | NatType, NatType => True
      | EmptyType, EmptyType => True
      | NeType _, NeType _ => [Γ |- T ≅ T' : U]
      | @SigType A B, @SigType A' B' => [Γ |- A ≅ A'] × [Γ,, A |- B ≅ B']
      | @IdType A x y, @IdType A' x' y' => [× [Γ |- A' ≅ A], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]]
      | _, _ => False
    end.

  Lemma red_ty_complete : forall (Γ : context) (T T' : term),
    isType T ->
    [Γ |- T ≅ T'] ->
    ∑ T'', [Γ |- T' ⤳* T''] × isType T''.
  Proof.
    intros * tyT Hconv.
    eapply Fundamental in Hconv as [HΓ HT HT' Hconv].
    eapply reducibleTyEq in Hconv.
    set (HTred := reducibleTy _ HT) in *.
    clearbody HTred.
    clear HT.
    destruct HTred as [[] lr] ; cbn in *.
    destruct lr.
    all: destruct Hconv; eexists; split; [lazymatch goal with H : [_ |- _ :⤳*: _] |- _ => apply H end|]; constructor.
    eapply convneu_whne; now symmetry.
  Qed.

  Lemma ty_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
    [Γ |- T ≅ T'] ->
    type_hd_view Γ nfT nfT'.
  Proof.
    intros * Hconv.
    eapply Fundamental in Hconv as [HΓ HT HT' Hconv].
    eapply reducibleTyEq in Hconv.
    set (HTred := reducibleTy _ HT) in *.
    clearbody HTred.
    clear HT.
    eapply reducibleTy in HT'.
    revert nfT T' nfT' HΓ HT' Hconv.
    revert HTred.
    generalize (eq_refl : one = one).
    generalize one at 1 3; intros l eql HTred; revert eql.
    pattern l, Γ, T, HTred; apply LR_rect_TyUr; clear l Γ T HTred.
    all: intros ? Γ T.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = U) as HeqT' by (eapply redtywf_whnf ; gen_typing); subst.
      assert (T = U) as HeqU by (eapply redtywf_whnf ; gen_typing).
      destruct nfT ; inversion HeqU ; subst.
      2: now exfalso ; gen_typing.
      clear HeqU.
      remember U as T eqn:HeqU in nfT' |- * at 2.
      destruct nfT'; inversion HeqU ; subst.
      2: now exfalso ; gen_typing.
      now reflexivity.
    - intros [nT ? ne] -> nfT T' nfT' HΓ HT' [nT' ? ne']; cbn in *.
      assert (T = nT) as <- by
        (apply red_whnf ; gen_typing).
      assert (T' = nT') as <- by
        (apply red_whnf ; gen_typing).
      destruct nfT.
      1-6: apply convneu_whne in ne; inversion ne.
      destruct nfT'.
      1-6: symmetry in ne'; apply convneu_whne in ne'; inversion ne'.
      cbn. gen_typing.
    - intros [dom cod red] _ _ -> nfT T' nfT' HΓ HT'[dom' cod' red']; cbn in *.
      assert (T = tProd dom cod) as HeqT by (apply red_whnf ; gen_typing).
      assert (T' = tProd dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
      destruct nfT; cycle -1.
      1: subst ; exfalso ; gen_typing.
      all: try congruence.
      destruct nfT'; cycle -1.
      1: subst ; exfalso ; gen_typing.
      all: try congruence.
      inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
      destruct (polyRedEqId (normRedΠ0 (invLRΠ HT')) (PolyRedEqSym _ polyRed0)).
      split; now escape.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = tNat) as HeqT' by (eapply redtywf_whnf ; gen_typing).
      assert (T = tNat) as HeqT by (eapply redtywf_whnf ; gen_typing).
      destruct nfT; inversion HeqT.
      + destruct nfT'; inversion HeqT'.
        * constructor.
        * exfalso; subst; inversion w.
      + exfalso; subst; inversion w.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = tEmpty) as HeqT' by (eapply redtywf_whnf ; gen_typing).
      assert (T = tEmpty) as HeqT by (eapply redtywf_whnf ; gen_typing).
      destruct nfT; inversion HeqT.
      + destruct nfT'; inversion HeqT'.
        * econstructor.
        * exfalso; subst; inversion w.
      + exfalso; subst; inversion w.
    - intros [dom cod red] _ _ -> nfT T' nfT' HΓ HT' [dom' cod' red'].
      assert (T = tSig dom cod) as HeqT by (apply red_whnf ; gen_typing).
      assert (T' = tSig dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
      destruct nfT; cycle -1.
      1: subst; inv_whne.
      all: try congruence.
      destruct nfT'; cycle -1.
      1: subst; inv_whne.
      all: try congruence.
      inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
      eapply polyRedEqId in polyRed0 as [].
      split ; now escape.
    - intros [??? ty] _ _ -> nfT T' nfT' HΓ HT' [??? ty']; cbn in *.
      assert (T = ty) as HeqT by (apply red_whnf; gen_typing).
      assert (T' = ty') as HeqT' by (apply red_whnf; gen_typing).
      destruct nfT; cycle -1; [subst; inv_whne|..]; unfold ty in *; try congruence.
      destruct nfT'; cycle -1; [subst; inv_whne|..]; unfold ty' in *; try congruence.
      cbn; inversion HeqT; inversion HeqT'; subst; escape; now split.
  Qed.

  Corollary red_ty_compl_univ_l Γ T :
    [Γ |- U ≅ T] ->
    [Γ |- T ⤳* U].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT' as (T''&[? nfT]).
    2: econstructor.
    enough (T'' = U) as -> by easy.
    assert [Γ |- U ≅ T''] as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: econstructor.
    1: eassumption.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_ty_compl_univ_l' Γ T :
    whnf T ->
    [Γ |- U ≅ T] ->
    T = U.
  Proof.
    now intros ? ?%red_ty_compl_univ_l%redty_whnf.
  Qed.

  Corollary red_ty_compl_univ_r Γ T :
    [Γ |- T ≅ U] ->
    [Γ |- T ⤳* U].
  Proof.
    intros.
    eapply red_ty_compl_univ_l.
    now symmetry.
  Qed.

  Corollary red_ty_compl_univ_r' Γ T :
    whnf T ->
    [Γ |- T ≅ U ] ->
    T = U.
  Proof.
    intros ? ?%red_ty_compl_univ_r%redty_whnf.
    all: easy.
  Qed.

  Corollary red_ty_compl_nat_l Γ T :
    [Γ |- tNat ≅ T] ->
    [Γ |- T ⤳* tNat].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT' as (T''&[? nfT]).
    2: econstructor.
    enough (T'' = tNat) as -> by easy.
    assert [Γ |- tNat ≅ T''] as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: econstructor.
    1: eassumption.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_ty_compl_nat_l' Γ T :
    whnf T ->
    [Γ |- tNat ≅ T] ->
    T = tNat.
  Proof.
    intros ? ?%red_ty_compl_nat_l%redty_whnf.
    all: easy.
  Qed.

  Corollary red_ty_compl_nat_r Γ T :
    [Γ |- T ≅ tNat] ->
    [Γ |- T ⤳* tNat].
  Proof.
    intros.
    eapply red_ty_compl_nat_l.
    now symmetry.
  Qed.

  Corollary red_ty_compl_nat_r' Γ T :
    whnf T ->
    [Γ |- T ≅ tNat ] ->
    T = tNat.
  Proof.
    intros ? ?%red_ty_compl_nat_r%redty_whnf.
    all: easy.
  Qed.

  Corollary red_ty_compl_empty_l Γ T :
    [Γ |- tEmpty ≅ T] ->
    [Γ |- T ⤳* tEmpty].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT' as (T''&[? nfT]).
    2: econstructor.
    enough (T'' = tEmpty) as -> by easy.
    assert [Γ |- tEmpty ≅ T''] as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: econstructor.
    1: eassumption.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_ty_compl_empty_l' Γ T :
    whnf T ->
    [Γ |- tEmpty ≅ T] ->
    T = tEmpty.
  Proof.
    intros ? ?%red_ty_compl_empty_l%redty_whnf.
    all: easy.
  Qed.

  Corollary red_ty_compl_empty_r Γ T :
    [Γ |- T ≅ tEmpty] ->
    [Γ |- T ⤳* tEmpty].
  Proof.
    intros.
    eapply red_ty_compl_empty_l.
    now symmetry.
  Qed.

  Corollary red_ty_compl_empty_r' Γ T :
    whnf T ->
    [Γ |- T ≅ tEmpty] ->
    T = tEmpty.
  Proof.
    intros ? ?%red_ty_compl_empty_r%redty_whnf.
    all: easy.
  Qed.

  Corollary red_ty_compl_prod_l Γ A B T :
    [Γ |- tProd A B ≅ T] ->
    ∑ A' B', [× [Γ |- T ⤳* tProd A' B'], [Γ |- A' ≅ A] & [Γ,, A' |- B ≅ B']].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT as (T''&[? nfT]).
    2: econstructor.
    assert [Γ |- tProd A B ≅ T''] as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: constructor.
    1: assumption.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
  Qed.

  Corollary red_ty_compl_prod_l' Γ A B T :
    whnf T ->
    [Γ |- tProd A B ≅ T] ->
    ∑ A' B', [× T = tProd A' B', [Γ |- A' ≅ A] & [Γ,, A' |- B ≅ B']].
  Proof.
    intros ? (?&?&[->%redty_whnf])%red_ty_compl_prod_l.
    2: gen_typing.
    now do 2 eexists.
  Qed.

  Corollary prod_ty_inj Γ A B  A' B' :
    [Γ |- tProd A B ≅ tProd A' B'] ->
    [Γ |- A' ≅ A] × [Γ,, A' |- B ≅ B'].
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.

  Corollary red_ty_compl_sig_l Γ A B T :
    [Γ |- tSig A B ≅ T] ->
    ∑ A' B', [× [Γ |- T ⤳* tSig A' B'], [Γ |- A ≅ A'] & [Γ,, A |- B ≅ B']].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT as (T''&[? nfT]).
    2: econstructor.
    assert [Γ |- tSig A B ≅ T''] as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: constructor.
    1: assumption.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
  Qed.

  Corollary red_ty_compl_sig_r Γ A B T :
    [Γ |- T ≅ tSig A B] ->
    ∑ A' B', [× [Γ |- T ⤳* tSig A' B'], [Γ |- A' ≅ A] & [Γ,, A' |- B ≅ B']].
  Proof.
    intros ? (?&?&[->%redty_whnf])%red_ty_compl_sig_l.
    2: gen_typing.
    now do 2 eexists.
  Qed.

  Corollary sig_ty_inj Γ A B  A' B' :
    [Γ |- tSig A B ≅ tSig A' B'] ->
    [Γ |- A ≅ A'] × [Γ,, A |- B ≅ B'].
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.

  Corollary red_ty_compl_id_l Γ A x y T :
    [Γ |- tId A x y ≅ T] ->
    ∑ A' x' y', [× [Γ |- T ⤳* tId A' x' y'], [Γ |- A' ≅ A], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT as (T''&[? nfT]).
    2: econstructor.
    assert [Γ |- tId A x y ≅ T''] as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: constructor.
    1: assumption.
    destruct nfT, Hconv.
    do 3 eexists ; split; eassumption.
  Qed.

  Corollary red_ty_compl_id_r Γ A x y T :
    [Γ |- T ≅ tId A x y] ->
    ∑ A' x' y', [× [Γ |- T ⤳* tId A' x' y'], [Γ |- A' ≅ A], [Γ |- x' ≅ x : A] & [Γ |- y' ≅ y : A]].
  Proof.
    intros hconv.
    symmetry in hconv.
    eapply red_ty_compl_id_l in hconv as (?&?&?&[]).
    do 3 eexists ; now split.
  Qed.
  
  Corollary red_ty_compl_id_r' Γ A x y T :
    whnf T ->
    [Γ |- T ≅ tId A x y] ->
    ∑ A' x' y', [× T = tId A' x' y', [Γ |- A' ≅ A], [Γ |- x' ≅ x : A] & [Γ |- y' ≅ y : A]].
  Proof.
    intros ? (?&?&?&[->%redty_whnf])%red_ty_compl_id_r.
    2: gen_typing.
    do 3 eexists ; now split.
  Qed.

  Corollary id_ty_inj {Γ A A' x x' y y'} :
    [Γ |- tId A x y ≅ tId A' x' y'] ->
    [× [Γ |- A' ≅ A], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]].
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.

End TypeConstructors.

Section Boundary.

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
    intros;split; intros; eapply typing_subst; tea; now eapply scons2_well_subst.
  Qed.

  Lemma shift_subst_eq t a : t⟨↑⟩[a..] = t.
  Proof. now asimpl. Qed.

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

  Lemma idElimMotiveCtxConv {Γ Γ' A A' x x'} :
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
    eapply convCtxSym0; tea.
    econstructor.
    1: econstructor; tea; now eapply ctx_refl.
    erewrite (wk1_irr (t:=A')), (wk1_irr (t:=x')); econstructor.
    1,2: eapply typing_wk; tea; gen_typing.
    rewrite wk1_ren_on; eapply TermRefl; now eapply ty_var0.
  Qed.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := True.
  Let PTm (Γ : context) (A t : term) := [Γ |- A].
  Let PTyEq (Γ : context) (A B : term) := [Γ |- A] × [Γ |- B].
  Let PTmEq (Γ : context) (A t u : term) := [× [Γ |- A], [Γ |- t : A] & [Γ |- u : A]].

  Lemma boundary : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    red; prod_splitter; try now constructor.
    - intros Γ A t H; apply Fundamental in H as [? VA _].
      now eapply escapeTy.
    - intros Γ A B H; apply Fundamental in H as [? VA VB _]; split.
      + now eapply escapeTy.
      + now eapply escapeTy.
    - intros Γ A t u H; apply Fundamental in H as [? VA Vtu].
      pose proof (ureflValidTm Vtu).
      prod_splitter.
      + now eapply escapeTy.
      + now eapply escapeTm.
      + now eapply escapeTm.
  Qed.

End Boundary.

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

#[export] Hint Resolve
  boundary_tm boundary_ty_conv_l boundary_ty_conv_r
  boundary_tm_conv_l boundary_tm_conv_r boundary_tm_conv_ty
  boundary_red_tm_l boundary_red_tm_r boundary_red_tm_ty
  boundary_red_ty_r : boundary.

Lemma boundary_ctx_conv_l (Γ Δ : context) :
  [ |- Γ ≅ Δ] ->
  [|- Γ].
Proof.
  destruct 1.
  all: econstructor ; boundary.
Qed.

#[export] Hint Resolve boundary_ctx_conv_l : boundary.

Corollary conv_ctx_refl_l (Γ Δ : context) :
[ |- Γ ≅ Δ] ->
[|- Γ ≅ Γ].
Proof.
  intros.
  eapply ctx_refl ; boundary.
Qed.

Corollary red_ty_compl_prod_r Γ A B T :
  [Γ |- T ≅ tProd A B] ->
  ∑ A' B', [× [Γ |- T ⤳* tProd A' B'], [Γ |- A ≅ A'] & [Γ,, A |- B' ≅ B]].
Proof.
  intros HT.
  symmetry in HT.
  eapply red_ty_compl_prod_l in HT as (?&?&[HA ? HB]).
  do 2 eexists ; split ; tea.
  1: now symmetry.
  symmetry.
  eapply stability1 ; tea.
  1-2: now boundary.
  now symmetry.
Qed.

Corollary red_ty_compl_prod_r' Γ A B T :
  whnf T ->
  [Γ |- T ≅ tProd A B] ->
  ∑ A' B', [× T = tProd A' B', [Γ |- A ≅ A'] & [Γ,, A |- B' ≅ B]].
Proof.
  intros ? (?&?&[->%redty_whnf])%red_ty_compl_prod_r.
  2: gen_typing.
  now do 2 eexists.
Qed.

Corollary red_ty_compl_sig_r Γ A B T :
  [Γ |- T ≅ tSig A B] ->
  ∑ A' B', [× [Γ |- T ⤳* tSig A' B'], [Γ |- A' ≅ A] & [Γ,, A' |- B' ≅ B]].
Proof.
  intros HT.
  symmetry in HT.
  eapply red_ty_compl_sig_l in HT as (?&?&[HA ? HB]).
  do 2 eexists ; split ; tea.
  1: now symmetry.
  symmetry.
  eapply stability1 ; tea.
  1-2: now boundary.
  now symmetry.
Qed.

Corollary red_ty_compl_sig_r' Γ A B T :
  whnf T ->
  [Γ |- T ≅ tSig A B] ->
  ∑ A' B', [× T = tSig A' B', [Γ |- A' ≅ A] & [Γ,, A' |- B' ≅ B]].
Proof.
  intros ? (?&?&[->%redty_whnf])%red_ty_compl_sig_r.
  2: gen_typing.
  now do 2 eexists.
Qed.


Section Stability.

  Lemma conv_well_subst (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [Γ |-s tRel : Δ].
  Proof.
    intros; eapply conv_well_subst; tea; boundary.
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
    red; prod_splitter; intros; red;intros; eapply stability0; tea; boundary.
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

(** ** Generation *)

(** The generation lemma (the name comes from the PTS literature), gives a
stronger inversion principle on typing derivations, that give direct access
to the last non-conversion rule, and bundle together all conversions.

Note that because we do not yet know that [Γ |- t : T] implies [Γ |- T],
we cannot use reflexivity in the case where the last rule was not a conversion
one, and we get the slightly clumsy disjunction of either an equality or a
conversion proof. We get a better version of generation later on, once we have
this implication. *)

Definition termGenData (Γ : context) (t T : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× T = decl, [|- Γ]& in_ctx Γ n decl]
    | tProd A B =>  [× T = U, [Γ |- A : U] & [Γ,, A |- B : U]]
    | tLambda A t => ∑ B, [× T = tProd A B, [Γ |- A] & [Γ,, A |- t : B]]
    | tApp f a => ∑ A B, [× T = B[a..], [Γ |- f : tProd A B] & [Γ |- a : A]]
    | tSort _ => False
    | tNat => T = U
    | tZero => T = tNat
    | tSucc n => T = tNat × [Γ |- n : tNat]
    |  tNatElim P hz hs n =>
      [× T = P[n..], [Γ,, tNat |- P], [Γ |- hz : P[tZero..]], [Γ |- hs : elimSuccHypTy P] & [Γ |- n : tNat]]
    | tEmpty => T = U
    | tEmptyElim P e =>
      [× T = P[e..], [Γ,, tEmpty |- P] & [Γ |- e : tEmpty]]
    | tSig A B => [× T = U, [Γ |- A : U] & [Γ ,, A |- B : U]]
    | tPair A B a b =>
     [× T = tSig A B, [Γ |- A], [Γ,, A |- B], [Γ |- a : A] & [Γ |- b : B[a..]]]
    | tFst p => ∑ A B, T = A × [Γ |- p : tSig A B]
    | tSnd p => ∑ A B, T = B[(tFst p)..] × [Γ |- p : tSig A B]
    | tId A x y => [× T = U, [Γ |- A : U], [Γ |- x : A] & [Γ |- y : A]]
    | tRefl A x => [× T = tId A x x, [Γ |- A] & [Γ |- x : A]]
    | tIdElim A x P hr y e =>
      [× T = P[e .: y..], [Γ |- A], [Γ |- x : A], [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P], [Γ |- hr : P[tRefl A x .: x..]], [Γ |- y : A] & [Γ |- e : tId A x y]]
  end.

Lemma termGen Γ t A :
  [Γ |- t : A] ->
  ∑ A', (termGenData Γ t A') × ((A' = A) + [Γ |- A' ≅ A]).
Proof.
  induction 1.
  all: try (eexists ; split ; [..|left ; reflexivity] ; cbn ; by_prod_splitter).
  + destruct IHTypingDecl as [? [? [-> | ]]].
    * prod_splitter; tea; now right.
    * prod_splitter; tea; right; now eapply TypeTrans.
Qed.

Lemma neutral_ty_inv Γ A :
  [Γ |- A] -> whne A -> [Γ |- A : U].
Proof.
  intros Hty Hne.
  unshelve eapply TypeRefl, ty_conv_inj in Hty.
  - now constructor.
  - now constructor.
  - cbn in *.
    apply Fundamental in Hty; destruct Hty.
    now eapply escapeTm.
Qed.

Lemma prod_ty_inv Γ A B :
  [Γ |- tProd A B] ->
  [Γ |- A] × [Γ,, A |- B].
Proof.
  intros Hty.
  apply TypeRefl, prod_ty_inj in Hty as [HA HB].
  split; boundary.
Qed.

Lemma sig_ty_inv Γ A B :
  [Γ |- tSig A B] ->
  [Γ |- A] × [Γ,, A |- B].
Proof.
  intros Hty.
  apply TypeRefl, sig_ty_inj in Hty as [HA HB].
  split; boundary.
Qed.

Lemma id_ty_inv Γ A x y :
  [Γ |- tId A x y] ->
  [× [Γ |- A], [Γ |- x : A] & [Γ |- y : A]].
Proof.
  intros Hty.
  apply TypeRefl, id_ty_inj in Hty as [HA HB].
  prod_splitter; boundary.
Qed.

Lemma termGen' Γ t A :
[Γ |- t : A] ->
∑ A', (termGenData Γ t A') × [Γ |- A' ≅ A].
Proof.
intros * H.
destruct (termGen _ _ _ H) as [? [? [->|]]].
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

Theorem subject_reduction_one Γ A t t' :
    [Γ |- t : A] ->
    [t ⤳ t'] ->
    [Γ |- t ≅ t' : A].
Proof.
  intros Hty Hred.
  induction Hred in Hty, A |- *.
  - apply termGen' in Hty as (?&((?&?&[-> Hty])&Heq)).
    apply termGen' in Hty as (?&((?&[->])&Heq')).
    eapply prod_ty_inj in Heq' as [? HeqB].
    econstructor.
    1: econstructor ; gen_typing.
    etransitivity ; tea.
    eapply typing_subst1 ; tea.
    now econstructor.
  - apply termGen' in Hty as (?&((?&?&[->])&Heq)).
    econstructor ; tea.
    econstructor.
    + now eapply IHHred.
    + now econstructor.
  - apply termGen' in Hty as [?[[->]?]].
    econstructor; tea.
    econstructor.
    1-3: now econstructor.
    now eapply IHHred.
  - apply termGen' in Hty as [?[[->]?]].
    now do 2 econstructor.
  - apply termGen' in Hty as [?[[-> ???(?&[->]&?)%termGen']?]].
    now do 2 econstructor.
  - apply termGen' in Hty as [?[[->]?]].
    econstructor ; tea.
    econstructor.
    1: now econstructor.
    now eapply IHHred.
  - apply termGen' in Hty as [? [[?[?[->]]]]].
    eapply TermConv; tea ; refold.
    now econstructor.
  - apply termGen' in Hty as [?[[?[?[-> h]]]]].
    apply termGen' in h as [?[[->] u]].
    destruct (sig_ty_inj _ _ _ _ _ u).
    eapply TermConv; refold.
    1: econstructor ; tea.
    now etransitivity.
  - apply termGen' in Hty as [? [[?[?[->]]]]].
    eapply TermConv; tea ; refold.
    now econstructor.
  - apply termGen' in Hty as [?[[?[?[-> h]]]]].
    apply termGen' in h as [?[[->] u]].
    destruct (sig_ty_inj _ _ _ _ _ u).
    assert [Γ |- B[(tFst (tPair A0 B a b))..] ≅ A].
    1:{ etransitivity; tea. eapply typing_subst1; tea.
      eapply TermConv; refold. 2: now symmetry.
      eapply TermRefl; refold; gen_typing.
    }
    eapply TermConv; tea; refold.
    now econstructor.
  - apply termGen' in Hty as [? [[-> ????? h]]].
    apply termGen' in h as [? [[->] h']].
    pose proof h' as []%id_ty_inj.
    econstructor; tea.
    econstructor; tea.
    1: now econstructor.
    + eapply TermConv; refold; [etransitivity; tea|]; now symmetry.
    + eapply TermConv; refold; now symmetry.
  - apply termGen' in Hty as [? [[-> ????? h]]].
    econstructor; tea; econstructor; tea.
    all: now first [eapply TypeRefl |eapply TermRefl| eauto].
  Qed.


  Theorem subject_reduction_one_type Γ A A' :
  [Γ |- A] ->
  [A ⤳ A'] ->
  [Γ |- A ≅ A'].
Proof.
  intros Hty Hred.
  destruct Hred.
  all: inversion Hty ; subst ; clear Hty ; refold.
  all: econstructor.
  all: eapply subject_reduction_one ; tea.
  all: now econstructor.
Qed.

Theorem subject_reduction Γ t t' A :
  [Γ |- t : A] ->
  [t ⤳* t'] ->
  [Γ |- t ⤳* t' : A].
Proof.
  intros Hty Hr; split ; refold.
  - assumption.
  - assumption.
  - induction Hr.
    + now constructor.
    + eapply subject_reduction_one in o ; tea.
      etransitivity ; tea.
      eapply IHHr.
      now boundary.
Qed.

Theorem subject_reduction_type Γ A A' :
[Γ |- A] ->
[A ⤳* A'] ->
[Γ |- A ⤳* A'].
Proof.
  intros Hty Hr; split; refold.
  - assumption.
  - assumption.
  - induction Hr.
    + now constructor.
    + eapply subject_reduction_one_type in o ; tea.
      etransitivity ; tea.
      eapply IHHr.
      now boundary.
Qed.

Corollary subject_reduction_raw Γ t t' A :
[t ⤳* t'] ->
[Γ |-[de] t : A] ->
[Γ |-[de] t' : A].
Proof.
eintros Hty ?%subject_reduction ; tea.
boundary.
Qed.

Corollary subject_reduction_raw_ty Γ A A' :
[A ⤳* A'] ->
[Γ |-[de] A] ->
[Γ |-[de] A'].
Proof.
eintros Hty ?%subject_reduction_type ; tea.
boundary.
Qed.

Corollary conv_red_l Γ A A' A'' : [Γ |-[de] A' ≅ A''] -> [A' ⤳* A] -> [Γ |-[de] A ≅ A''].
Proof.
  intros Hconv **.
  etransitivity ; tea.
  symmetry.
  eapply RedConvTyC, subject_reduction_type ; tea.
  boundary.
Qed.

Lemma Uterm_isType Γ A :
  [Γ |-[de] A : U] ->
  whnf A ->
  isType A.
Proof.
  intros Hty Hwh.
  destruct Hwh.
  all: try solve [now econstructor].
  all: exfalso.
  all: eapply termGen' in Hty ; cbn in *.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ U] |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: try now cbn in Hconv.
Qed.

Lemma type_isType Γ A :
  [Γ |-[de] A] ->
  whnf A ->
  isType A.
Proof.
  intros [] ; refold; cycle -1.
  1: intros; now eapply Uterm_isType.
  all: econstructor.
Qed.

Lemma fun_isFun Γ A B t:
  [Γ |-[de] t : tProd A B] ->
  whnf t ->
  isFun t.
Proof.
  intros Hty Hwh.
  destruct Hwh.
  all: try now econstructor.
  all: eapply termGen' in Hty ; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tProd _ _] |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.


Lemma sig_isPair Γ A B t:
  [Γ |-[de] t : tSig A B] ->
  whnf t ->
  isPair t.
Proof.
  intros Hty Hwh.
  destruct Hwh.
  all: try now econstructor.
  all: eapply termGen' in Hty ; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tSig _ _] |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma nat_isNat Γ t:
  [Γ |-[de] t : tNat] ->
  whnf t ->
  isNat t.
Proof.
  intros Hty Hwh.
  destruct Hwh.
  all: try now econstructor.
  all: eapply termGen' in Hty ; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tNat] |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma empty_isEmpty Γ t:
  [Γ |-[de] t : tEmpty] ->
  whnf t ->
  whne t.
Proof.
  intros Hty Hwh.
  destruct Hwh ; try easy.
  all: eapply termGen' in Hty ; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tEmpty] |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma id_isId Γ t {A x y} :
  [Γ |-[de] t : tId A x y] ->
  whnf t ->
  isId t.
Proof.
  intros Hty wh; destruct wh.
  all: try now econstructor.
  all: eapply termGen' in Hty; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy; subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tId _ _ _] |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end; try econstructor.
  all: now cbn in Hconv.
Qed.

Lemma neutral_isNeutral Γ A t :
  [Γ |-[de] t : A] ->
  whne A ->
  whnf t ->
  whne t.
Proof.
  intros (?&Hgen&Hconv)%termGen' HwA Hwh.
  set (iA := NeType HwA).
  destruct Hwh ; cbn in * ; try easy.
  all: exfalso.
  all: prod_hyp_splitter.
  all: subst.
  all: unshelve eapply ty_conv_inj in Hconv ; tea.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

(** *** Lemmas to handle identity types *)


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

Lemma idElimMotiveCtxConv {Γ Γ' A A' x x'} :
[|- Γ ≅ Γ'] ->
[Γ |- A ≅ A'] ->
[Γ |- x ≅ x' : A] ->
[ |- (Γ',, A'),, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0) ≅ (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)].
Proof.
  intros.
  assert [|- Γ] by boundary.
  assert [Γ |- A] by boundary.
  assert [ |- (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)].
  {
    constructor.
    - constructor ; boundary.
    - constructor.
      + eapply typing_wk.
        2: constructor.
        all: boundary.
      + eapply typing_wk.
        2: constructor.
        all: boundary.
      + rewrite wk1_ren_on.
        do 2 constructor.
        all: boundary.
  }
  assert [Γ' |- A'].
  {
   eapply stability.
   2: now symmetry.
   now boundary.
  }
  assert [ |- (Γ',, A'),, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0)].
  {
    constructor.
    - econstructor.
      all: boundary.
    - constructor.
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
  }
  eapply convCtxSym0; tea.
  econstructor.
  1: econstructor; tea; now eapply ctx_refl.
  erewrite (wk1_irr (t:=A')), (wk1_irr (t:=x')) ; econstructor.
  1,2: eapply typing_wk; tea; gen_typing.
  rewrite wk1_ren_on; eapply TermRefl; now eapply ty_var0.
Qed.

Lemma idElimConv {Γ A x P hr y e A' x' P' hr' e' y' T A'' x'' y''}:
  well_typed (ta := de) Γ (tIdElim A x P hr y e) ->
  well_typed (ta := de) Γ (tIdElim A' x' P' hr' y' e') ->
  (forall T', [Γ |-[de] e : T'] -> [Γ |-[de] T ≅ T']) ->
  (forall T', [Γ |-[de] e' : T'] -> [Γ |-[de] T ≅ T']) ->
  [Γ |-[de] T ≅ tId A'' x'' y''] ->
  whnf T ->
  ∑ AT xT yT,
  [× T = tId AT xT yT,
    [Γ |-[de] A ≅ A'], [Γ |-[de] A ≅ AT], [Γ |-[de] A ≅ A''],
    [Γ |-[de] x ≅ x' : A], [Γ |-[de] x ≅ xT : A], [Γ |-[de] x ≅ x'' : A],
    [Γ |-[de] y ≅ y' : A], [Γ |-[de] y ≅ yT : A] & [Γ |-[de] y ≅ y'' : A]].
Proof.
  intros [? [? [[-> ????? he]]]%termGen'] [? [? [[-> ????? he']]]%termGen'] hty hty' htyconv ?.
  specialize (hty _ he) as (?&?&?&[-> ])%red_ty_compl_id_r'.
  2: gen_typing.
  specialize (hty' _ he') as []%id_ty_inj ; tea.
  eapply id_ty_inj in htyconv as [].
  do 3 eexists ; split.
  1: reflexivity.
  - etransitivity ; now symmetry.
  - now symmetry.
  - etransitivity ; now symmetry.
  - etransitivity ; symmetry ; tea ; symmetry ; now econstructor.
  - now symmetry.
  - etransitivity ; symmetry ; tea ; symmetry ; now econstructor.
  - etransitivity ; symmetry ; tea ; symmetry ; now econstructor.
  - now symmetry.
  - etransitivity ; symmetry ; tea ; symmetry ; now econstructor.
Qed.