(** * LogRel.TypeConstructorsInj: injectivity and no-confusion of type constructors, and many consequences, including subject reduction. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All DeclarativeTyping GenericTyping.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences.

Set Printing Primitive Projection Parameters.

Import WeakDeclarativeTypingProperties.

(** ** Direct consequences of type constructors injectivity *)
(** Various specialized and easy-to-use versions of the general theorem. *)

Section TypeConstructors.
  Context `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.

  Corollary conv_univ_l Γ T :
    isType T ->
    [Γ |- U ≅ T] ->
    T = U.
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_compl_univ_l Γ T :
    [Γ |- U ≅ T] ->
    [Γ |- T ⤳* U].
  Proof.
    intros [? [T' []]%red_ty_complete_l]%dup.
    2: now gen_typing.
    enough (T' = U) as -> by easy.
    eapply conv_univ_l ; eauto.
    etransitivity ; [eassumption|now eapply RedConvTyC].
  Qed.

  Corollary conv_univ_r Γ T :
    isType T ->
    [Γ |- T ≅ U ] ->
    T = U.
  Proof.
    intros.
    eapply conv_univ_l ; eauto.
    now symmetry.
  Qed.

  Corollary red_compl_univ_r Γ T :
    [Γ |- T ≅ U] ->
    [Γ |- T ⤳* U].
  Proof.
    intros.
    eapply red_compl_univ_l.
    now symmetry.
  Qed.

  Corollary conv_nat_l Γ T :
    isType T ->
    [Γ |- tNat ≅ T] ->
    T = tNat.
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_compl_nat_l Γ T :
    [Γ |- tNat ≅ T] ->
    [Γ |- T ⤳* tNat].
  Proof.
    intros [? [T' []]%red_ty_complete_l]%dup.
    2: now gen_typing.
    enough (T' = tNat) as -> by easy.
    eapply conv_nat_l ; eauto.
    etransitivity ; [eassumption|now eapply RedConvTyC].
  Qed.

  Corollary conv_nat_r Γ T :
    isType T ->
    [Γ |- T ≅ tNat] ->
    T = tNat.
  Proof.
    intros.
    eapply conv_nat_l ; eauto.
    now symmetry.
  Qed.

  Corollary red_compl_nat_r Γ T :
    [Γ |- T ≅ tNat] ->
    [Γ |- T ⤳* tNat].
  Proof.
    intros.
    eapply red_compl_nat_l.
    now symmetry.
  Qed.

  Corollary conv_empty_l Γ T :
    isType T ->
    [Γ |- tEmpty ≅ T] ->
    T = tEmpty.
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_compl_empty_l Γ T :
    [Γ |- tEmpty ≅ T] ->
    [Γ |- T ⤳* tEmpty].
  Proof.
    intros [? [T' []]%red_ty_complete_l]%dup.
    2: now gen_typing.
    enough (T' = tEmpty) as -> by easy.
    eapply conv_empty_l ; eauto.
    etransitivity ; [eassumption|now eapply RedConvTyC].
  Qed.

  Corollary conv_empty_r Γ T :
    isType T ->
    [Γ |- T ≅ tEmpty] ->
    T = tEmpty.
  Proof.
    intros.
    eapply conv_empty_l ; eauto.
    now symmetry.
  Qed.

  Corollary red_compl_empty_r Γ T :
    [Γ |- T ≅ tEmpty] ->
    [Γ |- T ⤳* tEmpty].
  Proof.
    intros.
    eapply red_compl_empty_l.
    now symmetry.
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

  Corollary conv_prod_l Γ A B T :
    isType T ->
    [Γ |- tProd A B ≅ T] ->
    ∑ A' B', [× T = tProd A' B', [Γ |- A' ≅ A] & [Γ,, A' |- B ≅ B']].
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    eauto.
  Qed.

  Corollary red_compl_prod_l Γ A B T :
    [Γ |- tProd A B ≅ T] ->
    ∑ A' B', [× [Γ |- T ⤳* tProd A' B'], [Γ |- A' ≅ A] & [Γ,, A' |- B ≅ B']].
  Proof.
    intros [? [T' [? nfT]]%red_ty_complete_l]%dup.
    2: now gen_typing.
    assert [Γ |- tProd A B ≅ T'] as Hconv by 
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
  Qed.

  Corollary conv_prod_r Γ A B T :
    isType T ->
    [Γ |- T ≅ tProd A B] ->
    ∑ A' B', [× T = tProd A' B', [Γ |- A ≅ A'] & [Γ,, A |- B' ≅ B]].
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    eauto.
  Qed.

  Corollary red_compl_prod_r Γ A B T :
    [Γ |- T ≅ tProd A B] ->
    ∑ A' B', [× [Γ |- T ⤳* tProd A' B'], [Γ |- A ≅ A'] & [Γ,, A |- B' ≅ B]].
  Proof.
    intros [? [T' [? nfT]]%red_ty_complete_r]%dup.
    2: now gen_typing.
    assert [Γ |- T' ≅ tProd A B] as Hconv by 
      (etransitivity ; [now eapply TypeSym, RedConvTyC|eassumption]).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
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

  Corollary conv_sig_l Γ A B T :
    isType T ->
    [Γ |- tSig A B ≅ T] ->
    ∑ A' B', [× T = tSig A' B', [Γ |- A ≅ A'] & [Γ,, A |- B ≅ B']].
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    eauto.
  Qed.

  Corollary red_compl_sig_l Γ A B T :
    [Γ |- tSig A B ≅ T] ->
    ∑ A' B', [× [Γ |- T ⤳* tSig A' B'], [Γ |- A ≅ A'] & [Γ,, A |- B ≅ B']].
  Proof.
    intros [? [T' [? nfT]]%red_ty_complete_l]%dup.
    2: now gen_typing.
    assert [Γ |- tSig A B ≅ T'] as Hconv by 
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
  Qed.

  Corollary conv_sig_r Γ A B T :
    isType T ->
    [Γ |- T ≅ tSig A B] ->
    ∑ A' B', [× T = tSig A' B', [Γ |- A' ≅ A] & [Γ,, A' |- B' ≅ B]].
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    eauto.
  Qed.

  Corollary red_compl_sig_r Γ A B T :
    [Γ |- T ≅ tSig A B] ->
    ∑ A' B', [× [Γ |- T ⤳* tSig A' B'], [Γ |- A' ≅ A] & [Γ,, A' |- B' ≅ B]].
  Proof.
    intros [? [T' [? nfT]]%red_ty_complete_r]%dup.
    2: now gen_typing.
    assert [Γ |- T' ≅ tSig A B] as Hconv by 
      (etransitivity ; [now eapply TypeSym, RedConvTyC|eassumption]).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
  Qed.

  Corollary id_ty_inj {Γ A A' x x' y y'} :
    [Γ |- tId A x y ≅ tId A' x' y'] ->
    [× [Γ |- A ≅ A'], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]].
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.

  Corollary conv_id_l Γ A x y T :
    isType T ->
    [Γ |- tId A x y ≅ T] ->
    ∑ A' x' y', [× T = tId A' x' y', [Γ |- A ≅ A'], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]].
  Proof.
    unshelve eintros nfT [? Hconv%ty_conv_inj]%dup.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    repeat esplit ; eauto.
  Qed.

  Corollary red_compl_id_l Γ A x y T :
    [Γ |- tId A x y ≅ T] ->
    ∑ A' x' y', [× [Γ |- T ⤳* tId A' x' y'], [Γ |- A ≅ A'], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]].
  Proof.
    intros [? [T' [? nfT]]%red_ty_complete_l]%dup.
    2: now gen_typing.
    assert [Γ |- tId A x y ≅ T'] as Hconv by 
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now gen_typing.
    destruct nfT, Hconv.
    do 3 eexists ; split.
    all: eassumption.
  Qed.

  Corollary conv_id_r Γ A x y T :
    isType T ->
    [Γ |- T ≅ tId A x y] ->
    ∑ A' x' y', [× T = tId A' x' y', [Γ |- A' ≅ A], [Γ |- x' ≅ x : A] & [Γ |- y' ≅ y : A]].
  Proof.
    intros ? Hconv.
    symmetry in Hconv.
    eapply conv_id_l in Hconv as (?&?&?&[->]) ; eauto.
    do 3 eexists ; now split.
  Qed.
  
  Corollary red_compl_id_r Γ A x y T :
    [Γ |- T ≅ tId A x y] ->
    ∑ A' x' y', [× [Γ |- T ⤳* tId A' x' y'], [Γ |- A' ≅ A], [Γ |- x' ≅ x : A] & [Γ |- y' ≅ y : A]].
  Proof.
    intros hconv.
    symmetry in hconv.
    eapply red_compl_id_l in hconv as (?&?&?&[]).
    do 3 eexists ; now split.
  Qed.

End TypeConstructors.


(** ** Subject reduction *)

Section SubjectReduction.

  Context `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.

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
      + now econstructor. 
      + now econstructor.
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

End SubjectReduction.

(** ** Classification of weak-head normal forms *)

(** Characterizes the possible weak-head normal forms at a given type. *)

Section WhClassification.
  Context `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.


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

  Lemma isType_ty Γ T t :
    [Γ |-[de] t : T] ->
    isType t ->
    isCanonical t ->
    [Γ |-[de] U ≅ T].
  Proof.
    intros Hty HisT Hcan.
    all: inversion HisT ; subst ; clear HisT ; cycle -1.
    1: now edestruct can_whne_exclusive.
    all: eapply termGen' in Hty as (?&[]&?); subst.
    all: eassumption.
  Qed.

End WhClassification.

Lemma idElimConv {Γ A x P hr y e A' x' P' hr' e' y' T A'' x'' y''}
  `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}:
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
  specialize (hty _ he) as (?&?&?&[-> ])%conv_id_r.
  2: now eapply type_isType ; boundary.
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