(** * LogRel.DeclarativeNeutralConv: declarative neutral conversion, and proof of its completeness for conversion of neutrals. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance.
From LogRel Require Import DeclarativeSubst TypeConstructorsInj.

Set Printing Primitive Projection Parameters.

Import DeclarativeTypingData.

Section NeutralConversion.

  Disable Notation "[ _ |- _ ~ _ : _ ]" : typing_scope.

  Inductive DeclNeutralConversion (Γ : context) : term -> term -> term -> Type :=

  | neuConvRel T n : [|- Γ] -> in_ctx Γ n T -> [Γ |- tRel n ~ tRel n : T]

  | neuConvApp A B n n' a a' :
      [Γ |- n ~ n' : tProd A B] ->
      [Γ |- a ≅ a' : A] ->
      [Γ |- tApp n a ~ tApp n' a' : B[a..]]

  | neuConvNat {P P' hz hz' hs hs' n n'} :
      [Γ |- n ~ n' : tNat] ->
      [Γ ,, tNat |- P ≅ P'] ->
      [Γ |- hz ≅ hz' : P[tZero..]] ->
      [Γ |- hs ≅ hs' : elimSuccHypTy P] ->
      [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' : P[n..]]

  | neuConvEmpty {P P' e e'} :
      [Γ ,, tEmpty |- P ≅ P'] ->
      [Γ |- e ~ e' : tEmpty] ->
      [Γ |- tEmptyElim P e ~ tEmptyElim P' e' : P[e..]]

  | neuConvFst {A B p p'} :
      [Γ |- p ~ p' : tSig A B] ->
      [Γ |- tFst p ~ tFst p' : A]

  | neuConvSnd {A B p p'} :
      [Γ |- p ~ p' : tSig A B] ->
      [Γ |- tSnd p ~ tSnd p' : B[(tFst p)..]]

  | neuConvId {A A' x x' P P' hr hr' y y' e e'} :
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'] ->
      [Γ |- hr ≅ hr' : P[tRefl A x .: x..]] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- e ~ e' : tId A x y] ->
      [Γ |- tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e' : P[e .: y..]]

  | neuConvConv {A B n n'} :
      [Γ |- n ~ n' : A] ->
      [Γ |- A ≅ B] ->
      [Γ |- n ~ n' : B]

  where "[ Γ |- m ~ n : A ]" := (DeclNeutralConversion Γ A m n).

End NeutralConversion.

#[local] Instance ConvNeuConv_Decl : ConvNeuConv de := DeclNeutralConversion.

Ltac fold_neu :=
  change DeclNeutralConversion with (conv_neu_conv (ta := de) (ConvNeuConv := ConvNeuConv_Decl)) in *.

Smpl Add fold_neu : refold.

Lemma conv_neu_wk Γ Δ (ρ : Δ ≤ Γ) A m n :
  [|- Δ] ->
  [Γ |- m ~ n : A] ->
  [Δ |- m⟨ρ⟩ ~ n ⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros HΔ.
  induction 1 ; eauto.
  - econstructor ; eauto.
    now eapply in_ctx_wk.
  - cbn in * ; eapply convne_meta_conv.
    3: reflexivity.
    1: econstructor ; eauto.
    2: now bsimpl.
    now eapply typing_wk.
    
  - erewrite (subst_ren_wk_up (A := tNat)).
    econstructor ; eauto.
    + erewrite <- !(wk_up_ren_on _ _ _ tNat).
      eapply typing_wk ; eauto.
      econstructor ; cbn ; eauto.
      now econstructor.
    + eapply convtm_meta_conv.
      1: eapply typing_wk ; eauto.
      all: now bsimpl.
    + eapply convtm_meta_conv.
      1: eapply typing_wk ; eauto.
      all: unfold elimSuccHypTy ; now bsimpl.
  
  - erewrite subst_ren_wk_up.
    econstructor ; eauto.
    erewrite <- !(wk_up_ren_on _ _ _ tEmpty).
    eapply typing_wk ; eauto.
    econstructor ; cbn ; eauto.
    now econstructor.

  - now econstructor.

  - cbn in * ; eapply convne_meta_conv.
    1: now econstructor.
    all: now bsimpl.

  - rewrite <- ! wk_idElim.
    assert [|- Δ ,, A⟨ρ⟩] by (constructor; tea; eapply typing_wk ; boundary).
    cbn in * ; eapply convne_meta_conv.
    1: econstructor ; eauto.
    all: try solve [now eapply typing_wk].
    + rewrite 2!(wk_up_wk1 ρ).
      eapply typing_wk ; eauto.
      change (up_ren ρ) with (wk_up A ρ :> nat -> nat).
      econstructor ; tea ; econstructor.
      * rewrite <- wk_up_wk1, wk_step_wk1; eapply typing_wk ; boundary.
      * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; now eapply typing_wk ; boundary.
      * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
    + eapply convtm_meta_conv.
      1: now eapply typing_wk.
      2: reflexivity.
      now bsimpl.
    + now bsimpl.
    + now bsimpl.
  
  - econstructor ; eauto.
    now eapply typing_wk.

Qed.

Lemma conv_neu_sound Γ A m n :
  [Γ |- m ~ n : A] ->
  [Γ |- m ≅ n : A].
Proof.
  induction 1 ; econstructor ; eauto.
  - now econstructor.
  - boundary.
  - boundary.
Qed.

Lemma conv_neu_ne Γ A m n :
  [Γ |- m ~ n : A] ->
  whne m × whne n.
Proof.
  induction 1 ; eauto ; split ; econstructor ; now prod_hyp_splitter.
Qed.

Definition neuGenData (Γ : context) (T t t' : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× t' = tRel n, [|- Γ], in_ctx Γ n decl & [Γ |- decl ≅ T]]
    | tApp f a => ∑ A B f' a',
        [× t' = tApp f' a', [Γ |- f ~ f' : tProd A B], [Γ |- a ≅ a' : A] & [Γ |- B[a..] ≅ T]]
    | tNatElim P hz hs n => ∑ P' hz' hs' n',
      [× t' = tNatElim P' hz' hs' n',
        [Γ,, tNat |- P ≅ P'], [Γ |- hz ≅ hz' : P[tZero..]], [Γ |- hs ≅ hs' : elimSuccHypTy P],
        [Γ |- n ~ n' : tNat] & [Γ |- P[n..] ≅ T]]
    | tEmptyElim P e => ∑ P' e',
      [× t' = tEmptyElim P' e', [Γ,, tEmpty |- P ≅ P'], [Γ |- e ~ e' : tEmpty] & [Γ |- P[e..] ≅ T]]
    | tFst p => ∑ A B p', [× t' = tFst p', [Γ |- p ~ p' : tSig A B] & [Γ |- A ≅ T]]
    | tSnd p => ∑ A B p', [× t' = tSnd p', [Γ |- p ~ p' : tSig A B] & [Γ |- B[(tFst p)..] ≅ T ]]
    | tIdElim A x P hr y e => ∑ A' x' P' hr' y' e',
      [× t' = tIdElim A' x' P' hr' y' e',
        [Γ |- A ≅ A'], [Γ |- x ≅ x' : A], [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'],
        [Γ |- hr ≅ hr' : P[tRefl A x .: x..]], [Γ |- y ≅ y' : A], [Γ |- e ~ e' : tId A x y]
        & [Γ |- P[e .: y..] ≅ T]]
    | _ => False
  end.

Lemma neuConvGen Γ T t t' :
  [Γ |- t ~ t' : T] ->
  neuGenData Γ T t t'.
Proof.
  induction 1 ; cbn ; repeat esplit ; eauto.
  - econstructor.
    now eapply in_ctx_wf.
  - econstructor.
    eapply typing_subst1.
    1: boundary.
    eapply prod_ty_inv.
    eauto using conv_neu_sound with boundary.
  - econstructor.
    eapply typing_subst1.
    all: eauto using conv_neu_sound with boundary.
  - econstructor.
    eapply typing_subst1.
    all: eauto using conv_neu_sound with boundary.
  - econstructor.
    eapply sig_ty_inv.
    eauto using conv_neu_sound with boundary. 
  - econstructor.
    eapply typing_subst1.
    1: econstructor.
    2: eapply sig_ty_inv.
    all: eauto using conv_neu_sound with boundary.
  - econstructor.
    eapply typing_subst2 ; last first.
    + boundary.
    + cbn.
      eapply typing_meta_conv.
      1: eauto using conv_neu_sound with boundary.
      now bsimpl.
    + boundary.
    + boundary.
  - destruct n ; cbn in * ; eauto.
    all: prod_hyp_splitter ; subst.
    all: repeat esplit ; eauto.
    all: now eapply TypeTrans.
Qed.

Lemma conv_neu_refl Γ A n :
  whne n ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A].
Proof.
  intros wn Hty.
  induction wn in A, Hty |- *.
  all: eapply termGen' in Hty ; cbn in * ; prod_hyp_splitter ; subst.
  all: eapply neuConvConv ; tea.
  all: econstructor ; eauto.
  all: now econstructor.
Qed.

Lemma conv_neu_sym Γ A m n :
  [Γ |- m ~ n : A] ->
  [Γ |- n ~ m : A].
Proof.
  induction 1 ; cbn in * ; refold.
  
  - now econstructor.

  - assert [Γ |- a' ≅ a : A] by now eapply TermSym.
    econstructor.
    1: econstructor ; eauto.
    eapply typing_subst1 ; eauto.
    constructor.
    eapply prod_ty_inv.
    eauto using conv_neu_sound with boundary.

  - econstructor.
    1: econstructor ; eauto.
    + now eapply TypeSym.
    + econstructor.
      1: now eapply TermSym.
      eapply typing_subst1 ; tea.
      do 2 constructor.
      boundary.
    + eapply TermConv ; refold.
      1: now eapply TermSym.
      eapply elimSuccHypTy_conv ; boundary.
    + eapply TypeSym, typing_subst1 ; eauto using conv_neu_sound.
  
  - econstructor.
    1: econstructor ; eauto.
    + now eapply TypeSym.
    + eapply TypeSym, typing_subst1 ; eauto using conv_neu_sound.

  - now econstructor.
  
  - econstructor.
    1: econstructor ; eauto.
    eapply typing_subst1.
    + econstructor.
      eapply TermSym.
      now eapply conv_neu_sound.
    + econstructor.
      eapply sig_ty_inv.
      eauto using conv_neu_sound with boundary.
  
  - assert [Γ |- A' ≅ A] by now eapply TypeSym.
    assert [Γ |- x' ≅ x : A'] by
      (econstructor ; tea ; now eapply TermSym).
    assert [|- Γ,, A'] by (econstructor ; now boundary).
    econstructor.
    1: econstructor ; eauto with boundary.
    + eapply TypeSym.
      eapply stability ; eauto.
      econstructor.
      1: econstructor ; eauto using ctx_refl with boundary.
      econstructor.
      * erewrite (wk1_irr (A := A)).
        now eapply typing_wk.
      * erewrite (wk1_irr (A := A)).
        now eapply typing_wk.
      * do 2 econstructor ; eauto.
        rewrite wk1_ren_on.
        now econstructor.
    + econstructor.
      1: now eapply TermSym.
      eapply typing_subst2 ; eauto with boundary.
      econstructor ; cbn in *.
      1: now econstructor.
      replace (tId _[_] _[_] _) with (tId A x x) by now bsimpl.
      do 2 econstructor ; boundary.
    + econstructor ; tea.
      now econstructor.
    + econstructor ; tea.
      now econstructor.
    + eapply TypeSym ; refold.
      eapply typing_subst2 ; eauto with boundary.
      cbn.
      eapply convtm_meta_conv ; eauto using conv_neu_sound.
      now bsimpl.

  - econstructor ; eauto.

Qed.

Lemma conv_neu_typing Γ T T' n n' :
  [Γ |- n ~ n' : T] ->
  [Γ |- n' : T'] ->
  [Γ |- T ≅ T'].
Proof.
  intros Hconv Hty.
  induction Hconv in T', Hty |- *.
  
  - eapply termGen' in Hty as [? [[]]]. 
    prod_hyp_splitter ; subst.
    eapply in_ctx_inj in i ; [..|eassumption] ; subst.
    assumption.
  
  - eapply termGen' in Hty as [? [(?&?&[-> []%IHHconv%prod_ty_inj])]].
    eapply TypeTrans ; tea.
    eapply typing_subst1.
    2: eassumption.
    econstructor ; eauto.
    now eapply TypeSym.

  - eapply termGen' in Hty as [? [[->]]].
    eapply TypeTrans ; tea.
    eapply typing_subst1 ; tea.
    now eapply conv_neu_sound.

  - eapply termGen' in Hty as [? [[->]]].
    eapply TypeTrans ; tea.
    eapply typing_subst1 ; tea.
    now eapply conv_neu_sound.

  - eapply termGen' in Hty as [? [(?&?&[-> []%IHHconv%sig_ty_inj])]].
    now eapply TypeTrans.

  - eapply termGen' in Hty as [? [(?&?&[-> []%IHHconv%sig_ty_inj])]].
    eapply TypeTrans ; tea.
    eapply typing_subst1.
    2: eassumption.
    econstructor ; eauto.
    now eapply conv_neu_sound.

  - eapply termGen' in Hty as [? [[->]]] ; refold.
    eapply TypeTrans ; tea.
    eapply typing_subst2 ; tea.
    1: boundary.
    cbn.
    eapply convtm_meta_conv.
    1: now eapply conv_neu_sound.
    all: now bsimpl.

  - eapply TypeTrans ; refold ; eauto.
    now eapply TypeSym.

Qed.


Lemma conv_neu_trans Γ A n1 n2 n3 :
  [Γ |- n1 ~ n2 : A] ->
  [Γ |- n2 ~ n3 : A] ->
  [Γ |- n1 ~ n3 : A].
Proof.
  intros H H'.
  induction H in n3, H' |- *.
  1-7: eapply neuConvGen in H' ; cbn in * ; refold ; prod_hyp_splitter ; subst.
  - now econstructor.
  - eapply conv_neu_typing in H.
    2: clear H ; eauto using conv_neu_sound with boundary.
    econstructor ; eauto.
    + eapply IHDeclNeutralConversion.
      econstructor ; eauto.
      now apply TypeSym.
    + eapply TermTrans ; eauto.
      econstructor ; tea.
      now eapply prod_ty_inj in H.
  - econstructor ; eauto.
    + now eapply TypeTrans.
    + eapply TermTrans ; tea.
      econstructor ; tea.
      eapply TypeSym, typing_subst1 ; tea.
      do 2 econstructor ; boundary.
    + eapply TermTrans ; tea.
      econstructor ; tea.
      eapply TypeSym, elimSuccHypTy_conv ; tea.
      all: boundary.
  - econstructor ; eauto.
    now eapply TypeTrans.
  - econstructor ; eauto.
    eapply IHDeclNeutralConversion.
    econstructor ; tea.
    eapply TypeSym, conv_neu_typing ; tea.
    eauto using conv_neu_sound with boundary.
  - econstructor ; eauto.
    eapply IHDeclNeutralConversion.
    econstructor ; tea.
    eapply TypeSym, conv_neu_typing ; tea.
    eauto using conv_neu_sound with boundary.
  - assert [|- Γ,, A ≅ Γ ,, A'] by
      (constructor ; eauto using ctx_refl with boundary).
    econstructor ; eauto.
    + now eapply TypeTrans.
    + eapply TermTrans ; tea.
      econstructor ; tea.
      now eapply TypeSym.
    + eapply TypeTrans ; tea.
      eapply stability ; tea.
      econstructor ; tea.
      econstructor ; tea.
      * erewrite (wk1_irr (A := A')).
        eapply typing_wk ; boundary.
      * erewrite (wk1_irr (A := A')).
        eapply typing_wk ; boundary.
      * do 2 econstructor ; eauto.
        1: boundary.
        rewrite wk1_ren_on.
        now econstructor.
    + eapply TermTrans ; tea ; refold.
      econstructor ; tea.
      eapply typing_subst2 ; eauto ; cycle -1.
      * now apply TypeSym.
      * boundary.
      * now apply TermSym.
      * cbn.
        eapply TermSym ; refold.
        replace (tId _ _ _) with (tId A x x') by now bsimpl.
        econstructor.
        1: now econstructor.
        constructor ; tea.
        all: now constructor ; boundary.
    + eapply TermTrans ; eauto ; refold.
      econstructor ; tea.
      now apply TypeSym.
    + eapply IHDeclNeutralConversion ; eauto.
      econstructor ; tea.
      eapply TypeSym.
      now econstructor.
  - econstructor ; eauto.
    eapply IHDeclNeutralConversion.
    econstructor ; eauto.
    now eapply TypeSym.
Qed.


Module DeclarativeTypingProperties.
  
  Export DeclarativeTypingData.
  #[export] Existing Instance ConvNeuConv_Decl.

  Import WeakDeclarativeTypingProperties.

  #[export] Existing Instance WfCtxDeclProperties.
  #[export] Existing Instance WfTypeDeclProperties.
  #[export] Existing Instance TypingDeclProperties.
  #[export] Existing Instance ConvTypeDeclProperties.
  #[export] Existing Instance RedTermDeclProperties.
  #[export] Existing Instance RedTypeDeclProperties.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de)
    (ConvNeuConv0 := ConvNeuConv_Decl) := {}.
  Proof.
    4,7,11: shelve.
    all: gen_typing.
    Unshelve.
    - intros.
      apply conv_neu_sound.
      assumption.
    - intros * ??? Hf ? Hg **.
      eapply (convtm_eta (ConvNeuConv0 := ConvNeuConv_WeakDecl)) ; eauto.
      + inversion Hf ; subst.
        all: constructor ; eauto.
        split.
        1-2: now eapply conv_neu_ne.
        now eapply conv_neu_sound.
      + inversion Hg ; subst.
        all: constructor ; eauto.
        split.
        1-2: now eapply conv_neu_ne.
        now eapply conv_neu_sound.
    - intros * ??? Hp ? Hp' **.
      eapply (convtm_eta_sig (ConvNeuConv0 := ConvNeuConv_WeakDecl)) ; eauto.
      + inversion Hp ; subst.
        all: constructor ; eauto.
        split.
        1-2: now eapply conv_neu_ne.
        now eapply conv_neu_sound.
      + inversion Hp' ; subst.
        all: constructor ; eauto.
        split.
        1-2: now eapply conv_neu_ne.
        now eapply conv_neu_sound.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de)
    (ConvNeuConv0 := ConvNeuConv_Decl) := {}.
  Proof.
    all: try solve [now econstructor].
    - split; red.
      + eauto using conv_neu_sym.
      + eauto using conv_neu_trans.
    - intros.
      eauto using conv_neu_wk.
    - now intros * ?%conv_neu_ne.
    - intros * H.
      eapply termGen' in H as [? [[? [->]]]].
      eapply neuConvConv ; tea.
      now econstructor.
  Qed.

  #[export] Instance DeclarativeTypingProperties :
    GenericTypingProperties de _ _ _ _ _ ConvNeuConv_Decl _ _ _ _ := {}.

End DeclarativeTypingProperties.