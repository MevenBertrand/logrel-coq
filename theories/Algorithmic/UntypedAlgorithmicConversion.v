(** * LogRel.UntypedAlgorithmicConversion: alternative definition of algorithmic conversion. *)

From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel Require Import Sections.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeConstructorsInj NeutralConvProperties.
From LogRel.Algorithmic Require Import BundledAlgorithmicTyping AlgorithmicConvProperties.

Import DeclarativeTypingProperties AlgorithmicTypedConvData AlgorithmicTypingData.


(** ** Definitions *)

(** **** Conversion of types/terms: there is no distinction here *)
Inductive UConvAlg : term -> term  -> Type :=
  | termConvRed {t t' u u'} :
    [t ⤳* t'] ->
    [u ⤳* u' ] ->
    [t' ≅h u'] ->
    [t ≅ u]
(** **** Conversion of types/terms reduced to a weak-head normal form *)
with UConvRedAlg : term -> term -> Type :=
  | UnivReflUAlg :
      [U ≅h U]
  | PiCongUAlg {A B A' B'} :
    [A ≅ A'] ->
    [B ≅ B'] ->
    [tProd A B ≅h tProd A' B']
  | NatReflUAlg :
    [tNat ≅h tNat]
  | ZeroReflUAlg :
    [tZero ≅h tZero]
  | SuccCongUAlg {t t'} :
    [t ≅ t'] ->
    [tSucc t ≅h tSucc t']
  | EmptyReflUAlg :
    [tEmpty ≅h tEmpty]
  | LamCongUAlg {A t A' t'} :
    [t ≅ t'] ->
    [tLambda A t ≅h tLambda A' t']
  | LambNeUAlg {A t n'} :
    whne n' ->
    [t ≅ eta_expand n'] -> 
    [tLambda A t ≅h n']
  | NeLamUAlg {n A' t'} :
    whne n ->
    [eta_expand n ≅ t'] -> 
    [n ≅h tLambda A' t']
  | SigCongUAlg {A B A' B'} :
    [A ≅ A'] ->
    [ B ≅ B'] ->
    [tSig A B ≅h tSig A' B']
  | PairCongUAlg {A B p q A' B' p' q'} :
    [p ≅ p'] ->
    [q ≅ q'] ->
    [tPair A B p q ≅h tPair A' B' p' q']
  | PairNeUAlg {A B p q n'} :
    whne n' ->
    [p ≅ tFst n'] ->
    [q ≅ tSnd n'] ->
    [tPair A B p q ≅h n']
  | NePairUAlg {n A' B' p' q'} :
    whne n ->
    [tFst n ≅ p'] ->
    [tSnd n ≅ q'] ->
    [n ≅h tPair A' B' p' q']
  | IdCongUAlg {A A' x x' y y'} :
    [A ≅ A'] ->
    [x ≅ x'] ->
    [y ≅ y'] ->
    [tId A x y ≅h tId A' x' y']
  | termIdReflCong {A x A' x'} :
    [tRefl A x ≅h tRefl A' x']
  | NeuConvUAlg {m n} :
    [m ~ n] ->
    [m ≅h n]

(** **** Conversion of neutral terms *)
with UConvNeuAlg : term  -> term -> Type :=
  | VarConvUAlg {n} :
    [tRel n ~ tRel n]
  | AppCongUAlg {m n t u} :
    [m ~ n] ->
    [t ≅ u] ->
    [tApp m t ~ tApp n u]
  | NatElimCongUAlg {n n' P P' hz hz' hs hs'} :
    [n ~ n'] ->
    [P ≅ P'] ->
    [hz ≅ hz'] ->
    [hs ≅ hs'] ->
    [tNatElim P hz hs n ~ tNatElim P' hz' hs' n']
  | EmptyElimCongUAlg {P P' e e'} :
    [e ~ e'] ->
    [P ≅ P'] ->
    [tEmptyElim P e ~ tEmptyElim P' e']
  | FstCongUAlg {m n} :
    [m ~ n] ->
    [tFst m ~ tFst n]
  | SndCongUAlg {m n} :
    [m ~ n] ->
    [tSnd m ~ tSnd n]
  | IdElimCongUAlg {A A' x x' P P' hr hr' y y' e e'} :
    [e ~ e'] ->
    [P ≅ P'] ->
    [hr ≅ hr'] ->
    [tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e']

where "[ A ≅ B ]" := (UConvAlg A B)
and "[ A ≅h B ]" := (UConvRedAlg A B)
and "[ m ~ n ]" := (UConvNeuAlg m n).

(** ** Induction principles *)

Scheme 
    Minimality for UConvAlg Sort Type with
    Minimality for UConvRedAlg Sort Type with
    Minimality for UConvNeuAlg Sort Type.
    
Combined Scheme UAlgoConvInduction from
    UConvAlg_rect_nodep,
    UConvRedAlg_rect_nodep,
    UConvNeuAlg_rect_nodep.

Arguments UAlgoConvInduction PEq PRedEq PNeEq : rename.


Definition UAlgoConvInductionConcl :=
  ltac:(
    let t := type of UAlgoConvInduction in
    let t' := remove_steps t in
    exact t').

(** ** Relation to weak-head normal forms *)

Section UAlgoConvWh.

  Let PEq (A B : term) := True.
  Let PNeEq (m n : term) := 
    whne m × whne n.
  Let PRedEq (t u : term) := 
    whnf t × whnf u.

  Theorem algo_uconv_wh :
    UAlgoConvInductionConcl PEq PRedEq PNeEq.
  Proof.
    subst PEq PRedEq PNeEq ; cbn.
    apply UAlgoConvInduction.
    all: intros ; prod_splitter ; prod_hyp_splitter.
    all: now constructor.
  Qed.

End UAlgoConvWh.

Notation "[ A ≅ B ]" := (UConvAlg A B).
Notation "[ A ≅h B ]" := (UConvRedAlg A B).
Notation "[ m ~ n ]" := (UConvNeuAlg m n).


(** ** Strengthening of untyped conversion *)
(** This will be useful in the equivalence proof, when we get an induction hypothesis
  that is weakened because of η-expansions. *)

Section UConvStr.
  
  Let PEq (A B : term) := forall Γ Δ (ρ : Γ ≤ Δ) A' B',
    A = A'⟨ρ⟩ -> B = B'⟨ρ⟩ ->
    [A' ≅ B'].
  Let PRedEq (A B : term) := forall Γ Δ (ρ : Γ ≤ Δ) A' B',
    A = A'⟨ρ⟩ -> B = B'⟨ρ⟩ ->
    [A' ≅h B'].
  Let PNeEq (t u : term) := forall Γ Δ (ρ : Γ ≤ Δ) t' u',
    t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ ->
    [t' ~ u'].

  #[local] Ltac push_renaming :=
    repeat match goal with
    | eq : _ = ?t⟨_⟩ |- _ =>
        destruct t ; cbn in * ; try solve [congruence] ;
        inversion eq ; subst ; clear eq
    end.

  Theorem algo_uconv_str :
    UAlgoConvInductionConcl PEq PRedEq PNeEq.
  Proof.
    subst PEq PRedEq PNeEq.
    apply UAlgoConvInduction.
    - intros * Hred Hred' ? IH * -> ->.
      eapply credalg_str in Hred as [? [->]] , Hred' as [? [->]].
      now econstructor.
    - solve [intros ; push_renaming ; now econstructor].
    - intros * ? IHA ? IHB ? **.
      push_renaming.
      econstructor.
      + now eapply IHA.
      + now unshelve eapply IHB with(ρ := wk_up _ ρ).
    - solve [intros ; push_renaming ; now econstructor].
    - solve [intros ; push_renaming ; now econstructor].
    - intros * ? IH ** ; push_renaming ; econstructor ; now eapply IH.
    - solve [intros ; push_renaming ; now econstructor].
    - intros * ? IH ** ; push_renaming ; econstructor ; now
        unshelve eapply IH with (ρ := wk_up _ ρ).
    - intros * ?? IH ** ; subst ; push_renaming ; econstructor.
      + now eapply whne_ren.
      + unshelve eapply IH with (ρ := wk_up _ ρ).
        1: assumption.
        all: now bsimpl.
    - intros * ?? IH ** ; subst ; push_renaming ; econstructor.
      + now eapply whne_ren.
      + unshelve eapply IH with (ρ := wk_up _ ρ).
        1: assumption.
        all: now bsimpl.
    - intros * ? IHA ? IHB ** ; push_renaming ; econstructor.
      + now eapply IHA.
      + unshelve eapply IHB with (ρ := wk_up _ ρ).
        1: assumption.
        all: now bsimpl.
    - intros * ? IHf ? IHs ** ; push_renaming ; econstructor.
      + now eapply IHf.
      + now eapply IHs.
    - intros * ?? IHf ? IHs ** ; subst ; push_renaming ; econstructor.
      + now eapply whne_ren.
      + now eapply IHf.
      + now eapply IHs.
    - intros * ?? IHf ? IHs ** ; subst ; push_renaming ; econstructor.
      + now eapply whne_ren.
      + now eapply IHf.
      + now eapply IHs.
    - intros * ? IHA ? IHa ? IHa' ** ; push_renaming ; econstructor.
      + now eapply IHA.
      + now eapply IHa.
      + now eapply IHa'.
    - solve [intros ; push_renaming ; now econstructor].
    - intros * ? IH ** ; subst.
      econstructor.
      now eapply IH.
    - intros ; push_renaming.
      eapply section_inj in H1 as ->.
      2: eapply section_wk.
      now econstructor.
    - intros * ? IH ? IH' ** ; push_renaming.
      econstructor.
      + now eapply IH.
      + now eapply IH'.
    - intros * ? IHn ? IHP ? IHz ? IHs ** ; push_renaming.
      econstructor.
      + now eapply IHn.
      + unshelve eapply IHP with (ρ := wk_up _ ρ).
        1: assumption.
        all: now bsimpl.
      + now eapply IHz.
      + now eapply IHs.
    - intros * ? IHn ? IHP ** ; push_renaming.
      econstructor.
      + now eapply IHn.
      + unshelve eapply IHP with (ρ := wk_up _ ρ).
        1: assumption.
        all: now bsimpl.
    - intros * ? IH ** ; push_renaming.
      econstructor.
      now eapply IH.
    - intros * ? IH ** ; push_renaming.
      econstructor.
      now eapply IH.
    - intros * ? IHn ? IHP ? IHr ** ; push_renaming.
      econstructor.
      + now eapply IHn.
      + unshelve eapply IHP with (ρ := wk_up _ (wk_up _ ρ)).
        1-2: assumption.
        all: now bsimpl.
      + now eapply IHr.
  Qed.

End UConvStr.


(** ** Extra preservation lemmas for untyped conversion *)

Section PremisePreserve.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de} `{!TypeReductionComplete de}.

  Lemma LamCongUAlg_prem0_red Γ T A t A' t' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ A'' B, [× [T ⤳* tProd A'' B], [Γ ,, A'' |-[de] t : B] & [Γ ,, A'' |-[de] t' : B]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' [? [[B' [->]] Hconv']]%termGen'].
    eapply red_compl_prod_l in Hconv as (A''&B''&[Hred]).
    edestruct prod_ty_inj.
    {
     etransitivity ; tea.
     now eapply RedConvTyC.
    }

    do 2 eexists ; split.
    - now eapply redty_sound.
    - now econstructor ; [eapply stability1|..] ; cycle 1.
    - now econstructor ; [eapply stability1|..].
  Qed.

  Lemma LamCongUAlg_prem0 Γ T A t A' t' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ B, [× [Γ ,, A |-[de] t : B], [Γ ,, A |- t' : B] & [Γ |-[de] tProd A B ≅ T]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' [? [[B' [->]] Hconv']]%termGen'].
    edestruct prod_ty_inj.
    {
     etransitivity ; [..|symmetry] ; [eapply Hconv'|eapply Hconv].
    }

    eexists ; split ; tea.
    econstructor ; tea.
    now eapply stability1.
  Qed.

  Lemma LamCongUAlg_concl Γ T A t A' t' B :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    [Γ ,, A |-[de] t ≅ t' : B] ->
    [Γ |-[de] tProd A B ≅ T] ->
    [Γ |-[de] tLambda A t ≅ tLambda A' t' : T].
  Proof.
    intros [[? []]%LamCongUAlg_prem0 [_ Ht']]%dup ??.
    econstructor ; tea.
    econstructor ; tea.
    2: constructor.
    1-2: eapply prod_ty_inv ; boundary.
    eapply termGen' in Ht' as (?&[? [->]]&?).
    eapply prod_ty_inj.
    etransitivity ; tea.
    now symmetry.
  Qed.

  Lemma LamNeUAlg_prem0_red Γ T A t n' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] n' : T] ->
    ∑ A'' B, [× [T ⤳* tProd A'' B], [Γ ,, A'' |- t : B] & [Γ ,, A'' |- eta_expand n' : B]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' Hn].
    eapply red_compl_prod_l in Hconv as (A''&B''&[Hred]).
    do 2 eexists ; split.

    - now eapply redty_sound.
    - now econstructor ; [eapply stability1 |..].
    - eapply typing_eta' ; econstructor ; tea.
      now eapply RedConvTyC.
  Qed.

  Lemma LamNeUAlg_prem0 Γ T A t n' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] n' : T] ->
    ∑ B, [× [Γ ,, A |-[de] t : B], [Γ ,, A |- eta_expand n' : B] & [Γ |-[de] tProd A B ≅ T]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' ?].

    eexists ; split ; tea.
    eapply typing_eta'.
    now econstructor.
  Qed.

  Lemma LamNeUAlg_concl Γ T A t n' B :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] n' : T] ->
    [Γ ,, A |-[de] t ≅ eta_expand n' : B] ->
    [Γ |-[de] tProd A B ≅ T] ->
    [Γ |-[de] tLambda A t ≅ n' : T].
  Proof.
    intros [[? []]%LamNeUAlg_prem0 [_ Ht']]%dup ??.
    econstructor ; tea.
    etransitivity.
    2: eapply TermFunEta ; refold ; now econstructor.
    econstructor ; tea.
    2-3: constructor.
    all: eapply prod_ty_inv ; boundary.
  Qed.

  Lemma NeLamUAlg_prem0_red Γ T n A' t' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ A'' B, [× [T ⤳* tProd A'' B], [Γ ,, A'' |- eta_expand n : B] & [Γ ,, A'' |- t' : B]].
  Proof.
    intros [Hn [? [[B [->]] Hconv]]%termGen'].
    eapply red_compl_prod_l in Hconv as (A''&B''&[Hred]).
    do 2 eexists ; split.

    - now eapply redty_sound.
    - eapply typing_eta' ; econstructor ; tea.
      now eapply RedConvTyC.
    - now econstructor ; [eapply stability1 | ..].
  Qed.

  Lemma NeLamUAlg_prem0 Γ T n A' t' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ B, [× [Γ ,, A' |-[de] eta_expand n : B], [Γ ,, A' |- t' : B] & [Γ |-[de] tProd A' B ≅ T]].
  Proof.
    intros [? [? [[B [->]] Hconv]]%termGen'].

    eexists ; split ; tea.
    eapply typing_eta'.
    now econstructor.
  Qed.

  Lemma NeLamUAlg_concl Γ T n A' t' B :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    [Γ ,, A' |-[de] eta_expand n ≅ t' : B] ->
    [Γ |-[de] tProd A' B ≅ T] ->
    [Γ |-[de] n ≅ tLambda A' t' : T].
  Proof.
    intros [[? []]%NeLamUAlg_prem0 [Ht _]]%dup ??.
    econstructor ; tea.
    etransitivity.
    1: symmetry ; eapply TermFunEta ; refold ; now econstructor.
    econstructor ; tea.
    2-3: constructor.
    all: eapply prod_ty_inv ; boundary.
  Qed.

  Lemma PairCongUAlg_prem0_red Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    ∑ A'' B'', [T ⤳* tSig A'' B''] × ([Γ |- p : A''] × [Γ |- p' : A'']).
  Proof.
    intros [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'].
    eapply red_compl_sig_l in Hconv as (A''&B''&[Hred]).

    edestruct sig_ty_inj.
    {
      etransitivity ; tea.
      now eapply RedConvTyC.
    }
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound.
    - now econstructor.
    - now econstructor.
  Qed.

  Lemma PairCongUAlg_prem1_red Γ A B p q A' B' p' q' A'' B'' T :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [T ⤳* tSig A'' B''] ->
    [Γ |-[de] p ≅ p' : A''] ->
    [Γ |- q : B''[(tFst (tPair A B p q))..]] × [Γ |- q' : B''[(tFst (tPair A B p q))..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'] ? ?.
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv as [].
    2: eapply RedConvTyC, subject_reduction_type ; boundary.
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv' as [].
    2: eapply RedConvTyC, subject_reduction_type ; boundary.
    
    assert [Γ |-[de] p' : A]
      by (econstructor ; tea ; etransitivity ; tea ; now symmetry).
    assert [Γ |-[ de ] p ≅ tFst (tPair A B p q) : A] by
      (econstructor ; symmetry ; now econstructor).

    split.
    all: econstructor ; tea.
    all: eapply typing_subst1 ; tea.
    etransitivity.
    all: eapply TermConv ; refold ; tea.
    3: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma PairCongUAlg_prem0 Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |- p : A] × [Γ |- p' : A].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'].
    split ; tea.
    econstructor ; tea.
    eapply sig_ty_inj.
    etransitivity ; tea.
    now symmetry.
  Qed.

  Lemma PairCongUAlg_prem1 Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] p ≅ p' : A] ->
    [Γ |- q : B[p..]] × [Γ |- q' : B[p..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'].
    split ; tea.
    econstructor ; tea.
    symmetry.
    eapply typing_subst1 ; tea.
    eapply sig_ty_inj.
    etransitivity ; tea.
    now symmetry.
  Qed.

  Lemma PairCongUAlg_concl Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] p ≅ p' : A] ->
    [Γ |-[de] q ≅ q' : B[p..]] ->
    [Γ |-[de] tPair A B p q ≅ tPair A' B' p' q' : T].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'] ??.
    econstructor.
    2: apply Hconv.
    econstructor ; tea.
    1: constructor ; boundary.
    all: eapply sig_ty_inj.
    all: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma PairNeUAlg_prem0_red Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    ∑ A'' B'', [T ⤳* tSig A'' B''] × ([Γ |- p : A''] × [Γ |- tFst n' : A'']).
  Proof.
    intros [[? [[->] [Hconv Hconv']%dup]]%termGen' ?].
    eapply red_compl_sig_l in Hconv as (?&?&[Hred]).
    
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound.
    - now econstructor.
    - do 2 econstructor ; tea.
      now eapply RedConvTyC.
  Qed.

  Lemma PairNeUAlg_prem1_red Γ A B p q n' A'' B'' T :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [T ⤳* tSig A'' B''] ->
    [Γ |-[de] p ≅ tFst n' : A''] ->
    [Γ |- q : B''[(tFst (tPair A B p q))..]] × [Γ |- tSnd n' : B''[(tFst (tPair A B p q))..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen'?] ? ?.

    assert [Γ |-[de] T ≅ tSig A'' B''] by
      (eapply RedConvTyC, subject_reduction_type ; boundary).
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv as [] ; tea.
    
    assert [Γ |-[ de ] p ≅ tFst (tPair A B p q) : A] by
      (econstructor ; symmetry ; now econstructor).

    split.
    - econstructor ; tea.
      now eapply typing_subst1.
    - econstructor.
      1: now do 2 econstructor.
      eapply typing_subst1.
      2: constructor ; boundary.
      etransitivity ; tea.
      econstructor.
      all: now symmetry.
  Qed.

  Lemma PairNeUAlg_prem0 Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [Γ |- p : A] × [Γ |- tFst n' : A].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' ?].
    split ; tea.
    do 2 (econstructor ; tea).
    now symmetry.
  Qed.

  Lemma PairNeUAlg_prem1 Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [Γ |-[de] p ≅ tFst n' : A] ->
    [Γ |- q : B[p..]] × [Γ |- tSnd n' : B[p..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' ?].
    split ; tea.
    econstructor ; tea.
    1: do 2 (econstructor ; tea).
    1: now symmetry.
    symmetry.
    eapply typing_subst1 ; tea.
    constructor.
    eapply sig_ty_inv.
    boundary.
  Qed.

  Lemma PairNeUAlg_concl Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [Γ |-[de] p ≅ tFst n' : A] ->
    [Γ |-[de] q ≅ tSnd n' : B[p..]] ->
    [Γ |-[de] tPair A B p q ≅ n' : T].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' ?] ??.
    econstructor ; tea.
    etransitivity.
    2: do 2 (econstructor ; tea) ; now symmetry.
    econstructor ; eauto.
    all: eapply sig_ty_inj.
    all: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma NePairUAlg_prem0_red Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    ∑ A'' B'', [T ⤳* tSig A'' B''] × ([Γ |- tFst n : A''] × [Γ |- p' : A'']).
  Proof.
    intros [? [? [[->] [Hconv Hconv']%dup]]%termGen'].
    eapply red_compl_sig_l in Hconv as (?&?&[Hred]).
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound.
    - do 2 econstructor ; tea.
      now eapply RedConvTyC.
    - now econstructor.
  Qed.

  Lemma NePairUAlg_prem1_red Γ n A' B' p' q' A'' B'' T :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [T ⤳* tSig A'' B''] ->
    [Γ |-[de] tFst n ≅ p' : A''] ->
    [Γ |- tSnd n : B''[(tFst n)..]] × [Γ |- q' : B''[(tFst n)..]].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'] ? ?.

    assert [Γ |-[de] T ≅ tSig A'' B''] by
      (eapply RedConvTyC, subject_reduction_type ; boundary).
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv as [] ; tea.

    split.
    - now do 2 econstructor.
    - econstructor ; tea.
      eapply typing_subst1 ; tea.
      econstructor.
      all: now symmetry.
  Qed.

  Lemma NePairUAlg_prem0 Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |- tFst n : A'] × [Γ |- p' : A'].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'].
    split ; tea.
    do 2 (econstructor ; tea).
    now symmetry.
  Qed.

  Lemma NePairUAlg_prem1 Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] tFst n ≅ p' : A'] ->
    [Γ |- tSnd n : B'[p'..]] × [Γ |- q' : B'[p'..]].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'].
    split ; tea.
    econstructor ; tea.
    1: do 2 (econstructor ; tea).
    1: now symmetry.
    eapply typing_subst1 ; tea.
    constructor.
    eapply sig_ty_inv.
    boundary.
  Qed.

  Lemma NePairUAlg_concl Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] tFst n ≅ p' : A'] ->
    [Γ |-[de] tSnd n ≅ q' : B'[p'..]] ->
    [Γ |-[de] n ≅ tPair A' B' p' q' : T].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'] ??.
    econstructor ; tea.
    symmetry.
    etransitivity.
    2: do 2 (econstructor ; tea) ; now symmetry.
    econstructor ; eauto.
    5-6: now symmetry. 
    all: eapply sig_ty_inj.
    all: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma AppCongUAlg_bridge_red Γ T m n t u :
    [Γ |-[al] m ~ n ▹ T] ->
    well_typed Γ (tApp m t) × well_typed Γ (tApp n u) ->
    ∑ A B,
      [T ⤳* tProd A B] ×
      [× [Γ |-[ de ] m ≅ n : tProd A B],
            forall T', [Γ |-[ de ] m : T'] -> [Γ |-[ de ] tProd A B ≅ T']
            & forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tProd A B ≅ T']].
  Proof.
    intros Hal [[? [? [(A&B&[-> Hm])]]%termGen'] [? [? [(A'&B'&[->])]]%termGen']].
    eapply algo_conv_sound in Hal as [? Hpri].
    2-3: now eexists.
    epose proof Hm as Hconv%Hpri.
    eapply red_compl_prod_r in Hconv as (?&?&[]).
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound. 
    - econstructor ; tea.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
  Qed.

  Lemma AppCongUAlg_bridge Γ T m n t u :
    [× [Γ |-[ de ] m ≅ n : T],
      forall T' : term, [Γ |-[ de ] m : T'] -> [Γ |-[ de ] T ≅ T']
      & forall T' : term, [Γ |-[ de ] n : T'] -> [Γ |-[ de ] T ≅ T']] ->
    well_typed Γ (tApp m t) × well_typed Γ (tApp n u) ->
    ∑ A B,
      [Γ |-[de] T ≅ tProd A B] ×
      [× [Γ |-[ de ] m ≅ n : tProd A B],
            forall T', [Γ |-[ de ] m : T'] -> [Γ |-[ de ] tProd A B ≅ T']
            & forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tProd A B ≅ T']].
  Proof.
    intros [? Hpri] [[? [? [(A&B&[-> Hm])]]%termGen'] [? [? [(A'&B'&[->])]]%termGen']].
    epose proof Hm as Hconv%Hpri.
    do 2 eexists ; split ; [..|split] ; tea.
    - now econstructor.
    - intros.
      etransitivity ; eauto.
      now symmetry.
    - intros.
      etransitivity ; eauto.
      now symmetry.
  Qed.

  Lemma NatElimCongUAlg_bridge_red Γ T P hz hs n P' hz' hs' n' :
    [Γ |-[al] n ~ n' ▹ T] ->
    well_typed Γ (tNatElim P hz hs n) × well_typed Γ (tNatElim P' hz' hs' n') ->
    [T ⤳* tNat] ×
      [× [Γ |-[ de ] n ≅ n' : tNat],
            forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tNat ≅ T']
            & forall T', [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] tNat ≅ T']].
  Proof.
    intros Hal [[? [? [[-> ??? Hn]]]%termGen'] [? [? [[->]]]%termGen']].
    eapply algo_conv_sound in Hal as [? Hpri].
    2-3: now eexists.
    epose proof Hn as Hconv%Hpri.
    eapply red_compl_nat_r in Hconv.
    split ; [..|split].
    - now eapply redty_sound. 
    - econstructor ; tea.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
  Qed.

  Lemma NatElimCongUAlg_bridge Γ T P hz hs n P' hz' hs' n' :
    [× [Γ |-[ de ] n ≅ n' : T],
      forall T' : term, [Γ |-[ de ] n : T'] -> [Γ |-[ de ] T ≅ T']
      & forall T' : term, [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] T ≅ T']] ->
    well_typed Γ (tNatElim P hz hs n) × well_typed Γ (tNatElim P' hz' hs' n') ->
    [Γ |-[de] T ≅ tNat] ×
    [× [Γ |-[ de ] n ≅ n' : tNat],
          forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tNat ≅ T']
          & forall T', [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] tNat ≅ T']].
  Proof.
    intros [? Hpri] [[? [? [[-> ??? Hn]]]%termGen'] [? [? [[->]]]%termGen']].
    epose proof Hn as Hconv%Hpri.
    split ; [..|split] ; tea.
    - now econstructor.
    - intros.
      etransitivity ; eauto.
      now symmetry.
    - intros.
      etransitivity ; eauto.
      now symmetry.
  Qed.

  Lemma EmptyElimCongUAlg_bridge_red Γ T P n P' n' :
    [Γ |-[al] n ~ n' ▹ T] ->
    well_typed Γ (tEmptyElim P n) × well_typed Γ (tEmptyElim P' n') ->
    [T ⤳* tEmpty] ×
      [× [Γ |-[ de ] n ≅ n' : tEmpty],
            forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tEmpty ≅ T']
            & forall T', [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] tEmpty ≅ T']].
  Proof.
    intros Hal [[? [? [[-> ? Hn]]]%termGen'] [? [? [[->]]]%termGen']].
    eapply algo_conv_sound in Hal as [? Hpri].
    2-3: now eexists.
    epose proof Hn as Hconv%Hpri.
    eapply red_compl_empty_r in Hconv.
    split ; [..|split].
    - now eapply redty_sound. 
    - econstructor ; tea.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
  Qed.

Lemma EmptyElimCongUAlg_bridge Γ T P n P' n' :
  [× [Γ |-[ de ] n ≅ n' : T],
    forall T' : term, [Γ |-[ de ] n : T'] -> [Γ |-[ de ] T ≅ T']
    & forall T' : term, [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] T ≅ T']] ->
  well_typed Γ (tEmptyElim P n) × well_typed Γ (tEmptyElim P' n') ->
  [Γ |-[de] T ≅ tEmpty] ×
  [× [Γ |-[ de ] n ≅ n' : tEmpty],
        forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tEmpty ≅ T']
        & forall T', [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] tEmpty ≅ T']].
Proof.
  intros [? Hpri] [[? [? [[-> ? Hn]]]%termGen'] [? [? [[->]]]%termGen']].
  epose proof Hn as Hconv%Hpri.
  split ; [..|split] ; tea.
  - now econstructor.
  - intros.
    etransitivity ; eauto.
    now symmetry.
  - intros.
    etransitivity ; eauto.
    now symmetry.
Qed.

  Lemma FstCongUAlg_bridge_red Γ T m n :
    [Γ |-[al] m ~ n ▹ T] ->
    well_typed Γ (tFst m) × well_typed Γ (tFst n) ->
    ∑ A B,
      [T ⤳* tSig A B] ×
      [× [Γ |-[ de ] m ≅ n : tSig A B],
            forall T', [Γ |-[ de ] m : T'] -> [Γ |-[ de ] tSig A B ≅ T']
            & forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tSig A B ≅ T']].
  Proof.
    intros Hal [[? [? [(A&B&[-> Hm])]]%termGen'] [? [? [(A'&B'&[->])]]%termGen']].
    eapply algo_conv_sound in Hal as [? Hpri].
    2-3: now eexists.
    epose proof Hm as Hconv%Hpri.
    eapply red_compl_sig_r in Hconv as (?&?&[]).
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound. 
    - econstructor ; tea.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
  Qed.

  Lemma FstCongUAlg_bridge Γ T n n' :
    [× [Γ |-[ de ] n ≅ n' : T],
      forall T' : term, [Γ |-[ de ] n : T'] -> [Γ |-[ de ] T ≅ T']
      & forall T' : term, [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] T ≅ T']] ->
    well_typed Γ (tFst n) × well_typed Γ (tFst n') ->
    ∑ A B, [Γ |-[de] T ≅ tSig A B] ×
    [× [Γ |-[ de ] n ≅ n' : tSig A B],
          forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tSig A B ≅ T']
          & forall T', [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] tSig A B ≅ T']].
  Proof.
    intros [? Hpri] [[? [? [(?&?&[-> Hn])]]%termGen'] [? [? [(?&?&[->])]]%termGen']].
    epose proof Hn as Hconv%Hpri.
    do 2 eexists.
    split ; [..|split] ; tea.
    - now econstructor.
    - intros.
      etransitivity ; eauto.
      now symmetry.
    - intros.
      etransitivity ; eauto.
      now symmetry.
  Qed.


  Lemma SndCongUAlg_bridge_red Γ T m n :
    [Γ |-[al] m ~ n ▹ T] ->
    well_typed Γ (tSnd m) × well_typed Γ (tSnd n) ->
    ∑ A B,
      [T ⤳* tSig A B] ×
      [× [Γ |-[ de ] m ≅ n : tSig A B],
            forall T', [Γ |-[ de ] m : T'] -> [Γ |-[ de ] tSig A B ≅ T']
            & forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tSig A B ≅ T']].
  Proof.
    intros Hal [[? [? [(A&B&[-> Hm])]]%termGen'] [? [? [(A'&B'&[->])]]%termGen']].
    eapply algo_conv_sound in Hal as [? Hpri].
    2-3: now eexists.
    epose proof Hm as Hconv%Hpri.
    eapply red_compl_sig_r in Hconv as (?&?&[]).
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound. 
    - econstructor ; tea.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
  Qed.

  Lemma SndCongUAlg_bridge Γ T n n' :
    [× [Γ |-[ de ] n ≅ n' : T],
      forall T' : term, [Γ |-[ de ] n : T'] -> [Γ |-[ de ] T ≅ T']
      & forall T' : term, [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] T ≅ T']] ->
    well_typed Γ (tSnd n) × well_typed Γ (tSnd n') ->
    ∑ A B, [Γ |-[de] T ≅ tSig A B] ×
    [× [Γ |-[ de ] n ≅ n' : tSig A B],
          forall T', [Γ |-[ de ] n : T'] -> [Γ |-[ de ] tSig A B ≅ T']
          & forall T', [Γ |-[ de ] n' : T'] -> [Γ |-[ de ] tSig A B ≅ T']].
  Proof.
    intros [? Hpri] [[? [? [(?&?&[-> Hn])]]%termGen'] [? [? [(?&?&[->])]]%termGen']].
    epose proof Hn as Hconv%Hpri.
    do 2 eexists.
    split ; [..|split] ; tea.
    - now econstructor.
    - intros.
      etransitivity ; eauto.
      now symmetry.
    - intros.
      etransitivity ; eauto.
      now symmetry.
  Qed.

  Lemma IdElimCongUAlg_bridge_red Γ T A x P hr y e A' x' P' hr' y' e' :
    [Γ |-[al] e ~ e' ▹ T] ->
    well_typed Γ (tIdElim A x P hr y e) × well_typed Γ (tIdElim A' x' P' hr' y' e') ->
    ∑ A'' x'' y'', [T ⤳* tId A'' x'' y''] ×
      [× [Γ |-[ de ] e ≅ e' : tId A'' x'' y''],
            forall T', [Γ |-[ de ] e : T'] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T']
            & forall T', [Γ |-[ de ] e' : T'] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T']].
  Proof.
    intros Hal [[? [? [[-> ????? He]]]%termGen'] [? [? [[->]]]%termGen']].
    eapply algo_conv_sound in Hal as [? Hpri].
    2-3: now eexists.
    epose proof He as Hconv%Hpri.
    eapply red_compl_id_r in Hconv as (?&?&?&[]).
    do 3 eexists.
    split ; [..|split].
    - now eapply redty_sound. 
    - econstructor ; tea.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
    - intros.
      etransitivity ; eauto.
      symmetry.
      now eapply RedConvTyC.
  Qed.

  Lemma IdElimCongUAlg_bridge Γ T A x P hr y e A' x' P' hr' y' e' :
    [× [Γ |-[ de ] e ≅ e' : T],
      forall T' : term, [Γ |-[ de ] e : T'] -> [Γ |-[ de ] T ≅ T']
      & forall T' : term, [Γ |-[ de ] e' : T'] -> [Γ |-[ de ] T ≅ T']] ->
    well_typed Γ (tIdElim A x P hr y e) × well_typed Γ (tIdElim A' x' P' hr' y' e') ->
    ∑ A'' x'' y'', [Γ |-[de] T ≅ tId A'' x'' y''] ×
      [× [Γ |-[ de ] e ≅ e' : tId A'' x'' y''],
            forall T', [Γ |-[ de ] e : T'] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T']
            & forall T', [Γ |-[ de ] e' : T'] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T']].
  Proof.
    intros [? Hpri] [[? [? [[-> ????? He]]]%termGen'] [? [? [[->]]]%termGen']].
    epose proof He as Hconv%Hpri.
    do 3 eexists.
    split ; [..|split] ; tea.
    - now econstructor.
    - intros.
      etransitivity ; eauto.
      now symmetry.
    - intros.
      etransitivity ; eauto.
      now symmetry.
  Qed.

End PremisePreserve.

Section UConvSound.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

  Lemma uconv_sound_decl :
    UAlgoConvInductionConcl
      (fun t u => 
        (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[de] t ≅ u]) ×
        (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[de] t ≅ u : A]))

      (fun t u =>
        (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[de] t ≅ u]) ×
        (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[de] t ≅ u : A]))

      (fun m n =>
        forall Γ, well_typed Γ m × well_typed Γ n ->
        ∑ A, [× [Γ |-[de] m ≅ n : A],
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]).
  
  Proof.
    apply UAlgoConvInduction.

    - intros * Ht Hu Ht' [Hty Htm].
      split.
      + intros * [Hconcl]%dup.
        eapply typeConvRed_prem2 in Hconcl ; tea.
        now eapply typeConvRed_concl ; eauto.

      + intros * [Hconcl]%dup.
        eapply termConvRed_prem3 in Hconcl ; tea.
        2: reflexivity.
        eapply termConvRed_concl ; eauto.
        reflexivity.

    - split.
      + now econstructor.
      + intros * [[? [[] ]]%termGen' _].

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typePiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, typePiCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros * [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&Hconv) ; tea.
        econstructor ; tea.
        eapply termPiCongAlg_concl.
        2: eapply IHB_tm, termPiCongAlg_prem1.
        1-2: eapply IHA_tm, termPiCongAlg_prem0.
        all: split ; now eapply ty_conv.
        
    - split.
      1: now constructor.
      intros * [].
      now constructor.

    - split.
      
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [].
        now constructor.

    - intros * ? [? IH].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl [Hty]]%dup.
        
        eapply termGen' in Hty as (?&[->]&?) ; tea.
        econstructor ; tea.
        eapply termSuccCongAlg_concl.
        1: eapply IH, termSuccCongAlg_prem0.
        all: split ; now eapply ty_conv.

    - split.
      1: now econstructor.
      intros * [].
      now constructor.

    - intros * ? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconv]%dup.
        eapply LamCongUAlg_prem0 in Hconv as (?&[]).
        eapply LamCongUAlg_concl ; eauto.

    - intros * ?? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconv]%dup.
        eapply LamNeUAlg_prem0 in Hconv as (?&[]).
        eapply LamNeUAlg_concl ; eauto.

    - intros * ?? [].
      split.
    
      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconv]%dup.
        eapply NeLamUAlg_prem0 in Hconv as (?&[]).
        eapply NeLamUAlg_concl ; eauto.

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, typeSigCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros * [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&Hconv) ; tea.
        econstructor ; tea.
        eapply termSigCongAlg_concl.
        2: eapply IHB_tm, termSigCongAlg_prem1.
        1-2: eapply IHA_tm, termSigCongAlg_prem0.
        all: split ; now eapply ty_conv.

    - intros * Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl ?]%dup.
        eapply PairCongUAlg_concl ; tea.
        2:eapply IHq, PairCongUAlg_prem1 ; tea.
        all: now eapply IHp, PairCongUAlg_prem0.

    - intros * ? Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl ?]%dup.
        eapply PairNeUAlg_concl ; tea.
        2:eapply IHq, PairNeUAlg_prem1 ; tea.
        all: now eapply IHp, PairNeUAlg_prem0.

    - intros * ? Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl ?]%dup.
        eapply NePairUAlg_concl ; tea.
        2:eapply IHq, NePairUAlg_prem1 ; tea.
        all: now eapply IHp, NePairUAlg_prem0.
        
    - intros * HA [IHA_ty IHA_tm] Hx [_ IHx_tm] Hy [_ IHy_tm].
      split.

      + intros ? [Hconcl]%dup.
        eapply typeIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty in Hpre0 as [Hpost0]%dup; eauto.
        eapply typeIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
        eapply IHx_tm, typeIdCongAlg_prem2 in Hpre1 as [Hpre2]%dup; eauto.
        now econstructor.

      + intros * [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&?) ; tea.
        econstructor ; tea.
        eapply termIdCongAlg_concl.
        3: eapply IHy_tm, termIdCongAlg_prem2.
        2,4: eapply IHx_tm, termIdCongAlg_prem1.
        1,2,4,6: eapply IHA_tm, termIdCongAlg_prem0.
        all: split ; now eapply ty_conv.

    - split.
  
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [[[? [[->] Hconv]]%termGen'] ?]%dup.
        econstructor ; tea.
        eapply termIdReflCong_concl.
        split ; now eapply ty_conv.

    - intros * Hconv IH.
      split.
      
      + intros * [Hconcl]%dup.
        eapply algo_uconv_wh in Hconv as [].
        eapply typeNeuConvAlg_prem2 in Hconcl; tea.
        edestruct IH ; tea.
        now eapply typeNeuConvAlg_concl.

      + intros * [Hconcl []]%dup.
        edestruct IH as (?&[]).
        1: split ; now eexists.
        now econstructor.

    - intros * [[[? (?&[? []]&?)%termGen']]]%dup.
      eexists.
      now eapply neuVarConvAlg_concl.

    - intros * Hconv IHm ? [_ IHt] * [Hconcl]%dup.

      eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IHm in Hpre0 as [? [Hpost0]%dup].
      eapply AppCongUAlg_bridge in Hpost0 as (?&?&[? [Hpre1]%dup]); tea.
      eapply neuAppCongAlg_prem1, IHt in Hpre1 ; eauto.
      eexists.
      now eapply neuAppCongAlg_concl.

    - intros * ? IH ? [IHP] ? [_ IHz] ? [_ IHs] ? [Hconcl]%dup.

      eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply NatElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuNatElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply neuNatElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHz in Hpre2 as [Hpos2]%dup ; eauto.
      eapply neuNatElimCong_prem3 in Hpos2 as [Hpre3 []]%dup ; eauto.
      eapply IHs in Hpre3 as Hpos3 ; eauto.
      eexists.
      now eapply neuNatElimCong_concl.

    - intros * ? IH ? [IHP] ? [Hconcl]%dup.

      eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply EmptyElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuEmptyElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eexists.
      now eapply neuEmptyElimCong_concl.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply FstCongUAlg_bridge in Hpost0 as (?&?&[? [Hpre1 []]%dup]); eauto.
      eexists.
      now eapply neuFstCongAlg_concl.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply SndCongUAlg_bridge in Hpost0 as (?&?&[? [Hpre1 []]%dup]); eauto.
      eexists.
      now eapply neuSndCongAlg_concl.

    - intros * ? IH ? [IHP] ? [_ IHr]  ? [Hconcl]%dup.

      eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply IdElimCongUAlg_bridge in Hpost0 as [? (?&?&?&[Hpost0]%dup)]; eauto.
      eapply neuIdElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply neuIdElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHr in Hpre2 as [Hpos2]%dup ; eauto.
      eexists.
      now eapply neuIdElimCong_concl.
  Qed.

End UConvSound.

(** ** Typed algorithmic conversion implies untyped algorithmic conversion *)

Section TypedToUntyped.
  Context
    `{!TypingSubst de}
    `{!TypeConstructorsInj de}.

  Lemma whne_app_inv f g :
  [tApp f⟨↑⟩ (tRel 0) ~ tApp g⟨↑⟩ (tRel 0)] ->
  [f ~ g].
  Proof.
    inversion 1 ; subst.
    unshelve eapply algo_uconv_str.
    6: eassumption.
    3: unshelve eapply wk1 ; tea ; exact ε.
    all: now bsimpl.
  Qed.

  Let PTyEq (Γ : context) (A B : term) := 
    [A ≅ B] × (whne A -> whne B -> [A ~ B]).
  Let PTyRedEq (Γ : context) (A B : term) :=
    [A ≅h B] × (whne A -> whne B -> [A ~ B]).
  Let PNeEq (Γ : context) (A t u : term) := [t ~ u].
  Let PNeRedEq (Γ : context) (A t u : term) := [t ~ u].
  Let PTmEq (Γ : context) (A t u : term) :=
    [t ≅ u] × (whne t -> whne u -> [t ~ u]).
  Let PTmRedEq (Γ : context) (A t u : term) :=
    [t ≅h u] × (whne t -> whne u -> [t ~ u]).

  Theorem bundled_conv_uconv :
    BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    all: subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply BundledConvInduction ; cbn in *.
    all: try solve [
      intros ; prod_hyp_splitter ; 
      now econstructor |
      intros ; prod_hyp_splitter ; 
      split ; [now econstructor|..] ;
      intros ;
      repeat match goal with
        | H : [_ ⤳* _] |- _ => eapply red_whne in H ; [..|eassumption] end ;
      now subst |
      intros ; prod_hyp_splitter ; 
      split ; [now econstructor|..] ;
      intros Hne ; now inversion Hne].
    - intros ; now prod_hyp_splitter.

    (** Comparison of two functions *)
    - intros * whf whg ? [[IHconv IHne]] [Hf Hg].
      eapply fun_isFun in Hf ; tea.
      eapply fun_isFun in Hg ; tea.
      destruct Hf, Hg.
      + split.
        2: intros Hne ; inversion Hne.
        econstructor.
        inversion IHconv ; subst.
        econstructor ; tea.
        all: eapply eta_expand_beta_inv ; tea.
        all: now eapply algo_uconv_wh in H2 as [].
      + split.
        2: intros Hne ; inversion Hne.
        econstructor ; tea.
        inversion IHconv ; subst.
        econstructor ; tea.
        eapply eta_expand_beta_inv ; tea.
        now eapply algo_uconv_wh in H2 as [].
      + split.
        2: intros ? Hne ; inversion Hne.
        econstructor ; tea.
        inversion IHconv ; subst.
        econstructor ; tea.
        eapply eta_expand_beta_inv ; tea.
        now eapply algo_uconv_wh in H2 as [].
      + split.
        1: econstructor.
        2: intros _ _.
        all: eapply whne_app_inv, IHne ; econstructor ; now eapply whne_ren.

    (** Comparison of two pairs *)
    - intros * whp whq ? [[IHconv IHne]] ? [[IHconv' IHne']] [Hp Hq].
      eapply sig_isPair in Hp ; tea.
      eapply sig_isPair in Hq ; tea.
      destruct Hp, Hq.
      + split.
        2: intros Hne ; inversion Hne.
        econstructor.
        * inversion IHconv ; subst.
          econstructor ; tea.
          all: eapply eta_expand_fst_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
        * inversion IHconv' ; subst.
          econstructor ; tea.
          all: eapply eta_expand_snd_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
      + split.
        2: intros Hne ; inversion Hne.
        econstructor ; tea.
        * inversion IHconv ; subst.
          econstructor ; tea.
          eapply eta_expand_fst_inv ; tea.
          now eapply algo_uconv_wh in H3 as [].
        * inversion IHconv' ; subst.
          econstructor ; tea.
          all: eapply eta_expand_snd_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
      + split.
        2: intros ? Hne ; inversion Hne.
        econstructor ; tea.
        * inversion IHconv ; subst.
          econstructor ; tea.
          eapply eta_expand_fst_inv ; tea.
          now eapply algo_uconv_wh in H3 as [].
        * inversion IHconv' ; subst.
          econstructor ; tea.
          all: eapply eta_expand_snd_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
      + split.
        1: econstructor.
        2: intros _ _.
        all: unshelve (epose proof (IHne _ _) as IHne_ ; inversion IHne_ ; subst ; tea).
        all: now econstructor. 
  Qed.
  
End TypedToUntyped.

(** ** Algorithmic typed neutral comparison *)
(** We prove that algorithmic neutral comparison implies algorithmic conversion, *at all types*.
  The quick proof goes through completeness of algorithmic conversion. Otherwise, we'd
  need deep normalisation of the type… In any case, of form of normalisation is unavoidable:
  at a non-normalising type, a variable is related to itself as a neutral but not as a normal form. *)

Section NeutralConversion.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}
    `{!TypeReductionComplete de} `{!ConvImplies de al}.

  Import AlgorithmicTypingData.

  Lemma ne_conv_conv (Γ : context) (A A' m n : term) :
    [Γ |-[de] A] ->
    isType A ->
    well_typed Γ m ->
    well_typed Γ n ->
    [Γ |-[al] m ~ n ▹ A'] ->
    [Γ |-[de] A' ≅ A] ->
    [Γ |-[al] m ≅h n : A].
  Proof.
    intros * ???? [[]%algo_conv_wh Hconv]%dup ? ; tea.
    eapply algo_conv_sound in Hconv as [[Hconv]%dup] ; tea.
    eapply tm_conv_compl, algo_conv_conv in Hconv ; cycle 1.
    - eapply ctx_refl ; boundary.
    - eassumption.
    - boundary.
    - boundary.
    - destruct Hconv as [??????? hA hm hn] ; subst ; refold.
      eapply red_whnf in hA as -> ; [| gen_typing].
      eapply red_whnf in hm as -> ; [| gen_typing].
      eapply red_whnf in hn as -> ; [| gen_typing].
      assumption.
  Qed.

  Lemma conv_wh_conv_red (Γ : context) (A A' m n : term) :
    [A ⤳* A'] ->
    whnf A' ->
    whnf m ->
    whnf n ->
    [Γ |-[al] m ≅ n : A] ->
    [Γ |-[al] m ≅h n : A'].
  Proof.
    intros hred hA hm hn hconv.
    destruct hconv as [??????? redA ?? hconv] ; refold.
    eapply red_whnf in hm, hn ; tea ; subst.
    eapply whred_det in redA ; tea ; subst.
    2: now eapply algo_conv_wh in hconv as [] ; gen_typing.
    eassumption.
  Qed.

End NeutralConversion.

(** Untyped algorithmic conversion implies typed algorithmic conversion *)

Section UntypedToTyped.
  Context
    `{!TypingSubst de}
    `{!TypeConstructorsInj de}
    `{!TypeReductionComplete de}
    `{!ConvImplies de al}
    `{!Normalisation de}.

  Let PEq (t u : term) :=
    (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[al] t ≅ u]) ×
    (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[al] t ≅ u : A]).

  Let PRedEq (t u : term) :=
    (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[al] t ≅h u]) ×
    (forall Γ A, isType A -> [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[al] t ≅h u : A]).

  Let PNeEq (t u : term) :=
    forall Γ, well_typed Γ t × well_typed Γ u ->
    ∑ A'', [Γ |-[al] t ~ u ▹ A''].

  Lemma uconv_tconv :
    UAlgoConvInductionConcl PEq PRedEq PNeEq.
  Proof.
    subst PEq PRedEq PNeEq.
    unfold UAlgoConvInductionConcl.
    apply UAlgoConvInduction.
    
    - intros * Ht Hu Ht' [Hty Htm].
      split.
      + intros * Hconcl.
        eapply typeConvRed_prem2 in Hconcl.
        2-3: eassumption.
        now econstructor.
      + intros * [Hconcl []]%dup.
        assert [Γ |-[de] A] as [[? ? wh]%ty_norm]%dup by boundary.
        eapply termConvRed_prem3 in Hconcl ; tea.
        econstructor ; eauto.
        eapply Htm ; eauto.
        eapply type_isType ; tea.
        now eapply  subject_reduction_raw_ty.

    - split.
      + now econstructor.
      + intros * ? [[? [[] ]]%termGen' _].

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typePiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, algo_conv_sound, typePiCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros ? T ? [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&->%conv_univ_l) ; tea.
        eapply termPiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_tm, algo_conv_sound, termPiCongAlg_prem1 in Hpre0 ; eauto.
        now econstructor.
        
    - split.
      1: now econstructor.
      intros ? T ? [Hty].

      assert (T = U) as -> by
        now eapply termGen' in Hty as (?&->&?%conv_univ_l).
      constructor.

    - split.
      
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hty].
        assert (T = tNat) as ->.
        {
          eapply termGen' in Hty as (?&->&?%red_compl_nat_l%redty_sound%red_whnf) ; tea.
          gen_typing.
        }
        constructor.

    - split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconcl [Hty]]%dup.
        assert (T = tNat) as ->.
        {
          eapply termGen' in Hty as (?&[->]&?%red_compl_nat_l%redty_sound%red_whnf) ; tea.
          gen_typing.
        }

        eapply termSuccCongAlg_prem0 in Hconcl.
        now constructor.

    - split.
      1: now econstructor.
      intros ? T ? [Hty].
      assert (T = U) as ->.
      {
        eapply termGen' in Hty as (?&->&?%red_compl_univ_l%redty_sound%red_whnf) ; tea.
        gen_typing.
      }
      constructor.

    - intros * ? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconv]%dup.
        eapply LamCongUAlg_prem0_red in Hconv as (?&?&[Hred]); tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.
        
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; eauto.
        1: reflexivity.
        1-2: eapply redalg_one_step, eta_expand_beta.

    - intros * ?? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconv]%dup.
        eapply LamNeUAlg_prem0_red in Hconv as (?&?&[Hred]); tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.
        
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; eauto.
        1,3: reflexivity.
        eapply redalg_one_step, eta_expand_beta.


    - intros * ?? [].
      split.
    
      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconv]%dup.
        eapply NeLamUAlg_prem0_red in Hconv as (?&?&[Hred]); tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.
        
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; eauto.
        1,2: reflexivity.
        eapply redalg_one_step, eta_expand_beta.

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, algo_conv_sound, typeSigCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros ? T ? [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&->%red_compl_univ_l%redty_sound%red_whnf) ; tea.
        2: gen_typing.

        eapply termSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.

        eapply IHA_tm, algo_conv_sound, termSigCongAlg_prem1 in Hpre0 ; eauto.
        now econstructor.

    - intros * Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * ? [Hconcl [[Hty]%dup]]%dup.

        eapply PairCongUAlg_prem0_red in Hconcl as (?&?&[Hred [Hpre0 []]%dup]) ; tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.

        eapply IHp, algo_conv_sound, PairCongUAlg_prem1_red in Hpre0 ; eauto.
        2: reflexivity.
        econstructor.
        1-2: now constructor.

        all: eapply algo_conv_tm_expand.
        all: solve [eapply redalg_one_step ; now constructor | reflexivity | eauto].

      - intros * ? Hp [_ IHp] Hq [_ IHq].
        split.
  
        + intros * [Hz%type_isType _].
          2: constructor.
          inversion Hz ; inv_whne.
  
        + intros * ? [Hconcl [[Hty]%dup]]%dup.
  
          eapply PairNeUAlg_prem0_red in Hconcl as (?&?&[Hred [Hpre0 []]%dup]) ; tea.
          eapply red_whnf in Hred as ->.
          2: gen_typing.
  
          eapply IHp, algo_conv_sound, PairNeUAlg_prem1_red in Hpre0 ; eauto.
          econstructor.
          1-2: now constructor.
          3: reflexivity.
  
          all: eapply algo_conv_tm_expand.
          all: solve [eapply redalg_one_step ; now constructor | reflexivity | eauto].

    - intros * ? Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * ? [Hconcl [[Hty]%dup]]%dup.

        eapply NePairUAlg_prem0_red in Hconcl as (?&?&[Hred [Hpre0 []]%dup]) ; tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.

        eapply IHp, algo_conv_sound, NePairUAlg_prem1_red in Hpre0 ; eauto.
        econstructor.
        1-2: now constructor.
        3: reflexivity.

        all: eapply algo_conv_tm_expand.
        all: solve [eapply redalg_one_step ; now constructor | reflexivity | eauto].
        
    - intros * HA [IHA_ty IHA_tm] Hx [_ IHx_tm] Hy [_ IHy_tm].
      split.

      + intros ? [Hconcl]%dup.
        eapply typeIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, algo_conv_sound in Hpre0 as [Hpost0]%dup; eauto.
        eapply typeIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
        eapply IHx_tm, algo_conv_sound, typeIdCongAlg_prem2 in Hpre1 as [Hpre2]%dup; eauto.
        now econstructor.

      + intros ? T ? [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&->%red_compl_univ_l%redty_sound%red_whnf) ; tea.
        2: gen_typing.

        eapply termIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_tm, algo_conv_sound in Hpre0 as [Hpost0]%dup; eauto.
        eapply termIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
        eapply IHx_tm, algo_conv_sound, termIdCongAlg_prem2 in Hpre1 as [Hpre2]%dup; eauto.
        now econstructor.

    - split.
  
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [[? [[->] Hconv]]%termGen' _].
        eapply red_compl_id_l in Hconv as (?&?&?&[Hred]).
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        econstructor.
      
    - intros * Hconv IH.
      split.
      
      + intros * [Hconcl]%dup.
        eapply algo_uconv_wh in Hconv as [].
        eapply typeNeuConvAlg_prem2 in Hconcl ; tea.
        edestruct IH ; tea.
        now econstructor.

      + intros * ? [Hconcl []]%dup.
        pose proof Hconv as []%algo_uconv_wh.
        eapply termNeuConvAlg_prem0 in Hconcl as [] ; tea.
        edestruct IH as [? IHconv] ; eauto.
        epose proof IHconv as []%algo_conv_sound ; tea.
        eapply ne_conv_conv in IHconv ; eauto.
        boundary.

    - intros * [[? [? [[decl [-> ? Hdecl]] ]]%termGen'] _].
      eexists.
      now econstructor.

    - intros * ? IH ? [_] ? [Hconcl]%dup.

      eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply AppCongUAlg_bridge_red in Hpost0 as (?&?&[? [Hpre1 []]%dup]); eauto.
      eapply neuAppCongAlg_prem1 in Hpre1 ; eauto.
      eexists ; econstructor ; eauto.
      econstructor ; tea.
      constructor.

    - intros * ? IH ? [IHP] ? [_ IHz] ? [_ IHs] ? [Hconcl]%dup.

      eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply NatElimCongUAlg_bridge_red in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuNatElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply algo_conv_sound in Hpos1 as [Hpos1]%dup ; eauto.
      eapply neuNatElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHz in Hpre2 as [Hpos2]%dup ; eauto.
      eapply algo_conv_sound in Hpos2 as [Hpos2]%dup ; eauto.
      eapply neuNatElimCong_prem3 in Hpos2 as [Hpre3 []]%dup ; eauto.
      eapply IHs in Hpre3 as Hpos3 ; eauto.
      eexists ; econstructor ; tea.
      econstructor ; eauto.
      now econstructor.

    - intros * ? IH ? [IHP] ? [Hconcl]%dup.

      eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply EmptyElimCongUAlg_bridge_red in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuEmptyElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eexists.
      repeat (econstructor ; eauto).

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply FstCongUAlg_bridge_red in Hpost0 as (?&?&[? [Hpre1 []]%dup]); eauto.
      eexists ; econstructor ; eauto.
      econstructor ; tea.
      constructor.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply SndCongUAlg_bridge_red in Hpost0 as (?&?&[? [Hpre1 []]%dup]); eauto.
      eexists ; econstructor ; eauto.
      econstructor ; tea.
      constructor.

    - intros * ? IH ? [IHP] ? [_ IHr]  ? [Hconcl]%dup.

      eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply IdElimCongUAlg_bridge_red in Hpost0 as [? (?&?&?&[Hpost0]%dup)]; eauto.
      eapply neuIdElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply algo_conv_sound in Hpos1 as [Hpos1]%dup ; eauto.
      eapply neuIdElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHr in Hpre2 as [Hpos2]%dup ; eauto.
      eexists ; econstructor ; tea.
      econstructor ; eauto.
      now econstructor.
  Qed.

End UntypedToTyped.