(** * LogRel.Consequences: important meta-theoretic consequences of normalization: canonicity of natural numbers and consistency. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  LogicalRelation Fundamental Validity LogicalRelation.Induction Substitution.Escape LogicalRelation.Irrelevance
  GenericTyping DeclarativeTyping DeclarativeNeutralConv TypeConstructorsInj Normalisation.


Import DeclarativeTypingData DeclarativeTypingProperties.


Lemma no_neutral_empty_ctx {A t} : whne t -> [ε |-[de] t : A] -> False.
Proof.
  intros wh; induction wh in A |- *.
  - intros [? [[? [?? h]]]]%termGen'; inversion h.
  - intros [? [[? [? []]]]]%termGen'; eauto.
  - intros [? [[? []]]]%termGen'; eauto.
  - intros [? [[? []]]]%termGen'; eauto.
  - intros [? [[? [? []]]]]%termGen'; eauto.
  - intros [? [[? [? []]]]]%termGen'; eauto.
  - intros [? [[?]]]%termGen'; eauto.
Qed.

Lemma wty_norm {Γ t A} : [Γ |- t : A] ->
  ∑ wh, [× whnf wh, [Γ |- t ⤳* wh : A]& [Γ |- wh : A]].
Proof.
  intros wtyt.
  pose proof (normalisation wtyt) as [wh red].
  pose proof (h := subject_reduction _ _ _ _ wtyt red).
  assert [Γ |- wh : A] by (destruct h; boundary).
  now eexists.
Qed.

(** *** Consistency: there are no closed proofs of false, i.e. no closed inhabitants of the empty type. *)

Lemma consistency {t} : [ε |- t : tEmpty] -> False.
Proof.
  intros [wh []]%wty_norm; refold.
  eapply no_neutral_empty_ctx; tea.
  eapply empty_isEmpty; tea.
Qed.

Print Assumptions consistency.

(** *** Canonicity: every closed natural number is a numeral, i.e. an iteration of [tSucc] on [tZero]. *)

Section NatCanonicityInduction.

  Let numeral : nat -> term := fun n => Nat.iter n tSucc tZero.

  #[local] Coercion numeral : nat >-> term.

  #[local] Lemma red_nat_empty : [ε ||-Nat tNat].
  Proof.
    repeat econstructor.
  Qed.

  Lemma nat_red_empty_ind :
    (forall t u, [ε ||-Nat t ≅ u : tNat | red_nat_empty] ->
    ∑ n : nat, [ε |- t ≅ n : tNat]) ×
    (forall t u, NatPropEq red_nat_empty t u -> ∑ n : nat, [ε |- t ≅ n : tNat]).
  Proof.
    apply NatRedEqInduction.
    - intros * [? []] ? ? _ [n] ; refold.
      exists n.
      now etransitivity.
    - exists 0 ; cbn.
      now repeat constructor.
    - intros ? ? _ [n].
      exists (S n) ; simpl.
      now econstructor.
    - intros ? [? ?].
      exfalso.
      eapply no_neutral_empty_ctx ; tea.
      now eapply convneu_whne.
  Qed.

  Lemma _nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ n : tNat].
  Proof.
    intros Ht.
    assert [LRNat_ one red_nat_empty | ε ||- t : tNat] as ?%nat_red_empty_ind.
    {
      apply Fundamental in Ht as [?? Vt%reducibleTmEq].
      irrelevance.
    }
    now assumption.
  Qed.

End NatCanonicityInduction.

Lemma nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
Proof.
  now apply _nat_canonicity.
Qed.