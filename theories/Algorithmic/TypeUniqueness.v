(** * LogRel.TypeUniqueness: all types for a term are convertible. *)

From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeConstructorsInj NeutralConvProperties.
From LogRel.Algorithmic Require Import BundledAlgorithmicTyping AlgorithmicTypingProperties.

Import DeclarativeTypingProperties AlgorithmicTypingData BundledTypingData AlgorithmicTypingProperties.

Section AlgorithmicUnique.

  Lemma algo_typing_unique : AlgoTypingInductionConcl
    (fun Γ A => True)
    (fun Γ A t => forall A', [Γ |-[al] t ▹ A'] -> A' = A)
    (fun Γ A t => forall A', [Γ |-[al] t ▹h A'] -> ∑ A'', [A'' ⤳* A] × [A'' ⤳* A'])
    (fun Γ A t => True).
  Proof.
    apply AlgoTypingInduction.
    all: try easy.
    all: try solve [intros ** ; match goal with H : context [al] |- _ => now inversion H end].
    - intros * ? * Hty'.
      inversion Hty' ; subst.
      now eapply in_ctx_inj.
    - intros * _ _ _ IHt ? Hty'.
      inversion Hty' ; subst ; refold.
      now erewrite <- IHt.
    - intros * _ IHf _ _ ? Hty'.
      inversion Hty' ; subst ; refold.
      eapply IHf in H3 as [? [Hred Hred']].
      eapply whred_det in Hred ; tea.
      2-3: gen_typing.
      now inversion Hred.
    - intros * ? ih ? hty.
      inversion hty; subst; refold.
      edestruct ih as [? [r r']]; tea.
      unshelve epose (e := whred_det _ _ _ _ _ r r'); try constructor.
      now injection e.
    - intros * ? ih ? hty.
      inversion hty; subst; refold.
      edestruct ih as [? [r r']]; tea.
      unshelve epose (e := whred_det _ _ _ _ _ r r'); try constructor.
      injection e; clear e; intros; now subst.
    - intros * _ IHt ? ? Hty'.
      inversion Hty' ; subst ; refold.
      eapply IHt in H0 as ->.
      now eexists.
  Qed.

End AlgorithmicUnique.

Corollary typing_unique Γ T T' t :
  [Γ |-[de] t : T] ->
  [Γ |-[de] t : T'] ->
  [Γ |-[de] T ≅ T'].
Proof.
  intros [_ Ti Hty]%algo_typing_complete [_ Ti' Hty']%algo_typing_complete.
  eapply algo_typing_unique in Hty ; tea ; subst.
  etransitivity ; tea.
  now symmetry.
Qed.  