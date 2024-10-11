(** * LogRel.NormalisationConsequences: direct consequences of normalisation. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping PropertiesDefinition SubstConsequences TypeConstructorsInj.

Import DeclarativeTypingData.

(** ** Well-foundedness of reduction *)

Theorem typing_acc_cored Γ t `{!Normalisation (ta := de)} :
  well_formed Γ t ->
  Acc cored t.
Proof.
  intros [[] Hty].
  all: first [
    apply ty_norm in Hty as [wh red] |
    apply tm_norm in Hty as [wh red]].
  all: induction red.
  - econstructor.
    intros t' [red].
    exfalso.
    eapply whnf_nored ; tea.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
  - econstructor.
    intros t' [red].
    exfalso.
    now eapply whnf_nored.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
Qed.

(** ** Consistency *)
(** There are no closed proofs of false, i.e. no closed inhabitants of the empty type.*)

Section Consistency.
  Context `{!TypingSubst (ta := de)}
    `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}
    `{!Normalisation (ta := de)}.


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
    pose proof (tm_norm wtyt) as [wh red].
    pose proof (h := subject_reduction _ _ _ _ wtyt red).
    assert [Γ |- wh : A] by (destruct h; boundary).
    now eexists.
  Qed.

  Lemma consistency {t} : [ε |- t : tEmpty] -> False.
  Proof.
    intros [wh []]%wty_norm; refold.
    eapply no_neutral_empty_ctx; tea.
    eapply empty_isEmpty; tea.
  Qed.

End Consistency.