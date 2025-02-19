(** * LogRel.NormalisationConsequences: direct consequences of normalisation. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping PropertiesDefinition SubstConsequences NeutralConvProperties TypeConstructorsInj DeclarativeProperties Normalisation.

Import DeclarativeTypingProperties.


#[refine]Instance NormDeepNorm `{ta : tag} `{DeepNormalisation ta} : Normalisation ta := {}.
Proof.
  - intros * [* ?? ?%dnf_whnf]%tm_dnorm.
    now econstructor.
  - intros * [* ? ?%dnf_whnf]%ty_dnorm.
    econstructor ; gen_typing.
Qed.

(** ** Well-foundedness of reduction *)

Theorem typing_acc_cored Γ t `{!Normalisation de} :
  well_formed Γ t ->
  Acc cored t.
Proof.
  intros [[] Hty] ; cbn in Hty.
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
  Context `{!TypingSubst de}
    `{!TypeReductionComplete de} `{!TypeConstructorsInj de}
    `{!Normalisation de}.


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


(** ** Canonicity *)
(** Every closed natural number is convertible to a numeral. Note that we really need
  deep normalisation here, with only wh normalisation we would only get that a closed natural
  number is convertible to 0 or a successor, but would have no control over the argument of the latter. *)
Section Canonicity.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}
    `{!DeepNormalisation de}.

  Let Pnorm Γ A t := (Γ = ε) -> A = tNat -> [ε |- t : tNat] ->
    ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
  Let Pnf Γ A t := (Γ = ε) -> A = tNat -> [ε |- t : tNat] ->
    ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
  Let Pneu (Γ : context) (A t : term) := True.
  Let Pty (Γ : context) (A : term) := True.

  Lemma nat_canonicity {t} : [ε |- t : tNat] ->
    ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
  Proof.
    intros [Hty Hnorm%tm_dnorm]%dup.
      epose proof (DeepNormInduction Pnorm Pnf Pneu Pneu Pty Pty) as
      [Hconcl _] ; cycle -1.
    1:{
      unfold Pnorm in Hconcl.
      eapply Hconcl.
      all: eauto.
    }
    all: clear Hty Hnorm ; unfold Pnorm, Pnf, Pneu, Pty ; cbn ; try solve [constructor].
    all: try solve [congruence].
    - intros * Hred Hred' _ IH -> -> Hty.
      eapply red_whnf in Hred ; subst ; [..|gen_typing].
      eapply subject_reduction in Hred' ; tea.
      edestruct IH ; eauto.
      1: boundary.
      eexists ; etransitivity ; tea.
      now eapply RedConvTeC.
    - intros.
      exists 0 ; cbn.
      now constructor.
    - intros * _ IH -> _ (?&[->]&?)%termGen'.
      destruct IH ; eauto.
      eexists (S _) ; cbn.
      now constructor.
    - intros * ? Hne ** ; subst.
      exfalso.
      eapply no_neutral_empty_ctx ; tea.
      now eapply dnf_whnf in Hne.
  Qed.

End Canonicity.