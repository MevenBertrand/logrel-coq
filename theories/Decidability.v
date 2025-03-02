(** * LogRel.Decidability: type-checking is decidable. *)
From Equations Require Import Equations.
From LogRel Require Import Utils Syntax.All DeclarativeTyping GenericTyping
  AlgorithmicTyping BundledAlgorithmicTyping AlgorithmicConvProperties
  AlgorithmicTypingProperties PropertiesDefinition NeutralConvProperties LogRelConsequences.

From LogRel.Decidability Require Import Functions Soundness Completeness Termination.
From PartialFun Require Import Monad PartialFun MonadExn.

Import AlgorithmicTypingProperties DeclarativeTypingProperties.
Set Universe Polymorphism.

Import IntermediateTypingProperties BundledTypingData.

#[local]Existing Instance TypingSubstLogRel.
#[local]Existing Instance RedCompleteLogRel.
#[local]Existing Instance TypeConstructorsInjLogRel.
#[local]Existing Instance NormalisationLogRel.
#[local]Existing Instance ConvCompleteLogRel.
#[local]Existing Instance TypingCompleteLogRel.

Definition inspect {A} (a : A) : ∑ b, a = b :=
  (a;eq_refl).
  
Notation "x 'eqn:' p" := ((x;p)) (only parsing, at level 20).

#[global]
Obligation Tactic := idtac.

Equations check (Γ : context) (t T : term) (hΓ : [|- Γ]) (hT : [Γ |- T]) :
  [Γ |- t : T] + ~[Γ |- t : T] :=

check Γ t T hΓ hT with (inspect (def (typing tconv) (check_state;Γ;T;t) _)) :=
  {
    | success _ eqn: e => inl _
    | exception _ eqn: e => inr _
  }.
Next Obligation.
  intros.
  apply typing_terminates ; tea.
  - apply implem_tconv_sound.
  - now intros ; eapply tconv_terminates.
Qed.
Next Obligation.
  intros * e ; cbn in *.
  apply bn_alg_typing_sound.
  epose proof (def_graph_sound _ _ _) as Hgraph.
  rewrite e in Hgraph.
  apply implem_typing_sound in Hgraph ; cbn in Hgraph.
  2: apply implem_tconv_sound.
  now constructor.
Qed.
Next Obligation.
  intros * e Hty ; cbn in *.
  set (Hter := check_obligations_obligation_1 _ _ _ _ _) in *.
  clearbody Hter.
  pose proof (def_graph_sound _ _ Hter) as Hgraph.
  enough (graph (typing tconv) (check_state;Γ;T;t) ok).
  {
    eapply orec_graph_functional in Hgraph ; tea.
    assert (ok = exception e0) as [=] by (etransitivity ; eassumption).
  }

  change [Γ |-[de] t : T] in Hty.
  eapply (tm_compl (ta' := bn)) in Hty as [].

  apply typing_complete.
  1: now apply implem_conv_complete.
  constructor ; tea.
  econstructor ; tea.
  now apply ty_conv_compl.
Qed.

Print Assumptions check.