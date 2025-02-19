(** * LogRel.Decidability: type-checking is decidable. *)
From Equations Require Import Equations.
From LogRel Require Import Utils Syntax.All DeclarativeTyping GenericTyping
  AlgorithmicTyping BundledAlgorithmicTyping AlgorithmicConvProperties
  AlgorithmicTypingProperties PropertiesDefinition NeutralConvProperties NormalisationConsequences LogRelConsequences.

From LogRel.Decidability Require Import Functions Soundness NegativeSoundness Termination.
From PartialFun Require Import Monad PartialFun MonadExn.

Import AlgorithmicTypingProperties AlgorithmicTypedConvData DeclarativeTypingProperties.
Set Universe Polymorphism.

Import IntermediateTypingProperties BundledTypingData.

#[local]Existing Instances
  TypingSubstLogRel RedCompleteLogRel TypeConstructorsInjLogRel
  TermConstructorsInjLogRel ConvNeutralConvPosLogRel
  ConvImpliesLogRel CompleteAlgoNormalisation.

Definition inspect {A} (a : A) : ∑ b, a = b :=
  (a;eq_refl).
  
Notation "x 'eqn:' p" := ((x;p)) (only parsing, at level 20).

#[global]
Obligation Tactic := idtac.

Equations check (Γ : context) (t T : term) (hΓ : [|-[de] Γ]) (hT : [Γ |-[de] T]) :
  [Γ |-[de] t : T] + ~[Γ |-[de] t : T] :=

check Γ t T hΓ hT with (inspect (def (typing tconv) (check_state;Γ;T;t) _)) :=
  {
    | success _ eqn: e => inl _
    | exception _ eqn: e => inr _
  }.
Next Obligation.
  intros.
  apply (typing_terminates (ta := al)) ; tea.
  - now intros * ?? ?%algo_conv_sound. 
  - intros. now apply implem_tconv_sound.
  - now intros ; eapply tconv_terminates.
Qed.
Next Obligation.
  intros * e ; cbn in *.
  apply bn_alg_typing_sound.
  epose proof (def_graph_sound _ _ _) as Hgraph.
  rewrite e in Hgraph.
  apply (implem_typing_sound (ta := al)) in Hgraph ; cbn in Hgraph.
  2: apply implem_tconv_sound.
  now constructor.
Qed.
Next Obligation.
  intros * e Hty ; cbn in *.
  set (Hter := check_obligations_obligation_1 _ _ _ _ _) in *.
  clearbody Hter.
  pose proof (def_graph_sound _ _ Hter) as Hgraph.
  rewrite e in Hgraph.
  eapply (implem_typing_sound_neg (ta := al)) in Hgraph ; cbn in * ; eauto.
  + now intros * ?? ?%algo_conv_sound.
  + eapply implem_tconv_sound.
  + intros ; eapply implem_tconv_sound_neg ; tea.
Qed.

Print Assumptions check.