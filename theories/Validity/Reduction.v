From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral Reduction Transitivity.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma redSubstValid {Γ A t u l}
  (VΓ : [||-v Γ])
  (red : [Γ ||-v t ⤳* u : A | VΓ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vu : [Γ ||-v<l> u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA].
Proof.
  constructor; intros. eapply redSubstLeftTmEq.
  1: now eapply validTmExt.
  now eapply validRed.
Qed.

End Reduction.