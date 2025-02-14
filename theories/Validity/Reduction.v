From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma redSubstValid {Γ Γ' A A' t u l}
  (VΓ : [||-v Γ ≅ Γ'])
  (red : [Γ ||-v t ⤳* u : A | VΓ])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vu : [Γ ||-v<l> u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA].
Proof.
  constructor; intros. eapply redSubstLeftTmEq.
  1: now eapply validTmExt.
  now eapply validRed.
Qed.

End Reduction.