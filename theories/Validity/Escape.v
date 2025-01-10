From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
From LogRel.Validity Require Import Validity Irrelevance Properties.

Set Universe Polymorphism.

Section Escape.
Context `{GenericTypingProperties}.

Lemma reducibleTy {Γ l A} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) : [Γ ||-<l> A].
Proof.
  replace A with A[tRel] by now asimpl.
  eapply validTy; tea.
  apply idSubstS.
Qed.

Lemma reducibleTyEq {Γ l A B} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
  [Γ ||-v<l> A ≅ B | VΓ | VA] -> [Γ ||-<l> A ≅ B | reducibleTy VΓ VA].
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace B with B[tRel] by now asimpl.
  unshelve epose proof (validTyEq X _ (idSubstS VΓ)).
  irrelevance.
Qed.

Lemma reducibleTmEq {Γ l A t u} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA] -> [Γ ||-<l> t ≅ u : A | reducibleTy VΓ VA].
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace t with t[tRel] by now asimpl.
  replace u with u[tRel] by now asimpl.
  unshelve epose proof (validTmEq X _ (idSubstS VΓ)).
  irrelevance.
Qed.

Lemma escapeTy {Γ l A} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) : [Γ |- A].
Proof. eapply escape; now eapply reducibleTy. Qed.


Lemma escapeEq {Γ l A B} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
  [Γ ||-v<l> A ≅ B | VΓ | VA] -> [Γ |- A ≅ B].
Proof.
  intros; unshelve eapply escapeEq; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTyEq.
Qed.

Lemma escapeTmEq {Γ l A t u} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA] -> [Γ |- t ≅ u : A].
Proof.
  intros; unshelve eapply escapeEqTerm; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTmEq.
Qed.

Lemma escapeTm {Γ l A t u} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA] -> [Γ |- t : A].
Proof.
  intros; unshelve eapply escapeTerm; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTmEq.
Qed.

End Escape.
