
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
From LogRel.Substitution Require Import Irrelevance Properties.

Set Universe Polymorphism.

Section Escape.
Context `{GenericTypingProperties}.

Lemma reducibleTy {wl Γ l A} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : [Γ ||-<l> A]< wl >.
Proof.
  replace A with A[tRel] by now asimpl.
  eapply validTy; tea.
  apply idSubstS.
Qed.

Lemma reducibleTyEq {wl Γ l A B} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) :
  [Γ ||-v<l> A ≅ B | VΓ | VA]< wl > -> [Γ ||-<l> A ≅ B | reducibleTy VΓ VA]< wl >.
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace B with B[tRel] by now asimpl.
  unshelve epose proof (validTyEq X _ (idSubstS VΓ)).
  irrelevance.
Qed.

Lemma reducibleTm {wl Γ l A t} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t : A | VΓ | VA]< wl > -> [Γ ||-<l> t : A | reducibleTy VΓ VA]< wl >.
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace t with t[tRel] by now asimpl.
  unshelve epose proof (validTm X _ (idSubstS VΓ)).
  irrelevance.
Qed.

Lemma reducibleTmEq {wl Γ l A t u} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl > -> [Γ ||-<l> t ≅ u : A | reducibleTy VΓ VA]< wl >.
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace t with t[tRel] by now asimpl.
  replace u with u[tRel] by now asimpl.
  unshelve epose proof (validTmEq X _ (idSubstS VΓ)).
  irrelevance.
Qed.

Lemma escapeTy {wl Γ l A} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : [Γ |- A]< wl >.
Proof. eapply escape; now eapply reducibleTy. Qed.


Lemma escapeEq {wl Γ l A B} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> A ≅ B | VΓ | VA]< wl > -> [Γ |- A ≅ B]< wl >.
Proof.
  intros; unshelve eapply escapeEq; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTyEq.
Qed.

Lemma escapeTm {wl Γ l A t} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t : A | VΓ | VA]< wl > -> [Γ |- t : A]< wl >.
Proof.
  intros; unshelve eapply escapeTerm; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTm.
Qed.

Lemma escapeTmEq {wl Γ l A t u} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl > -> [Γ |- t ≅ u : A]< wl >.
Proof.
  intros; unshelve eapply escapeEqTerm; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTmEq.
Qed.

End Escape.
