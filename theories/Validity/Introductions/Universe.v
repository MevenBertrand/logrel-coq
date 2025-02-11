From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Introductions.Universe.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion Reflexivity.

Set Universe Polymorphism.

Section Universe.
Context `{GenericTypingProperties} {Γ : context}.

Lemma UValid (VΓ : [||-v Γ]) : [Γ ||-v<one> U | VΓ].
Proof.
  unshelve econstructor; intros.
  - now eapply LRU_, redUOneCtx.
  - cbn; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma univValid {A l l'} (VΓ : [||-v Γ])
  (VU : [Γ ||-v<l> U | VΓ])
  (VA : [Γ ||-v<l> A : U | VΓ | VU]) :
  [Γ ||-v<l'> A| VΓ].
Proof.
  unshelve econstructor; intros.
  - instValid vσ. now eapply UnivEq.
  - instValid  vσσ'; now eapply UnivEqEq.
Qed.

Lemma univEqValid {A B l l'} (VΓ : [||-v Γ])
  (VU : [Γ ||-v<l'> U | VΓ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VAB : [Γ ||-v<l'> A ≅ B : U | VΓ | VU]) :
  [Γ ||-v<l> A ≅ B | VΓ | VA].
Proof.
  constructor; intros; instValid Vσσ'.
  now eapply UnivEqEq.
Qed.

End Universe.