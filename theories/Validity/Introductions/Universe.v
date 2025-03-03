From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe.
From LogRel.Validity Require Import Validity Irrelevance Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Universe.
Context `{GenericTypingProperties} {Γ Γ' : context}.

Lemma UValid (VΓ : [||-v Γ ≅ Γ' ]) : [Γ ||-v<one> U | VΓ].
Proof.  unshelve econstructor; intros; now eapply LRU_, redUOneCtx. Defined.

Lemma univValid {A A' l} l' {VΓ : [||-v Γ ≅ Γ']}
  {VU : [Γ ||-v<l> U | VΓ]}
  (VA : [Γ ||-v<l> A ≅ A' : U | VΓ | VU]) :
  [Γ ||-v<l'> A ≅ A' | VΓ].
Proof. constructor; intros ???? Vσ ; eapply UnivEq; exact (validTmExt VA _ Vσ). Qed.

End Universe.