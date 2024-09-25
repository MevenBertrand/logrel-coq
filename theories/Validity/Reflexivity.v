From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Reflexivity.
From LogRel.Validity Require Import Validity.

Set Universe Polymorphism.

Section Reflexivity.
Context `{GenericTypingProperties}.

Lemma reflValidTy {Γ A l} {VΓ : [||-v Γ]}
  (VA : [Γ ||-v<l> A | VΓ]) :
  [Γ ||-v<l> A ≅ A | VΓ | VA].
Proof.
  constructor; intros; eapply validTyExt.
Qed.
Set Printing Primitive Projection Parameters.

Lemma ureflValidTy {Γ A B l} {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  (VAB : [Γ ||-v<l> A ≅ B | VΓ | VA]) :
  [Γ ||-v<l> B | VΓ ].
Proof.
  unshelve econstructor; intros.
  1: (unshelve now eapply LRTyEqRedRight, validTyEq); [tea| |now eapply lrefl].
  eapply LRTransEq.
  2: (unshelve now eapply validTyEq); cycle 2; tea.
  eapply LRTyEqSym.
  (unshelve now eapply validTyEq); tea; now eapply lrefl.
Qed.

#[deprecated(note="Unneeded")]
Lemma reflValidTm {Γ t A l} {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ t : A | VΓ | VA].
Proof. exact Vt. Qed.

Lemma lreflValidTm {Γ t u A l} (VΓ : [||-v Γ])
  {VA : [Γ ||-v<l> A | VΓ]}
  (Vtu : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Γ ||-v<l> t : A | VΓ | VA].
Proof.
  constructor; intros.
  etransitivity; [now eapply validTmEq|symmetry].
  eapply LRTmEqConv.
  2: now eapply validTmEq.
  eapply LRTyEqSym.
  eapply validTyExt.
  Unshelve. 1,6-8:tea. now eapply urefl.
Qed.

Lemma ureflValidTm {Γ t u A l}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  (Vtu : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Γ ||-v<l> u : A | VΓ | VA].
Proof.
  eapply lreflValidTm; now eapply symValidTmEq.
Qed.

End Reflexivity.