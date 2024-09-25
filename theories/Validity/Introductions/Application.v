From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.

Set Universe Polymorphism.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Set Printing Universes.

Lemma appcongValid {Γ F G t u a b l}
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]}
  (Vtu : [Γ ||-v<l> t ≅ u : tProd F G | VΓ | VΠFG])
  (Va : [Γ ||-v<l> a : F | VΓ | VF])
  (Vb : [Γ ||-v<l> b : F | VΓ | VF])
  (Vab : [Γ ||-v<l> a ≅ b : F | VΓ | VF])
  (VGa := substSΠ VΠFG Va) :
  [Γ ||-v<l> tApp t a ≅ tApp u b : G[a..] | VΓ | VGa].
Proof.
  constructor; intros; instValid Vσσ'.
  pose proof (h := substSΠaux VΠFG Va _ _ _ wfΔ Vσσ').
  pose proof (appcongTerm _ RVtu RVab h).
  irrelevance.
Qed.

Lemma appValid {Γ F G t u l}
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]}
  (Vt : [Γ ||-v<l> t : tProd F G | VΓ | VΠFG])
  (Vu : [Γ ||-v<l> u : F | VΓ | VF])
  (VGu := substSΠ VΠFG Vu) :
  [Γ ||-v<l> tApp t u : G[u..] | VΓ | VGu].
Proof.
  eapply lreflValidTm, appcongValid.
  1,3: now eapply reflValidTm.
  tea.
Qed.


End Application.
