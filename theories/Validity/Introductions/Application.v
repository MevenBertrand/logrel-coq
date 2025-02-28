From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import  Properties Introductions.Application.
From LogRel.Validity Require Import Validity Irrelevance Properties Pi ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Universes.

Lemma appcongValid {Γ Γ' F F' G G' t u a b l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VΠFG : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ]}
  (Vtu : [Γ ||-v<l> t ≅ u : tProd F G | VΓ | VΠFG])
  (Vab : [Γ ||-v<l> a ≅ b : F | VΓ | _])
  (VGa := substSΠ VΠFG Vab) :
  [Γ ||-v<l> tApp t a ≅ tApp u b : G[a..] | VΓ | VGa].
Proof.
  constructor; intros; instValid Vσσ'; cbn.
  unshelve eapply irrLREq; cycle -1.
  1: eapply (appcongTerm RVΠFG RVtu RVab).
  all: refold; now rewrite <-!singleSubstComm'.
Qed.

Lemma appcongValid' {Γ Γ' F F' G G' C C' t u a b l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VΠFG : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ]}
  (Vtu : [Γ ||-v<l> t ≅ u : tProd F G | VΓ | VΠFG])
  (Vab : [Γ ||-v<l> a ≅ b : F | VΓ | validΠdom VΠFG])
  (VC : [Γ ||-v<l> C ≅ C' | VΓ])
  (eqC : C = G[a..]):
  [Γ ||-v<l> tApp t a ≅ tApp u b : C | VΓ | VC].
Proof.
  eapply irrValidTm, appcongValid; tea.
  rewrite <-eqC; irrValid.
  Unshelve. all: irrValid.
Qed.

Lemma appValid {Γ F G t u l}
  {VΓ : [||-v Γ]}
  (* {VF : [Γ ||-v<l> F | VΓ]} *)
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]}
  (Vt : [Γ ||-v<l> t : tProd F G | VΓ | VΠFG])
  (Vu : [Γ ||-v<l> u : F | VΓ | _])
  (VGu := substSΠ VΠFG Vu) :
  [Γ ||-v<l> tApp t u : G[u..] | VΓ | VGu].
Proof.
  eapply lrefl, appcongValid; tea.
Qed.


End Application.
