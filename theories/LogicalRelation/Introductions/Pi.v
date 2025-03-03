From Coq Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly.

Set Universe Polymorphism.

Section PolyRedPi.
  Context `{GenericTypingProperties}.

  Lemma LRPiPoly0 {Γ l A A' B B'} (wfΓ : [|- Γ]) (PAB : PolyRed Γ l A A' B B') : [Γ ||-Π<l> tProd A B ≅ tProd A' B'].
  Proof.
    eapply mkParamRedTy; tea; intros; gtyping.
  Defined.

  Definition LRPiPoly {Γ l A A' B B'} (wfΓ : [|- Γ]) (PAB : PolyRed Γ l A A' B B') :
    [Γ ||-<l> tProd A B ≅ tProd A' B'] :=
    LRPi' (LRPiPoly0 wfΓ PAB).

End PolyRedPi.
