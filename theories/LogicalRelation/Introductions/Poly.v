From Coq Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section PolyValidity.

  Context `{GenericTypingProperties}.

  Lemma mkParamRedTy {T}
    (wtyT : forall Γ A B, [Γ |- A] -> [Γ,, A |- B] -> [Γ |- T A B])
    (convT : forall Γ A A' B B', [Γ |- A] -> [Γ |- A ≅ A'] -> [Γ,, A |- B ≅ B'] -> [Γ |- T A B ≅ T A' B'])
    {Γ l A A' B B'} (wfΓ : [|-Γ]) (PA : PolyRed Γ l A A' B B') :
    ParamRedTy T Γ l (T A B) (T A' B').
  Proof.
    pose proof (instKripke wfΓ PA.(PolyRed.shpRed)).
    pose proof (instKripkeFam wfΓ PA.(PolyRed.posRed)).
    pose proof (instKripkeFamConv wfΓ PA.(PolyRed.posRed)).
    escape.
    exists A A' B B'; tea.
    1,2: econstructor; tea; eapply redtywf_refl; eauto.
    eauto.
  Defined.

End PolyValidity.
