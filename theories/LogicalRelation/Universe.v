From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance.

Set Universe Polymorphism.
Set Printing Universes.

Section UniverseReducibility.
  Context `{GenericTypingProperties}.

  Lemma redUOneCtx {Γ} : [|- Γ] -> [Γ ||-U<one> U].
  Proof.
    intros ; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
  Defined.

  Lemma redUOne {Γ l A} : [Γ ||-<l> A] -> [Γ ||-U<one> U].
  Proof.
    intros ?%escape; eapply redUOneCtx; gen_typing.
  Qed.

  Lemma UnivEq'@{i j k l} {Γ A B l} (rU : [ LogRel@{i j k l} l | Γ ||- U ]) (rA : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU])
    : [ LogRel@{i j k l} zero | Γ ||- A].
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A ≅ B : U | LRU_@{i j k l} (redUOne rU)]
             as [ ? ?? hA ] by irrelevance.
    exact (LRCumulative hA).
  Qed.

  Lemma UnivEq@{i j k l} {Γ A B l} l' (rU : [ LogRel@{i j k l} l | Γ ||- U]) (rA : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU])
    : [ LogRel@{i j k l} l' | Γ ||- A].
  Proof.
    destruct l'.
    - eapply (UnivEq' rU rA).
    - econstructor. eapply LR_embedding.
      + exact Oi.
      + apply (UnivEq' rU rA).
  Qed.

  Lemma UnivEqEq@{i j k l} {Γ A B l l'} (rU : [ LogRel@{i j k l} l | Γ ||- U ]) (rA : [LogRel@{i j k l} l' | Γ ||- A ]) (rAB : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU ])
    : [ LogRel@{i j k l} l' | Γ ||- A ≅ B | rA ].
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A ≅ B : U | LRU_@{i j k l} (redUOne rU) ] as [ _ _ _ hA _ hAB ] by irrelevance.
    eapply LRTyEqIrrelevantCum. exact hAB.
  Qed.

End UniverseReducibility.
