(** * LogRel.LogicalRelation.Definition.Empty : Definition of the logical relation for the empty type *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** ** Reducibility of empty type *)
Module EmptyRedTy.

  Record EmptyRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Set :=
  {
    redL : [Γ |- A :⤳*: tEmpty] ;
    redR : [Γ |- B :⤳*: tEmpty]
  }.

  Arguments EmptyRedTy {_ _ _}.
  Section EmptyRedTy.
  Context `{ta : tag} `{WfType ta} `{RedType ta}.

  Definition whredL {Γ A B} : EmptyRedTy Γ A B -> [Γ |- A ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition whredR {Γ A B} : EmptyRedTy Γ A B -> [Γ |- B ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  End EmptyRedTy.
End EmptyRedTy.

Export EmptyRedTy(EmptyRedTy, Build_EmptyRedTy).
Notation "[ Γ ||-Empty A ≅ B ]" := (EmptyRedTy Γ A B) (at level 0, Γ, A at level 50).

#[program]
Instance WhRedTyEmptyRedTy `{GenericTypingProperties} {Γ} : WhRedTyRel Γ (EmptyRedTy Γ) :=
  {|
    whredtyL := fun A B RAB => EmptyRedTy.whredL RAB ;
    whredtyR := fun A B RAB => EmptyRedTy.whredR RAB ;
  |}.
Next Obligation. destruct h; gtyping. Qed.


Module EmptyRedTmEq.
Section EmptyRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Record EmptyRedTmEq {Γ t u} : Set :=
    {
      nfL : term ;
      nfR : term ;
      redL : [Γ |- t :⤳*: nfL : tEmpty] ;
      redR : [Γ |- u :⤳*: nfR : tEmpty ] ;
      eq : [Γ ||-NeNf nfL ≅ nfR : tEmpty]
  }.
  Arguments  EmptyRedTmEq : clear implicits.
  Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Definition whredL {Γ t u} : EmptyRedTmEq Γ t u -> [Γ |- t ↘ tEmpty].
    Proof.
      intros []; econstructor; tea; unshelve eapply NeNf.whredL; cycle 3; tea.
    Defined.

    Definition whredR {Γ t u} : EmptyRedTmEq Γ t u -> [Γ |- u ↘ tEmpty].
    Proof.
      intros []; econstructor; tea; unshelve eapply NeNf.whredR; cycle 3; tea.
    Defined.
  End  Def.

End EmptyRedTmEq.
Arguments EmptyRedTmEq {_ _ _ _}.
End EmptyRedTmEq.

Export EmptyRedTmEq(EmptyRedTmEq,Build_EmptyRedTmEq).

Notation "[ Γ ||-Empty t ≅ u :Empty]" := (@EmptyRedTmEq _ _ _ _ _ _ _ Γ t u).  (* (at level 0, Γ, t, u at level 50). *)

#[program]
Instance EmptyRedTmEqWhRed `{GenericTypingProperties} {Γ} : WhRedTmRel Γ tEmpty (EmptyRedTmEq Γ) :=
  {| whredtmL := fun t u Rtu => EmptyRedTmEq.whredL Rtu ;
    whredtmR := fun t u Rtu => EmptyRedTmEq.whredR Rtu |}.
Next Obligation.
  destruct h as [???? []].
  eapply convtm_convneu; tea; constructor.
Qed.