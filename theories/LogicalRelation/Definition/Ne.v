(** * LogRel.LogicalRelation.Definition.Ne : Definition of the logical relation for neutal types and terms *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** ** Reducibility of neutral types *)

Module neRedTy.

  Record neRedTy `{ta : tag}
    `{WfType ta} `{ConvNeuConv ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Set := {
    tyL : term;
    redL : [ Γ |- A :⤳*: tyL];
    tyR : term;
    redR : [ Γ |- B :⤳*: tyR];
    eq : [ Γ |- tyL ~ tyR : U] ;
  }.

  Arguments neRedTy {_ _ _ _}.

  Definition whredL `{GenericTypingProperties} {Γ : context} {A B : term} :
    neRedTy Γ A B -> [Γ |- A ↘ ].
  Proof. intros []; econstructor; tea; constructor; now eapply convneu_whne. Defined.

  Definition whredR `{GenericTypingProperties} {Γ : context} {A B : term} :
    neRedTy Γ A B -> [Γ |- B ↘ ].
  Proof. intros []; econstructor; tea; constructor; eapply convneu_whne; now symmetry. Defined.

End neRedTy.

Export neRedTy(neRedTy, Build_neRedTy).
Notation "[ Γ ||-ne A ≅ B ]" := (neRedTy Γ A B).

#[program]
Instance neRedTyWhRedTy `{GenericTypingProperties} {Γ} : WhRedTyRel Γ (neRedTy Γ) :=
  {| whredtyL := fun A B RAB => neRedTy.whredL RAB ;
     whredtyR := fun A B RAB => neRedTy.whredR RAB ;
  |}.
Next Obligation.
  destruct h.
  eapply convty_term, convtm_convneu; tea; constructor.
Qed.


Module neRedTmEq.

  Record neRedTmEq `{ta : tag}
    `{WfType ta} `{RedType ta}
    `{Typing ta} `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A B : term} {R : [ Γ ||-ne A ≅ B]} {t u  : term}
  : Set := {
    termL     : term;
    termR     : term;
    redL      : [ Γ |- t :⤳*: termL : R.(neRedTy.tyL) ];
    redR      : [ Γ |- u :⤳*: termR : R.(neRedTy.tyL) ];
    eq : [ Γ |- termL ~ termR : R.(neRedTy.tyL)] ;
  }.

  Arguments neRedTmEq {_ _ _ _ _ _ _ _ _ _ _} _ _ _.

  Definition whredL `{GenericTypingProperties} {Γ : context} {t u A B : term} {R : [ Γ ||-ne A ≅ B]} :
    neRedTmEq R t u -> [Γ |- t ↘  R.(neRedTy.tyL)].
  Proof.  intros []; econstructor; tea; constructor; now eapply convneu_whne. Defined.

  Definition whredR `{GenericTypingProperties} {Γ : context} {t u A B : term} {R : [ Γ ||-ne A ≅ B]} :
    neRedTmEq R t u -> [Γ |- u ↘  R.(neRedTy.tyL)].
  Proof. intros []; econstructor; tea; constructor; eapply convneu_whne; now symmetry. Defined.

End neRedTmEq.

Export neRedTmEq(neRedTmEq, Build_neRedTmEq).
Notation "[ Γ ||-ne t ≅ u : A | R ] " := (neRedTmEq (Γ:=Γ) (A:=A) R t u).

#[program]
Instance neRedTmWhRedTm `{GenericTypingProperties} {Γ A B} (R : [Γ ||-ne A ≅ B]) : WhRedTmRel Γ (neRedTy.tyL R) (neRedTmEq R) :=
  {| whredtmL := fun t u Rtu => neRedTmEq.whredL Rtu ;
     whredtmR := fun t u Rtu => neRedTmEq.whredR Rtu ;
  |}.
Next Obligation.
  destruct h; cbn; eapply convtm_convneu; tea.
  destruct R; cbn in *; constructor; now eapply convneu_whne.
Qed.

(** ** Reducibility of neutrals at an arbitrary type *)

Module NeNf.

  Record RedTmEq `{ta : tag} `{Typing ta} `{ConvNeuConv ta} {Γ A k l} : Set :=
    {
      tyL : [Γ |- k : A] ;
      tyR : [Γ |- l : A] ;
      conv : [Γ |- k ~ l : A]
    }.

  Arguments RedTmEq {_ _ _}.

  Definition whredL `{GenericTypingProperties} {Γ : context} {t u A : term} :
    RedTmEq Γ A t u -> [Γ |- t ↘  A].
  Proof.
    intros []; econstructor.
    1: now eapply redtmwf_refl.
    constructor; now eapply convneu_whne.
  Defined.

  Definition whredR `{GenericTypingProperties} {Γ : context} {t u A : term} :
    RedTmEq Γ A t u -> [Γ |- u ↘  A].
  Proof.
    intros []; econstructor.
    1: now eapply redtmwf_refl.
    constructor; eapply convneu_whne; now symmetry.
  Defined.

  Definition conv_ `{GenericTypingProperties} {Γ : context} {t u A B : term} :
    [Γ |- A ≅ B] -> RedTmEq Γ A t u -> RedTmEq Γ B t u.
  Proof.
    intros ? []; econstructor.
    1,2: now eapply ty_conv.
    now eapply convneu_conv.
  Qed.

End NeNf.

Notation "[ Γ ||-NeNf k ≅ l : A ]" := (NeNf.RedTmEq Γ A k l) (at level 0, Γ, k, l, A at level 50).


#[program]
Instance NeNfWhRedTm `{GenericTypingProperties} {Γ A} (posA : isPosType A) : WhRedTmRel Γ A (NeNf.RedTmEq Γ A) :=
  {| whredtmL := fun t u Rtu => NeNf.whredL Rtu ;
     whredtmR := fun t u Rtu => NeNf.whredR Rtu ;
  |}.
Next Obligation.
  destruct h; now eapply convtm_convneu.
Defined.