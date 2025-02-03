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


Module neRedTmEq.

  Record neRedTmEq `{ta : tag}
    `{WfType ta} `{RedType ta}
    `{Typing ta} `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t u A B : term} {R : [ Γ ||-ne A ≅ B]}
  : Set := {
    termL     : term;
    termR     : term;
    redL      : [ Γ |- t :⤳*: termL : R.(neRedTy.tyL) ];
    redR      : [ Γ |- u :⤳*: termR : R.(neRedTy.tyL) ];
    eq : [ Γ |- termL ~ termR : R.(neRedTy.tyL)] ;
  }.

  Arguments neRedTmEq {_ _ _ _ _ _ _ _ _} _ _ {_ _} _.

  Definition whredL `{GenericTypingProperties} {Γ : context} {t u A B : term} {R : [ Γ ||-ne A ≅ B]} :
    neRedTmEq t u R -> [Γ |- t ↘  R.(neRedTy.tyL)].
  Proof.  intros []; econstructor; tea; constructor; now eapply convneu_whne. Defined.

  Definition whredR `{GenericTypingProperties} {Γ : context} {t u A B : term} {R : [ Γ ||-ne A ≅ B]} :
    neRedTmEq t u R -> [Γ |- u ↘  R.(neRedTy.tyL)].
  Proof. intros []; econstructor; tea; constructor; eapply convneu_whne; now symmetry. Defined.

End neRedTmEq.

Export neRedTmEq(neRedTmEq, Build_neRedTmEq).
Notation "[ Γ ||-ne t ≅ u : A | R ] " := (neRedTmEq (Γ:=Γ) (A:=A) t u R).


(** ** Reducibility of neutrals at an arbitrary type *)

Module NeNf.

  Record RedTmEq `{ta : tag} `{Typing ta} `{ConvNeuConv ta} {Γ k l A} : Set :=
    {
      tyL : [Γ |- k : A] ;
      tyR : [Γ |- l : A] ;
      conv : [Γ |- k ~ l : A]
    }.

  Arguments RedTmEq {_ _ _}.

  Definition whredL `{GenericTypingProperties} {Γ : context} {t u A : term} :
    RedTmEq Γ t u A -> [Γ |- t ↘  A].
  Proof.
    intros []; econstructor.
    1: now eapply redtmwf_refl.
    constructor; now eapply convneu_whne.
  Defined.

  Definition whredR `{GenericTypingProperties} {Γ : context} {t u A : term} :
    RedTmEq Γ t u A -> [Γ |- u ↘  A].
  Proof.
    intros []; econstructor.
    1: now eapply redtmwf_refl.
    constructor; eapply convneu_whne; now symmetry.
  Defined.

  Definition conv_ `{GenericTypingProperties} {Γ : context} {t u A B : term} :
    [Γ |- A ≅ B] -> RedTmEq Γ t u A -> RedTmEq Γ t u B.
  Proof.
    intros ? []; econstructor.
    1,2: now eapply ty_conv.
    now eapply convneu_conv.
  Qed.

End NeNf.

Notation "[ Γ ||-NeNf k ≅ l : A ]" := (NeNf.RedTmEq Γ k l A) (at level 0, Γ, k, l, A at level 50).

