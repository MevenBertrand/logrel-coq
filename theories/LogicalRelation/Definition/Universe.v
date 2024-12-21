(** * LogRel.LogicalRelation.Definition.Universe : Definition of the logical relation for universes *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Universe levels *)

Inductive TypeLevel : Set :=
  | zero : TypeLevel
  | one  : TypeLevel.

Inductive TypeLevelLt : TypeLevel -> TypeLevel -> Set :=
    | Oi : TypeLevelLt zero one.

Notation "A << B" := (TypeLevelLt A B).

Definition LtSubst {l} (h : l = one) : zero << l.
Proof.
  rewrite h.
  constructor.
Qed.

Definition elim {l : TypeLevel} (h : l << zero) : False :=
  match h in _ << lz return (match lz with | zero => False | one => True end) with
    | Oi => I
  end.


(** ** Reducibility of the universe *)

Module URedTy.

  Record URedTy `{ta : tag} `{!WfType ta} `{!RedType ta} `{H : WfContext ta} {l} {Γ : context} {A B : term}
  : Set := {
    level  : TypeLevel;
    lt  : level << l;
    redL : [ Γ |- A  :⤳*: U ] ;
    redR : [ Γ |- B  :⤳*: U ] ;
  }.

  Arguments URedTy {_ _ _ _}.

  Definition wfCtx  `{WfContextProperties}  {l} {Γ : context} {A B : term} : URedTy l Γ A B -> [|- Γ].
  Proof. intros []; timeout 1 gen_typing. Qed.

  Definition whredL `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta} {l} {Γ : context} {A B : term} :
    URedTy l Γ A B -> [Γ |- A ↘ ].
  Proof. intros []; timeout 1 gen_typing. Defined.

  Definition whredR `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta} {l} {Γ : context} {A B : term} :
    URedTy l Γ A B -> [Γ |- B ↘ ].
  Proof. intros []; timeout 1 gen_typing. Defined.

End URedTy.

Export URedTy(URedTy,Build_URedTy).


Notation "[ Γ ||-U< l > A ≅ B ]" := (URedTy l Γ A B) (at level 0, Γ, l, A, B at level 50).

Module URedTm.

  Record URedTm@{i j} `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {Γ : context} {t A B : term} {R : [Γ ||-U<l> A ≅ B]}
  : Type@{j} := {
    te : term;
    red : [ Γ |- t :⤳*: te : U ];
    type : isType te;
  }.

  Arguments URedTm {_ _ _ _ _ _ _ _} rec.

  Definition whred `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t A B : term} {R : [Γ ||-U<l> A ≅ B]} :
    URedTm rec Γ t A B R -> [Γ |- t ↘  U].
  Proof. intros []; gtyping. Defined.

  Record URedTmEq@{i j} `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {Γ : context} {t u A B : term} {R : [Γ ||-U<l> A ≅ B]}
  : Type@{j} := {
      redL : URedTm (@rec) Γ t A B R ;
      redR : URedTm (@rec) Γ u A B R ;
      eq   : [ Γ |- redL.(te) ≅ redR.(te) : U ];
      (* relEq : [ rec R.(URedTy.lt) | Γ ||- t ≅ u ] ; *)
  }.

  Arguments URedTmEq {_ _ _ _ _ _ _ _} rec.

  Definition whredL `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-U<l> A ≅ B]} :
    URedTmEq rec Γ t u A B R -> [Γ |- t ↘  U].
  Proof. intros []; now eapply whred. Defined.

  Definition whredR `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-U<l> A ≅ B]} :
    URedTmEq rec Γ t u A B R -> [Γ |- u ↘  U].
  Proof. intros []; now eapply whred. Defined.

End URedTm.

Export URedTm(URedTm,Build_URedTm,URedTmEq,Build_URedTmEq).
Notation "[ R | Γ ||-U t ≅ u : A | l ]" := (URedTmEq R Γ t u A _ l) (at level 0, R, Γ, t, u, A, l at level 50).
Notation "[ R | Γ ||-U t ≅ u : A ≅ B | l ]" := (URedTmEq R Γ t u A B l) (at level 0, R, Γ, t, u, A, B, l at level 50).
