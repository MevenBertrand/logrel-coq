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

Definition ltInd (P : TypeLevel -> Type) (ih : (forall l, (forall l', l' << l -> P l') -> P l))
  : forall l, P l.
Proof.
  assert (P zero) by (apply ih; intros ? []%elim).
  intros []; tea; apply ih; intros ? h; now inversion h.
Qed.

(** ** Reducibility of the universe *)

Module URedTy.

  Record URedTy `{ta : tag} `{!WfType ta} `{!RedType ta} {l} {Γ : context} {A B : term}
  : Set := {
    level  : TypeLevel;
    lt  : level << l;
    redL : [ Γ |- A  :⤳*: U ] ;
    redR : [ Γ |- B  :⤳*: U ] ;
  }.

  Arguments URedTy {_ _ _}.

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

#[program]
Instance URedTyWhRedTy `{GenericTypingProperties} {Γ l} : WhRedTyRel Γ (URedTy l Γ) :=
 {| whredtyL := fun A B RAB => URedTy.whredL RAB ;
    whredtyR := fun A B RAB => URedTy.whredR RAB ;
 |}.
Next Obligation. destruct h; gtyping. Qed.

Notation "[ Γ ||-U< l > A ≅ B ]" := (URedTy l Γ A B) (at level 0, Γ, l, A, B at level 50).

Import EqNotations.

Lemma level_unique `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta}
  {Γ lA lB l A A' B B'}
  (RA : [Γ ||-U<lA> A ≅ A'])
  (RB : [Γ ||-U<lB> B ≅ B'])
  (RAB : [Γ ||-U<l> A ≅ B]) : RA.(URedTy.level) = RB.(URedTy.level).
Proof.
  (* If we introduce more universes this lemma should still hold because
    RAB entails that A ⤳* U RAB.(level), B ⤳* U RAB.(level)
    also A ⤳* RA.(level) and B ⤳* RB.(level) and by determinism of reduction
    RA.(level) = RAB.(level) = RB.(level)
  *)
  destruct RA as [? []], RB as [? []]; reflexivity.
Qed.

Lemma level_unique' `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta}
  {Γ lA lB l A A' B B'}
  (RA : [Γ ||-U<lA> A' ≅ A])
  (RB : [Γ ||-U<lB> B' ≅ B])
  (RAB : [Γ ||-U<l> A ≅ B]) : RA.(URedTy.level) = RB.(URedTy.level).
Proof.
  (* If we introduce more universes this lemma should still hold because
    RAB entails that A ⤳* U RAB.(level), B ⤳* U RAB.(level)
    also A ⤳* RA.(level) and B ⤳* RB.(level) and by determinism of reduction
    RA.(level) = RAB.(level) = RB.(level)
  *)
  destruct RA as [? []], RB as [? []]; reflexivity.
Qed.

Module URedTm.

  Record URedTm `{ta : tag} `{Typing ta} `{RedTerm ta}
    {level : TypeLevel} {Γ : context} {t : term}
  : Set := {
    te : term;
    red : [ Γ |- t :⤳*: te : U (* level *) ];
    type : isType te;
  }.

  Arguments URedTm {_ _ _}.

  Definition whred `{ta : tag} `{Typing ta} `{RedTerm ta}
    {l} {Γ : context} {t: term} :
    URedTm l Γ t -> [Γ |- t ↘  U].
  Proof. intros []; gtyping. Defined.

  Record URedTmEq@{i j} `{ta : tag} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {Γ : context} {A B : term} {R : [Γ ||-U<l> A ≅ B]} {t u}
  : Type@{j} := {
      redL : URedTm R.(URedTy.level) Γ t ;
      redR : URedTm R.(URedTy.level) Γ u ;
      eq   : [ Γ |- redL.(te) ≅ redR.(te) : U ];
      relEq : [ rec R.(URedTy.lt) | Γ ||- t ≅ u ] ;
  }.

  Arguments URedTmEq {_ _ _ _ _ _ _ } rec.

  Definition whredL `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-U<l> A ≅ B]} :
    URedTmEq rec Γ A B R t u -> [Γ |- t ↘  U].
  Proof. intros []; now eapply whred. Defined.

  Definition whredR `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-U<l> A ≅ B]} :
    URedTmEq rec Γ A B R t u -> [Γ |- u ↘  U].
  Proof. intros []; now eapply whred. Defined.

End URedTm.

Export URedTm(URedTm,Build_URedTm,URedTmEq,Build_URedTmEq).
Notation "[ R | Γ ||-U t ≅ u : A | l ]" := (URedTmEq R Γ A _ l t u) (at level 0, R, Γ, t, u, A, l at level 50).
Notation "[ R | Γ ||-U t ≅ u : A ≅ B | l ]" := (URedTmEq R Γ A B l t u) (at level 0, R, Γ, t, u, A, B, l at level 50).

Instance URedTmWhRed `{GenericTypingProperties} {Γ l} : WhRedTm Γ U (URedTm l Γ) :=
  fun t => URedTm.whred.

