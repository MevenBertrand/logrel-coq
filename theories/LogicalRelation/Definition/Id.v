(** * LogRel.LogicalRelation.Definition.Id : Definition of the logical relation for indentity types *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Logical relation for Identity types *)

Module IdRedTyPack.

  Record IdRedTyPack@{i} `{ta : tag} `{WfContext ta} `{WfType ta} `{RedType ta} `{ConvType ta}
    {Γ : context} {A B : term}
  : Type :=
  {
    tyL : term ;
    tyR : term ;
    lhsL : term ;
    lhsR : term ;
    rhsL : term ;
    rhsR : term ;
    redL : [Γ |- A :⤳*: tId tyL lhsL rhsL] ;
    redR : [Γ |- B :⤳*: tId tyR lhsR rhsR] ;
    eq : [Γ |- tId tyL lhsL rhsL ≅ tId tyR lhsR rhsR] ;
    tyRed : LRPack@{i} Γ tyL tyR ;
    lhsRed : [ tyRed | Γ ||- lhsL ≅ lhsR : _ ] ;
    rhsRed : [ tyRed | Γ ||- rhsL ≅ rhsR : _ ] ;
    (* Bake in PER property for reducible conversion at ty  to cut dependency cycles *)
    tyPER : PER tyRed.(LRPack.eqTm) ;
  }.

  Record IdRedTyAdequate@{i j} `{ta : tag} `{WfContext ta} `{WfType ta} `{RedType ta} `{ConvType ta}
    {Γ : context} {A B : term} {R : RedRel@{i j}} {IA : IdRedTyPack@{i} (Γ:=Γ) (A:=A) (B:=B)} :=
    {
      tyAd : LRPackAdequate@{i j} R IA.(tyRed) ;
    }.

  Arguments IdRedTyPack {_ _ _ _ _}.
  Arguments IdRedTyAdequate {_ _ _ _ _ _ _ _}.

  Definition outTy `{ta : tag} `{WfContext ta} `{WfType ta} `{RedType ta} `{ConvType ta} {Γ A B} : IdRedTyPack Γ A B -> term :=
    fun IA => tId IA.(tyL) IA.(lhsL) IA.(rhsL).

  Arguments outTy {_ _ _ _ _ _ _ _} _ /.

End IdRedTyPack.

Export IdRedTyPack(IdRedTyPack, Build_IdRedTyPack, IdRedTyAdequate, Build_IdRedTyAdequate).


Module IdRedTmEq.
Section IdRedTmEq.
  Universe i.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {Γ : context} {A B: term} {IA : IdRedTyPack@{i} Γ A B}.

  Inductive IdPropEq : term -> term -> Type :=
  | reflReq {A A' x x'} :
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ |- x : A] ->
    [Γ |- x' : A'] ->
    [Γ |- IA.(IdRedTyPack.tyL) ≅ A] ->
    [Γ |- IA.(IdRedTyPack.tyL) ≅ A'] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.lhsL) ≅ x : _ ] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.lhsL) ≅ x' : _ ] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.rhsL) ≅ x : _ ] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.rhsL) ≅ x' : _ ] ->
    IdPropEq (tRefl A x) (tRefl A' x')
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : IdRedTyPack.outTy IA] -> IdPropEq ne ne'.


  Record IdRedTmEq  {t u : term} : Type :=
    Build_IdRedTmEq {
      nfL : term ;
      nfR : term ;
      redL : [Γ |- t :⤳*: nfL : IdRedTyPack.outTy IA ] ;
      redR : [Γ |- u :⤳*: nfR : IdRedTyPack.outTy IA ] ;
      eq : [Γ |- nfL ≅ nfR : IdRedTyPack.outTy IA] ;
      prop : IdPropEq nfL nfR ;
  }.

  Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Definition whnfL {t u} : IdPropEq t u -> whnf t.
    Proof. intros [] ; [constructor|]; unshelve eapply NeNf.whredL ; cycle 3; tea. Qed.

    Definition whnfR {t u} : IdPropEq t u -> whnf u.
    Proof. intros [] ; [constructor|]; unshelve eapply NeNf.whredR ; cycle 3; tea. Qed.

    Definition whredL {t u} : @IdRedTmEq t u -> [Γ |- t ↘ IdRedTyPack.outTy IA].
    Proof. intros []; econstructor; tea; now eapply whnfL. Defined.

    Definition whredR {t u} : @IdRedTmEq t u -> [Γ |- u ↘ IdRedTyPack.outTy IA].
    Proof. intros []; econstructor; tea; now eapply whnfR. Defined.
  End Def.

End IdRedTmEq.
Arguments IdRedTmEq {_ _ _ _ _ _ _ _ _ _ _ _}.
Arguments IdPropEq {_ _ _ _ _ _ _ _ _ _}.
End IdRedTmEq.

Export IdRedTmEq(IdRedTmEq,Build_IdRedTmEq, IdPropEq).
