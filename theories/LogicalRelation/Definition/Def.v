(** * LogRel.LogicalRelation.Definition.Def : Definition of the logical relation *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne Universe Poly Pi Sig Nat Empty Id.


Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Definition of the logical relation *)

(** This simply bundles the different cases for reducibility already defined. *)

Unset Elimination Schemes.

Inductive LR@{i j k} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta}
  {l : TypeLevel} (rec : forall l', l' << l -> RedRel@{i j})
: RedRel@{j k} :=
  | LRU {Γ A B} (H : [Γ ||-U<l> A ≅ B]) :
      LR rec Γ A B (fun t u => [ rec | Γ ||-U t ≅ u : A | H ])
  | LRne {Γ A B} (neA : [ Γ ||-ne A ≅ B]) :
      LR rec Γ A B (fun t u =>  [ Γ ||-ne t ≅ u : A | neA])
  | LRPi {Γ : context} {A B : term} (ΠA : PiRedTyPack@{j} Γ A B) (ΠAad : PiRedTyAdequate@{j k} (LR rec) ΠA) :
    LR rec Γ A B (PiRedTmEq ΠA)
  | LRNat {Γ A B} (NA : [Γ ||-Nat A ≅ B]) :
    LR rec Γ A B (NatRedTmEq Γ)
  | LREmpty {Γ A B} (NA : [Γ ||-Empty A ≅ B]) :
    LR rec Γ A B (EmptyRedTmEq Γ)
  | LRSig {Γ : context} {A B : term} (ΣA : SigRedTyPack@{j} Γ A B) (ΣAad : SigRedTyAdequate@{j k} (LR rec) ΣA) :
    LR rec Γ A B (SigRedTmEq ΣA)
  | LRId {Γ A B} (IA : IdRedTyPack@{j} Γ A B) (IAad : IdRedTyAdequate@{j k} (LR rec) IA) :
    LR rec Γ A B (IdRedTmEq IA)
  .

Set Elimination Schemes.

(** ** Bundling of the logical relation *)

(** Boilerplate to make the relation look a bit better. *)

Section MoreDefs.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Definition rec0@{i j} (l' : TypeLevel) (h : l' << zero) : RedRel@{i j} :=
    match elim h with
    end.

  Definition LogRel0@{i j k} :=
    LR@{i j k} rec0@{i j}.

  Definition LRbuild0@{i j k} {Γ A B tmeq} :
    LogRel0@{i j k} Γ A B tmeq -> [ LogRel0@{i j k} | Γ ||- A ≅ B ] :=
    fun H => {|
      LRAd.pack := {| LRPack.eqTm := tmeq |} ;
      LRAd.adequate := H |}.

  Definition LogRelRec@{i j k} (l : TypeLevel) : forall l', l' << l -> RedRel@{j k} :=
    match l with
      | zero => rec0@{j k}
      | one => fun _ _ => LogRel0@{i j k}
    end.

  Arguments LogRelRec l l' l_ /.

  Definition rec1 :=
    LogRelRec one.

  Definition LogRel1@{i j k l} :=
    LR@{j k l} rec1@{i j k}.

  Definition LogRel@{i j k l} (l : TypeLevel) :=
    LR@{j k l} (LogRelRec@{i j k} l).

  Definition LRbuild@{i j k l} {Γ l A B tmeq} :
    LR@{j k l} (LogRelRec@{i j k} l) Γ A B tmeq -> [ LogRel l | Γ ||- A ≅ B] :=
    fun H => {|
      LRAd.pack := {| LRPack.eqTm := tmeq |} ;
      LRAd.adequate := H |}.

  Definition LRU_@{i j k l} {l Γ A B} (H : [Γ ||-U<l> A ≅ B])
    : [ LogRel@{i j k l} l | Γ ||- A ≅ B ] :=
    LRbuild (LRU (LogRelRec l) H).

  Definition LRne_@{i j k l} l {Γ A B} (neA : [Γ ||-ne A ≅ B])
    : [ LogRel@{i j k l} l | Γ ||- A ≅ B ] :=
    LRbuild (LRne (LogRelRec l) neA).

  Definition LRPi_@{i j k l} l {Γ A B} (ΠA : PiRedTyPack@{k} Γ A B)
    (ΠAad : PiRedTyAdequate (LR (LogRelRec@{i j k} l)) ΠA)
    : [ LogRel@{i j k l} l | Γ ||- A  ≅ B] :=
    LRbuild (LRPi (LogRelRec l) ΠA ΠAad).

  Definition LRNat_@{i j k l} l {Γ A B} (NA : [Γ ||-Nat A ≅ B])
    : [LogRel@{i j k l} l | Γ ||- A ≅ B] :=
    LRbuild (LRNat (LogRelRec l) NA).

  Definition LREmpty_@{i j k l} l {Γ A B} (NA : [Γ ||-Empty A ≅ B])
    : [LogRel@{i j k l} l | Γ ||- A ≅ B] :=
    LRbuild (LREmpty (LogRelRec l) NA).

  Definition LRId_@{i j k l} l {Γ A B} (IA : IdRedTyPack@{k} Γ A B)
    (IAad : IdRedTyAdequate (LR (LogRelRec@{i j k} l)) IA)
    : [LogRel@{i j k l} l | Γ ||- A ≅ B] :=
    LRbuild (LRId (LogRelRec l) IA IAad).

End MoreDefs.

(** To be explicit with universe levels use the rhs, e.g
   [ LogRel@{i j k l} l | Γ ||- A] or [ LogRel0@{i j k} ||- Γ ||- A ≅ B | RA ]
 *)
Notation "[ Γ ||-< l > A ≅ B ]" := [ LogRel l | Γ ||- A ≅ B].
Notation "[ Γ ||-< l > A ]" := [ LogRel l | Γ ||- A ≅ A].
Notation "[ Γ ||-< l > t : A | RA ]" := [ LogRel l | Γ ||- t ≅ t : A | RA ].
Notation "[ Γ ||-< l > t ≅ u : A | RA ]" := [ LogRel l | Γ ||- t ≅ u : A | RA ].

(** ** Folding and unfolding lemmas of the logical relation wrt levels *)

Section LogRelRecFoldLemmas.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Lemma redTyRecFwd@{i j k l} {l Γ U0 U1 A B} (h : [Γ ||-U<l> U0 ≅ U1]) :
    [LogRelRec@{j k l} l (URedTy.level h) (URedTy.lt h) | Γ ||- A ≅ B] ->
    [LogRel@{i j k l} (URedTy.level h) | Γ ||- A ≅ B].
  Proof.
    destruct h as [? lt]; cbn.
    pattern level, l , lt.
    (* Employ using to specify the universe level l instead of generating a fresh one *)
    induction lt using TypeLevelLt_rect@{l}.
    cbn. easy.
  Defined.

  Lemma redTyRecBwd@{i j k l} {l Γ U0 U1 A B} (h : [Γ ||-U<l> U0 ≅ U1]) :
    [LogRel@{i j k l} (URedTy.level h) | Γ ||- A ≅ B] ->
    [LogRelRec@{j k l} l (URedTy.level h) (URedTy.lt h) | Γ ||- A ≅ B].
  Proof.
    destruct h as [? lt]; cbn.
    (* Employ using to specify the universe level l instead of generating a fresh one *)
    pattern level, l , lt; induction lt using TypeLevelLt_rect@{l}.
    cbn. easy.
  Defined.

  Lemma redTmRecFwd@{i j k l} {l Γ U0 U1 A B t u} (h : [Γ ||-U<l> U0 ≅ U1])
    (RAB : [LogRelRec@{j k l} l (URedTy.level h) (URedTy.lt h) | Γ ||- A ≅ B]) :
    [RAB | _ ||- t ≅ u : _] -> [redTyRecFwd@{i j k l} h RAB | _ ||- t ≅ u : _].
  Proof.
    destruct h as [? []]; now cbn.
  Defined.

  Lemma redTmRecBwd@{i j k l} {l Γ U0 U1 A B t u} (h : [Γ ||-U<l> U0 ≅ U1])
    (RAB : [LogRel@{i j k l} (URedTy.level h) | Γ ||- A ≅ B]) :
    [RAB | _ ||- t ≅ u : _] -> [redTyRecBwd h RAB | _ ||- t ≅ u : _].
  Proof.
    destruct h as [? []]; now cbn.
  Qed.

End LogRelRecFoldLemmas.
