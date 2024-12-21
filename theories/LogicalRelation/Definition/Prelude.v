(** * LogRel.LogicalRelation.Definition.Prelude: Structures employed to define the logical relation *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Create HintDb logrel.
#[global] Hint Constants Opaque : logrel.
#[global] Hint Variables Transparent : logrel.
Ltac logrel := eauto with logrel.

(** Note: modules are used as a hackish solution to provide a form of namespaces for record projections. *)

(** ** Preliminaries *)

(** Instead of using induction-recursion, we encode simultaneously the fact that a type is reducible,
  and the graph of its decoding, as a single inductive relation.
  Concretely, the type of our reducibility relation is the following RedRel:
  for some R : RedRel, R Γ A eqTy redTm eqTm says
  that according to R, A is reducible in Γ and the associated reducible type equality
  (resp. term reducibility, term reducible equality) are eqTy (resp. redTm eqTm).
  One should think of RedRel as a functional relation taking two arguments (Γ and A) and returning
  three outputs (eqTy, redTm and eqTm). *)

  Definition RedRel@{i j} :=
  context               ->
  term                  ->
  term                  ->
  (term -> term -> Type@{i}) ->
  Type@{j}.

(** An LRPack contains the data corresponding to the codomain of RedRel seen as a functional relation. *)

Module LRPack.

  Record LRPack@{i} {Γ : context} {A B : term} :=
  {
    eqTm :  term -> term -> Type@{i};
  }.

  Arguments LRPack : clear implicits.

End LRPack.

Export LRPack(LRPack,Build_LRPack).

(* Notation "[ P | Γ ||- A ≅ B ]" := (@LRPack.eqTy Γ A P B). *)
Notation "[ P | Γ ||- t : A ]" := (@LRPack.eqTm Γ A A P t t).
Notation "[ P | Γ ||- t ≅ u : A ]" := (@LRPack.eqTm Γ A _ P t u).
Notation "[ P | Γ ||- t ≅ u : A ≅ B ]" := (@LRPack.eqTm Γ A B P t u).

(** An LRPack is adequate wrt. a RedRel when its three unpacked components are. *)
Definition LRPackAdequate@{i j} {Γ : context} {A B : term}
  (R : RedRel@{i j}) (P : LRPack@{i} Γ A B) : Type@{j} :=
  R Γ A B P.(LRPack.eqTm).

Arguments LRPackAdequate _ _ _ /.

Module LRAd.

  Record > LRAdequate@{i j} {Γ : context} {A B : term} {R : RedRel@{i j}} : Type :=
  {
    pack :> LRPack@{i} Γ A B ;
    adequate :> LRPackAdequate@{i j} R pack
  }.

  Arguments LRAdequate : clear implicits.
  Arguments Build_LRAdequate {_ _ _ _ _}.

End LRAd.

Export LRAd(LRAdequate,Build_LRAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion LRAd.pack : LRAdequate >-> LRPack.
Coercion LRAd.adequate : LRAdequate >-> LRPackAdequate.

(* TODO : update these for LRAdequate *)

Notation "[ R | Γ ||- A ≅ B ]"              := (@LRAdequate Γ A B R).
(* Notation "[ R | Γ ||- A ≅ B | RA ]"     := (RA.(@LRAd.pack Γ A R).(LRPack.eqTy) B). *)
Notation "[ R | Γ ||- t ≅ u : A | RA ]" := (RA.(@LRAd.pack Γ A _ R).(LRPack.eqTm) t u).
Notation "[ R | Γ ||- t ≅ u : A ≅ B | RA ]" := (RA.(@LRAd.pack Γ A B R).(LRPack.eqTm) t u).
