From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils.

(* Export UnscopedNotations.
#[global] Open Scope subst_scope. *)

Declare Scope asubst_scope.
Delimit Scope asubst_scope with asub.

Arguments funcomp {X Y Z}%type_scope (g f)%function_scope.

Notation "f >> g" := (funcomp g f) (at level 50) : function_scope.

Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : asubst_scope.

Notation "s ⟨ xi1 ⟩" := (ren1 xi1 s) (at level 7, left associativity, format "s ⟨ xi1 ⟩") : asubst_scope.
(* Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : function_scope. *)

Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : asubst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : asubst_scope.

Notation "↑" := (shift) : asubst_scope.

#[global] Open Scope asubst_scope.

#[global] Instance Ren1_subst {Y Z : Type} `{Ren1 (nat -> nat) Y Z} :
  (Ren1 (nat -> nat) (nat -> Y) (nat -> Z)) :=
  fun ρ σ i => (σ i)⟨ρ⟩.

Ltac fold_autosubst :=
    change ren_term with (@ren1 _ _ _ Ren_term) in * ;
    change subst_term with (@subst_term _ _ _ Subst_term) in *;
    change (fun i => (?σ i)⟨?ρ⟩) with (@ren1 _ _ _ Ren1_subst ρ σ) in *.

Smpl Add fold_autosubst : refold.

Arguments ren1 {_ _ _}%type_scope {Ren1} _ !_/.
(* Ideally, we'd like Ren_term to not be there, and ren_term to be directly the Ren1 instance…*)
Arguments Ren_term _ _ /.
Arguments Ren1_subst {_ _ _} _ _/.