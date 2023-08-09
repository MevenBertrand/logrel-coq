(** * LogRel.AutoSubst.Extra: extra content to better handle the boilerplate generated by AutoSubst. *)

(** This is the only file in the AutoSubst submodule that is not automatically generated. *)
From smpl Require Import Smpl.
From Coq Require Import ssrbool List.
From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst.

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

Notation "s [ t ]⇑" := (subst_term (scons t (shift >> tRel)) s) (at level 7, left associativity, format "s '/' [ t ]⇑") : asubst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : asubst_scope.

Notation "↑" := (shift) : asubst_scope.

#[global] Open Scope asubst_scope.

Notation U := (tSort set).
Notation "'eta_expand' f" := (tApp f⟨↑⟩ (tRel 0)) (at level 40, only parsing).

#[global] Instance Ren1_subst {Y Z : Type} `{Ren1 (nat -> nat) Y Z} :
  (Ren1 (nat -> nat) (nat -> Y) (nat -> Z)) :=
  fun ρ σ i => (σ i)⟨ρ⟩.
    
Ltac fold_autosubst :=
    fold ren_term ;
    fold subst_term.

Smpl Add fold_autosubst : refold.

Ltac change_autosubst :=
    change ren_term with (@ren1 _ _ _ Ren_term) in * ;
    change subst_term with (@subst1 _ _ _ Subst_term) in *;
    change (fun i => (?σ i)⟨?ρ⟩) with (@ren1 _ _ _ Ren1_subst ρ σ) in *.

Smpl Add 50 change_autosubst : refold.

Arguments ren1 {_ _ _}%type_scope {Ren1} _ !_/.
(* Ideally, we'd like Ren_term to not be there, and ren_term to be directly the Ren1 instance… *)
Arguments Ren_term _ _ /.
Arguments Ren1_subst {_ _ _} _ _/.

Notation arr A B := (tProd A B⟨↑⟩).
Notation comp A f g := (tLambda A (tApp f⟨↑⟩ (tApp g⟨↑⟩ (tRel 0)))).
Notation idterm A  := (tLambda A (tRel 0)).

Lemma arr_ren1 {A B} : forall ρ, (arr A B)⟨ρ⟩ = arr A⟨ρ⟩ B⟨ρ⟩.
Proof.
  now asimpl.
Qed.

Lemma subst_arr A B σ : (arr A B)[σ] = arr A[σ] B[σ].
Proof. now asimpl. Qed.

Lemma subst_prod X Y σ : (tProd X Y)[σ] = tProd X[σ] Y[up_term_term σ].
Proof. now asimpl. Qed.

Lemma shift_up_eq {t σ} : t⟨↑⟩[up_term_term σ] = t[σ]⟨↑⟩.
Proof. now asimpl. Qed.

Lemma up_single_subst {t σ u} : t[up_term_term σ][u..] = t[u .:  σ].
Proof.  now asimpl. Qed.

Lemma up_liftSubst_eq {σ t u} : t[up_term_term σ][u]⇑ = t[u .: ↑ >> up_term_term σ].
Proof.
  asimpl. eapply ext_term; intros [|n]; cbn.
  1: reflexivity.
  unfold funcomp; now rewrite  rinstInst'_term.
Qed.

Lemma liftSubst_scons_eq {t u v: term} σ : t[u]⇑[v .: σ] = t[u[v .: σ] .: σ].
Proof. now asimpl. Qed.

Definition elimSuccHypTy P :=
  tProd tNat (arr P P[tSucc (tRel 0)]⇑).

