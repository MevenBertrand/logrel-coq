(** * LogRel.Context: definition of contexts and operations on them.*)
From Coq Require Import ssreflect Morphisms Setoid.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst.

Set Primitive Projections.

(** ** Context declaration *)
(** Context: list of declarations *)
(** Terms use de Bruijn indices to refer to context entries.*)

Definition context := list term.

Notation "'ε'" := (@nil term).
Notation " Γ ,, d " := (@cons _ d Γ) (at level 20, d at next level).
Notation " Γ ,,, Δ " := (@app _ Δ Γ) (at level 25, Δ at next level, left associativity).

(** States that a definition, correctly weakened, is in a context. *)
Inductive in_ctx {A} `{Ren1 (nat -> nat) A A} : list A -> nat -> A -> Type :=
  | in_here Γ d : in_ctx (Γ,,d) 0 (d⟨↑⟩)
  | in_there Γ d d' n : in_ctx Γ n d -> in_ctx (Γ,,d') (S n) (d⟨↑⟩).

Lemma in_ctx_inj Γ n decl decl' :
  in_ctx Γ n decl -> in_ctx Γ n decl' -> decl = decl'.
Proof.
  induction 1 in decl' |- * ; inversion 1 ; subst.
  1: reflexivity.
  now f_equal.
Qed.