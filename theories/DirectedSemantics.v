
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import DirectedDirections DirectedErasure DirectedDeclarativeTyping DirectedContext.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping DeclarativeInstance DeclarativeSubst Weakening GenericTyping.


Reserved Notation "[ Δ |- w : t -( d )- u : A ]" (at level 0, Δ, d, t, u, A, w at level 50).
Reserved Notation "[ Δ |- ϕ : σ -( )- τ : Θ ]" (at level 0, Δ, Θ, σ, τ, ϕ at level 50).

Import DeclarativeTypingData.
Import DeclarativeTypingProperties.
Import Notations.

Definition witType (d: direction) :=
  match d with
  | Fun | Cofun => term
  | Discr => unit
  end.


Inductive TermRel (Δ: Context.context) (t u: term) : forall (d: direction), term -> witType d -> Type :=
| termRelFun { f } :
  [ Δ |- f : arr t u ] ->
  [ Δ |- f : t -( Fun )- u : U ]
| termRelCofun { f } :
  [ Δ |- f : arr u t ] ->
  [ Δ |- f : t -( Cofun )- u : U ]
| termRelDiscr { A } :
  [ Δ |- t ≅ u : A ] ->
  [ Δ |- tt : t -( Discr )- u : A ]
| termRelPiFun { A B w }:
  [ Δ |- A ] ->
  [ Δ ,, A |- w : tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Fun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
  [ Δ |- tLambda A w : t -( Fun )- u : tProd A B ]
| termRelPiCofun { A B w }:
  [ Δ |- A ] ->
  [ Δ ,, A |- w : tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Cofun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
  [ Δ |- tLambda A w : t -( Cofun )- u : tProd A B ]

where "[ Δ |- w : t -( d )- u : A ]" := (TermRel Δ t u d A w).

(* Definition TermRel_actionType {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : *)
(*   match d with Fun | Cofun => term | Discr => unit end. *)
(* Proof. *)
(*   induction rel. *)
(*   - exact (arr t u). *)
(*   - exact (arr u t). *)
(*   - exact tt. *)
(*   - exact (tProd A IHrel). *)
(*   - exact (tProd A IHrel). *)
(* Defined. *)

(* Definition TermRel_action_concl {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : Type. *)
(* Proof. *)
(*   destruct d. *)
(*   - exact (∑(w: term), [ Δ |- w : TermRel_actionType rel ]). *)
(*   - exact (∑(w: term), [ Δ |- w : TermRel_actionType rel ]). *)
(*   - exact [ Δ |- t ≅ u : A ]. *)
(* Defined. *)

(* Definition TermRel_action {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : TermRel_action_concl rel. *)
(* Proof. *)
(*   depind rel; simpl. *)
(*   - exists f. assumption. *)
(*   - exists f. assumption. *)
(*   - assumption. *)
(*   - destruct IHrel as [v H]. *)
(*     exists (tLambda A v). now constructor. *)
(*   - destruct IHrel as [v H]. *)
(*     exists (tLambda A v). now constructor. *)
(* Defined. *)

(* Lemma TermRel_Fun_is_kind {Δ t u A} : *)
(*   [ Δ |- t -( Fun )- u : A ] -> DirectedDeclarativeTyping.is_kind A. *)
(* Proof. *)
(*   intro h. *)
(*   depind h. *)
(*   all: try inversion H. *)
(*   all: by cbn. *)
(* Qed. *)

(* Lemma TermRel_Cofun_is_kind {Δ t u A} : *)
(*   [ Δ |- t -( Cofun )- u : A ] -> DirectedDeclarativeTyping.is_kind A. *)
(* Proof. *)
(*   intro h. *)
(*   depind h. *)
(*   all: try inversion H. *)
(*   all: by cbn. *)
(* Qed. *)

(* Lemma TermRel_WellTyped {Δ t u d A} : *)
(*   [ Δ |- t -( d )- u : A ] -> [ Δ |- t : A ] × [ Δ |- u : A ]. *)
(* Proof. *)
(*   induction 1. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)

Definition witList := list (∑ (d: direction), witType d).

Inductive SubstRel (Δ: context) :
  (nat -> term) -> (nat -> term) -> DirectedContext.context -> witList -> Type :=
| substRelSEmpty : forall σ τ, [ Δ |- nil : σ -( )- τ : nil ]
| substRelSConsDiscr : forall σ τ Θ d A ϕ w,
    [ Δ |- ϕ : (↑ >> σ) -( )- (↑ >> τ) : Θ ] ->
    [ Δ |- A[↑ >> σ] ≅ A[↑ >> τ] ] ->
    [ Δ |- w : (σ var_zero) -( d )- (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- cons (d; w) ϕ : σ -( )- τ : cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Discr;
                      DirectedContext.dir := d |} Θ ]
| substRelSConsFun : forall σ τ Θ d A f ϕ w,
    [ Δ |- ϕ : (↑ >> σ) -( )- (↑ >> τ) : Θ ] ->
    [ Δ |- f : arr A[↑ >> σ] A[↑ >> τ] ] ->
    [ Δ |- w : tApp f (σ var_zero) -( d )- (τ var_zero) : A[↑ >> τ] ] ->
    [ Δ |- cons (d; w) ϕ : σ -( )- τ : cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Fun ;
                      DirectedContext.dir := d |} Θ ]
| substRelSConsCofun : forall σ τ Θ d A f ϕ w,
    [ Δ |- ϕ : (↑ >> σ) -( )- (↑ >> τ) : Θ ] ->
    [ Δ |- f : arr A[↑ >> τ] A[↑ >> σ] ] ->
    [ Δ |- w : (σ var_zero) -( d )- tApp f (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- cons (d; w) ϕ : σ -( )- τ : cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Cofun ;
                      DirectedContext.dir := d |} Θ ]
where "[ Δ |- ϕ : σ -( )- τ : Θ ]" := (SubstRel Δ σ τ Θ ϕ).

(* Lemma TermRel_WellSubst_l {Δ σ τ Θ} : *)
(*   [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s σ : erase_dir Θ ]. *)
(* Proof. *)
(*   induction 1. *)
(*   - constructor. *)
(*   - constructor; tea. *)
(*     unshelve eapply (fst (TermRel_WellTyped _)). *)
(*     3: eassumption. *)
(*   - constructor; tea. *)
(*     admit. *)
(*   - admit. *)
(* Admitted. *)


(* Lemma TermRel_WellSubst_r {Δ σ τ Θ} : *)
(*   [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s τ : erase_dir Θ ]. *)
(* Proof. *)
(* Admitted. *)


