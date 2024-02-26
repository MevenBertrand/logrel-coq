(** * LogRel.Decidability.Execution: example executions of the type checker, in Coq. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils Notations BasicAst Context GenericTyping DeclarativeTyping DeclarativeInstance BundledAlgorithmicTyping AlgorithmicTypingProperties.
From PartialFun Require Import Monad PartialFun MonadExn.
From LogRel.Decidability Require Import Functions Soundness.

From LogRel Require TermNotations.

Import DeclarativeTypingProperties.

#[local] Definition infer (Γ : context) (t : term) : Fueled (exn errors term) :=
  (fueled (typing tconv) 1000 (inf_state;Γ;tt;t)).

#[local] Definition check (Γ : context) (T t : term) : Fueled (exn errors unit) := 
  (fueled (typing tconv) 1000 (check_state;Γ;T;t)).

#[local] Definition check_ty (Γ : context) (t : term) : Fueled (exn errors unit) := 
  (fueled (typing tconv) 1000 (wf_ty_state;Γ;tt;t)).

#[local] Definition conv_tm (Γ : context) (T: term) (t1 : term) (t2 : term) : Fueled (exn errors unit) :=
  (fueled _conv 1000 (tm_state;Γ;T;t1;t2)).


Ltac infer_auto :=
  match goal with
  | |- [ε |- ?t : ?T] =>
    assert [|- ε] by econstructor ;
      eassert (graph (typing tconv) (inf_state;ε;tt;t) (success _))
        as ?%implem_typing_sound%algo_typing_sound
        by (apply (fueled_graph_sound (typing tconv) 1000 (inf_state;_)) ; reflexivity)
  end ; auto using implem_tconv_sound.

Ltac wf_ty_auto :=
  match goal with
  | |- [ε |- ?T] =>
      assert [|- ε] by econstructor ;
      eassert (graph (typing tconv) (wf_ty_state;ε;tt;T) (success _))
        as ?%implem_typing_sound%algo_typing_sound
        by (apply (fueled_graph_sound (typing tconv) 1000 (wf_ty_state;_)) ; reflexivity)
  end ; auto using implem_tconv_sound.

Ltac check_auto :=
  match goal with
  | |- [ε |- ?t : ?T] =>
    assert [|- ε] by econstructor ;
    eassert (graph (typing tconv) (check_state;ε;T;t) (success _))
      as ?%implem_typing_sound%algo_typing_sound
      by (apply (fueled_graph_sound (typing tconv) 1000 (check_state;_)) ; reflexivity) ;
    eassert (graph (typing tconv) (wf_ty_state;ε;tt;T) (success _))
      as ?%implem_typing_sound%algo_typing_sound
      by (apply (fueled_graph_sound (typing tconv) 1000 (wf_ty_state;_)) ; reflexivity)
end ; auto using implem_tconv_sound.


Import TermNotations.

(*** A series of example, each time the term in Coq first, then a proof that it type-checks
  in our system, proven via reification. *)

Check ((0;0) : ∑ x : nat, nat).

Goal ⟪ ε |- (0 : ℕ; 0 : ℕ) : ℕ × ℕ⟫.
Proof.
  infer_auto.
Qed.

Check ((fun x => nat_rec (fun _ => nat) 0 (fun _ ih => S (S ih)) x) : nat -> nat).

Goal ⟪ε |- λ ℕ, indℕ ℕ 0 (λ ℕ ℕ, x₀.+2) 2 : ℕ → ℕ⟫.
Proof.
  infer_auto.
Qed.

Check (eq_refl : (nat_rect (fun _ => Type) nat (fun _ ih => nat -> ih) 3) = (nat -> nat -> nat -> nat)).

Goal ⟪ ε |- rfl □ (ℕ → ℕ → ℕ → ℕ) :
  (ℕ → ℕ → ℕ → ℕ) =⟨ □ ⟩ indℕ □ ℕ (λ ℕ □, ℕ → x₀) 3⟫.
Proof.
  check_auto.
Qed.