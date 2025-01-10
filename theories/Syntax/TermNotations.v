
From LogRel Require Import Utils AutoSubst.Extra.
From LogRel.Syntax Require Import Notations BasicAst Context.

(** Custom notation for contexts *)
Declare Custom Entry mlttctx.
(** Custom notation for terms and types *)
Declare Custom Entry mltt.

(* Entry point for tests *)
Notation "'⟪ctx' e ⟫" := e (e custom mlttctx at level 2, only parsing).
Notation "'⟪tm' e ⟫" := e (e custom mltt at level 2, only parsing).

Notation "'ε'" := ε (in custom mlttctx at level 0).
Notation "Γ , A" := (Γ ,, A) (in custom mlttctx at level 1, A custom mltt at level 2, left associativity).

(* Parentheses *)
Notation "( x )" := x (in custom mltt, x at level 2).

(* DeBruijn indices *)
Notation "'x₀'" := (tRel 0) (in custom mltt at level 0).
Notation "'x₁'" := (tRel 1) (in custom mltt at level 0).
Notation "'x₂'" := (tRel 2) (in custom mltt at level 0).
Notation "'x₃'" := (tRel 3) (in custom mltt at level 0).
Notation "'x₄'" := (tRel 4) (in custom mltt at level 0).
Notation "'x₅'" := (tRel 5) (in custom mltt at level 0).
Notation "'x₆'" := (tRel 6) (in custom mltt at level 0).
Notation "'x₇'" := (tRel 7) (in custom mltt at level 0).
Notation "'x₈'" := (tRel 8) (in custom mltt at level 0).
Notation "'x₉'" := (tRel 9) (in custom mltt at level 0).

Notation "'□'" := U (in custom mltt at level 0).

(* Π fragment *)
(* Notation "'Π' A , B" := (tProd A B) (in custom mltt at level 2, right associativity). *)
Notation "'Π' x .. y , p" := (tProd x ( .. (tProd y p) ..))
  (in custom mltt at level 2, x, y at level 0, right associativity,
   format "'[' 'Π'  '/  ' x  ..  y ,  '/  ' p ']'").
Notation "A '→' B" := (tProd A B⟨↑⟩) (in custom mltt at level 2, right associativity).
Notation "f x" := (tApp f x) (in custom mltt at level 1, left associativity).
(* Notation "'λ' A , t" := (tLambda A t) (in custom mltt at level 2, right associativity). *)
Notation "'λ' x .. y , p" := (tLambda x ( .. (tLambda y p) ..))
  (in custom mltt at level 2,  x, y at level 0, right associativity,
   format "'[' 'λ'  '/  ' x  ..  y ,  '/  ' p ']'").

(* Nat fragment *)
Notation "'ℕ'" := tNat (in custom mltt at level 0).
Notation "0" := tZero (in custom mltt at level 0).
Notation "n '.+1'" := (tSucc n) (in custom mltt at level 1).
Notation "'indℕ' P hz hs n" := (tNatElim P hz hs n) (in custom mltt at level 1, P, hz, hs, n at level 0).

Notation "n '.+2'" := (tSucc (tSucc n)) (in custom mltt at level 1).
Notation "n '.+3'" := (tSucc (tSucc (tSucc n))) (in custom mltt at level 1).
Notation "n '.+4'" := (tSucc (tSucc (tSucc (tSucc n)))) (in custom mltt at level 1).
Notation "n '.+5'" := (tSucc (tSucc (tSucc (tSucc (tSucc n))))) (in custom mltt at level 1).
Notation "1" := ⟪tm 0.+1⟫ (in custom mltt at level 0).
Notation "2" := ⟪tm 0.+2⟫ (in custom mltt at level 0).
Notation "3" := ⟪tm 0.+3⟫ (in custom mltt at level 0).
Notation "4" := ⟪tm 0.+4⟫ (in custom mltt at level 0).
Notation "5" := ⟪tm 0.+5⟫ (in custom mltt at level 0).

(* Σ fragment *)
Notation "'∑' x .. y , p" := (tSig x ( .. (tSig y p) ..))
  (in custom mltt at level 2,  x, y at level 0, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'").
(* Notation "'∑' A , B" := (tSig A B) (in custom mltt at level 2, right associativity). *)
Notation "A '×' B" := (tSig A B⟨↑⟩) (in custom mltt at level 2).
Notation "( x : A ; y : B )" := (tPair A B x y) (in custom mltt at level 0, x, A, y, B at level 2).
Notation "x '.1'" := (tFst x) (in custom mltt at level 1).
Notation "x '.2'" := (tSnd x) (in custom mltt at level 1).

(* Id fragment *)
Notation "x =⟨ A ⟩ y" := (tId A x y) (in custom mltt at level 1).
Notation "'rfl' A x" := (tRefl A x)  (in custom mltt at level 1, A, x at level 0).
Notation "'indId' A x P y hr e" := (tIdElim A x P y hr e) (in custom mltt at level 1, A, x, P, y, hr, e at level 0).


(* Alternative notations for typing judgements using the custom notations *)

Notation "⟪ |- Γ ⟫" := (wf_context Γ)
  (at level 0, Γ custom mlttctx at level 1) : typing_scope.
Notation "⟪ Γ |- A ⟫" := (wf_type Γ A)
  (at level 0, Γ custom mlttctx at level 1, A custom mltt at level 2, only parsing) : typing_scope.
Notation "⟪ Γ |- t : A ⟫" := (typing Γ A t)
  (at level 0, Γ custom mlttctx at level 1, t custom mltt at level 2, A custom mltt at level 2, only parsing) : typing_scope.
Notation "⟪ Γ |- A ≅ B ⟫" := (conv_type Γ A B)
  (at level 0, Γ custom mlttctx at level 1, A custom mltt at level 2, B custom mltt at level 2, only parsing) : typing_scope.
Notation "⟪ Γ |- t ≅ u : A ⟫" := (conv_term Γ A t u )
  (at level 0, Γ custom mlttctx at level 1, t custom mltt at level 2, u custom mltt at level 2, A custom mltt at level 2, only parsing) : typing_scope.

(* Tests *)
(* Check ⟪ |- ε, ℕ ⟫.
Check ⟪ ε, ℕ |- ℕ⟫.
Check ⟪ ε, ℕ |- x₀ : ℕ⟫.
Check ⟪ ε, ℕ |- indℕ ℕ 0 0 x₀ : ℕ⟫.
Check ⟪ ε, ℕ |- x₀ ≅ indℕ ℕ 0 (λ ℕ, λ ℕ, S x₀) x₀ : ℕ ⟫. *)