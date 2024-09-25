From Coq Require Import Nat Morphisms.
From LogRel Require Import Utils AutoSubst.Extra.
From LogRel.Syntax Require Import Weakening.

Arguments id {_} _/.
Arguments Datatypes.id {_} _/.
Arguments funcomp {X Y Z}%_type_scope (g f)%_function_scope _/.

Record section {A B : Type} {f : A -> B} :=
  { sec_fun :> B -> A ; sec_ok : f >> sec_fun =1 id }.

Arguments section {_ _} _.

Lemma section_inj {A B} (f : A -> B) (x x' : A) :
  section f ->
  f x = f x' ->
  x = x'.
Proof.
  intros [? sec] ? ; red in sec ; cbn in *.
  rewrite <- (sec x), <- (sec x').
  now f_equal.
Qed.

Lemma section_id {A : Type} : section (@id A).
Proof.
  exists id.
  reflexivity.
Qed.

Lemma section_compose {A B C : Type} (f : A -> B) (g : B -> C) :
  section f -> section g -> section (f >> g).
Proof.
  intros [f' Hf] [g' Hg].
  exists (g' >> f').
  intros ?.
  red in Hf, Hg ; cbn in *.
  now rewrite Hg, Hf.
Qed.

Lemma section_S : section S.
Proof.
  exists pred.
  reflexivity.
Qed.

Lemma section_up f : section f -> section (up_ren f).
Proof.
  intros [f' Hf].
  exists (up_ren f').
  intros [] ; cbn.
  1: reflexivity.
  red in Hf ; cbn in *.
  now rewrite Hf.
Qed.

Theorem section_wk {Γ Δ} (ρ : Γ ≤ Δ) : section ρ.
Proof.
  destruct ρ as [ρ Hρ].
  induction Hρ ; cbn in *.
  - apply section_id.
  - apply section_compose ; tea.
    apply section_S.
  - now apply section_up.
Defined.

Notation "ρ ⁻¹" := (section_wk ρ) (at level 80).

#[global] Instance Ren1_sec {Y Z : Type} {f : nat -> nat} `(ren : Ren1 (nat -> nat) Y Z) :
  (Ren1 (section f) Y Z) := fun s t => t⟨s.(sec_fun)⟩.

Arguments Ren1_sec {_ _ _} _ _/.

Lemma wk_section {Γ Δ} (ρ : Γ ≤ Δ) (t : term) :
  t⟨ρ⟩⟨ρ⁻¹⟩ = t.
Proof.
  asimpl.
  etransitivity.
  2: apply rinstId'_term.
  eapply extRen_term.
  cbn.
  apply (ρ⁻¹).
Qed.