(** * LogRel.LogicalRelation.InstKripke: combinators to instantiate Kripke-style quantifications *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Reflexivity Neutral Weakening Irrelevance Application Reduction Transitivity NormalRed EqRedRight.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.


Lemma instKripkeEq `{GenericTypingProperties} {Γ A B l} (wfΓ : [|-Γ])
  {h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  (eq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [h Δ ρ wfΔ | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩])
  : [instKripke wfΓ h | Γ ||- A ≅ B].
Proof.
  specialize (eq Γ wk_id wfΓ); rewrite wk_id_ren_on in eq.
  irrelevance.
Qed.

Lemma instKripkeTmEq `{GenericTypingProperties} {Γ A t u l} (wfΓ : [|-Γ])
  {h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  (eq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [h Δ ρ wfΔ | Δ ||- t⟨ρ⟩ ≅ u⟨ρ⟩ : _])
  : [instKripke wfΓ h | Γ ||- t ≅ u : _].
Proof.
  specialize (eq Γ wk_id wfΓ); rewrite !wk_id_ren_on in eq.
  irrelevance.
Qed.

Lemma instKripkeSubst `{GenericTypingProperties} {Γ A B l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel]])
  : [ Γ ,, A ||-<l> B].
Proof.
  pose proof (instKripke wfΓ hA).
  escape. assert (wfΓA : [|- Γ ,, A]) by gen_typing.
  unshelve epose proof (hinst := hB (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply var0; tea; now bsimpl.
  now rewrite <- eq_id_subst_scons in hinst.
Qed.

Lemma instKripkeSubstEq `{GenericTypingProperties} {Γ A B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  : [ instKripkeSubst wfΓ hB |  Γ ,, A ||- _ ≅ B'].
Proof.
  pose proof (instKripke wfΓ hA).
  escape. assert (wfΓA : [|- Γ ,, A]) by gen_typing.
  unshelve epose proof (hinst := eq (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply var0; tea; now bsimpl.
  rewrite <- eq_id_subst_scons in hinst.
  irrelevance; now rewrite <- eq_id_subst_scons.
Qed.

Lemma instKripkeSubstTmEq `{GenericTypingProperties} {Γ A B t u l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _])
  : [ instKripkeSubst wfΓ hB |  Γ ,, A ||- t ≅ u : _].
Proof.
  pose proof (instKripke wfΓ hA).
  escape. assert (wfΓA : [|- Γ ,, A]) by gen_typing.
  unshelve epose proof (hinst := eq (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply var0; tea; now bsimpl.
  rewrite <- ! eq_id_subst_scons in hinst.
  irrelevance; now rewrite <- eq_id_subst_scons.
Qed.

Lemma instKripkeSubstConv `{GenericTypingProperties} {Γ A A' B l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  (eq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [hA Δ ρ wfΔ | Δ ||- A⟨ρ⟩ ≅ A'⟨ρ⟩])
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel]])
  : [ Γ ,, A' ||-<l> B].
Proof.
  pose proof (instKripkeEq wfΓ eq).
  escape. assert (wfΓA' : [|- Γ ,, A']) by gen_typing.
  unshelve epose proof (hinst := hB (Γ ,, A') (tRel 0) (tRel 0) (@wk1 Γ A') wfΓA' _).
  1: now unshelve (eapply var0conv; tea; symmetry; erewrite <- wk1_ren_on; now eapply escapeEq, wkEq).
  now rewrite <- eq_id_subst_scons in hinst.
Qed.

Lemma instKripkeSubstConvEq `{GenericTypingProperties} {Γ A A' B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  (eqA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [hA Δ ρ wfΔ | Δ ||- A⟨ρ⟩ ≅ A'⟨ρ⟩])
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  : [ instKripkeSubstConv wfΓ eqA hB |  Γ ,, A' ||- _ ≅ B'].
Proof.
  pose proof (instKripkeEq wfΓ eqA).
  escape. assert (wfΓA' : [|- Γ ,, A']) by gen_typing.
  unshelve epose proof (hinst := eq (Γ ,, A') (tRel 0) (tRel 0) (@wk1 Γ A') wfΓA' _).
  1: now unshelve (eapply var0conv; tea; symmetry; erewrite <- wk1_ren_on; now eapply escapeEq, wkEq).
  rewrite <- eq_id_subst_scons in hinst.
  irrelevance; now rewrite <- eq_id_subst_scons.
Qed.

Lemma instKripkeSubstConvTmEq `{GenericTypingProperties} {Γ A A' B t u l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]}
  (eqA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [hA Δ ρ wfΔ | Δ ||- A⟨ρ⟩ ≅ A'⟨ρ⟩])
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _])
  : [ instKripkeSubstConv wfΓ eqA hB |  Γ ,, A' ||- t ≅ u : _].
Proof.
  pose proof (instKripkeEq wfΓ eqA).
  escape. assert (wfΓA' : [|- Γ ,, A']) by gen_typing.
  unshelve epose proof (hinst := eq (Γ ,, A') (tRel 0) (tRel 0) (@wk1 Γ A') wfΓA' _).
  1: now unshelve (eapply var0conv; tea; symmetry; erewrite <- wk1_ren_on; now eapply escapeEq, wkEq).
  rewrite <- ! eq_id_subst_scons in hinst.
  irrelevance; now rewrite <- eq_id_subst_scons.
Qed.
