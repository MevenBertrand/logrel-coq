(** * LogRel.LogicalRelation.InstKripke: combinators to instantiate Kripke-style quantifications *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity Weakening Neutral.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section InstKripke.
Context `{GenericTypingProperties}.

Lemma instKripkeTm {Γ A A' t u l} (wfΓ : [|-Γ])
  {h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (eq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [h Δ ρ wfΔ | Δ ||- t⟨ρ⟩ ≅ u⟨ρ⟩ : _])
  : [instKripke wfΓ h | Γ ||- t ≅ u : _].
Proof.
  specialize (eq Γ wk_id wfΓ); rewrite !wk_id_ren_on in eq.
  eapply irrLREq; tea; now rewrite wk_id_ren_on.
Qed.

Lemma instKripkeFam {Γ A A' B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  : [ Γ ,, A ||-<l> B ≅ B'].
Proof.
  pose proof (instKripke wfΓ hA).
  escape. assert (wfΓA : [|- Γ ,, A]) by gen_typing.
  unshelve epose proof (hinst := hB (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply var0; tea; now bsimpl.
  now rewrite 2!var0_wk1_id in hinst.
Qed.

Lemma instKripkeFamTm {Γ A A' B B' t u l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _])
  : [ instKripkeFam wfΓ hB |  Γ ,, A ||- t ≅ u : _].
Proof.
  pose proof (instKripke wfΓ hA).
  escape. assert (wfΓA : [|- Γ ,, A]) by gen_typing.
  unshelve epose proof (hinst := eq (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply var0; tea; now bsimpl.
  rewrite 2!var0_wk1_id in hinst.
  eapply irrLREq; tea; now rewrite var0_wk1_id.
Qed.

Lemma instKripkeFamConv {Γ A A' B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  : [ Γ ,, A' ||-<l> B ≅ B'].
Proof.
  unshelve eapply instKripkeFam.
  2: intros; symmetry; eauto.
  1: tea.
  unshelve (intros; eapply hB; now eapply irrLRSym); tea.
Qed.


Lemma instKripkeFamConvTm {Γ A A' B B' t u l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _])
  : [ instKripkeFamConv wfΓ hB |  Γ ,, A' ||- t ≅ u : _].
Proof.
  eapply irrLR.
  unshelve eapply instKripkeFamTm.
  2: tea.
  2: intros; symmetry; eauto.
  1: unshelve (intros; eapply hB; now eapply irrLRSym); tea.
  intros; unshelve eapply irrLR, eq; tea; now eapply irrLRSym.
Qed.

Lemma instKripkeSubst {Γ A A' B B' l}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  (RA : [Γ ||-<l> A ≅ A'])
  [t t']
  (ht : [_ ||-<l> t ≅ t' : _ | RA])
  : [ Γ ||-<l> B[t..] ≅ B'[t'..]].
Proof.
  erewrite 2!eq_subst_scons; unshelve eapply hB.
  2:rewrite 2! wk_id_ren_on; eapply irrLREq; tea; now rewrite wk_id_ren_on.
  escape; gtyping.
Qed.

Lemma instKripkeSubstTm {Γ A A' B B' u u' l}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- u[a .: ρ >> tRel] ≅ u'[b .: ρ >> tRel] : _])
  (RA : [Γ ||-<l> A ≅ A'])
  [t t' ]
  (ht : [_ ||-<l> t ≅ t' : _ | RA])
  : [ _ ||-<l> u[t..] ≅ u'[t'..] : _ | instKripkeSubst hB RA ht].
Proof.
  erewrite 2!eq_subst_scons; eapply irrLREq.
  2: unshelve eapply eq.
  1: now rewrite <-eq_subst_scons.
  2: rewrite 2!wk_id_ren_on; eapply irrLREq; tea; now rewrite wk_id_ren_on.
  escape; gtyping.
Qed.

End InstKripke.


