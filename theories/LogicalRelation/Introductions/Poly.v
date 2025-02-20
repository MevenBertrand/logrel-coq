From Coq Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Transitivity EqRedRight InstKripke.

Set Universe Polymorphism.

Lemma subst_wk_id_tail Γ P t : P[t .: @wk_id Γ >> tRel] = P[t..].
Proof. setoid_rewrite id_ren; now bsimpl. Qed.

Set Printing Primitive Projection Parameters.

Section PolyValidity.

  Context `{GenericTypingProperties}.

  Lemma mkPolyRed {Γ l A B} (wfΓ : [|-Γ])
    (RA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩])
    (RB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> a ≅ b : _ | RA Δ ρ wfΔ] -> [Δ ||-<l> B[a .: ρ >> tRel]])
    (RBext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (Rab : [Δ ||-<l> a ≅ b : _ | RA Δ ρ wfΔ]),
      [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a b ρ wfΔ Rab]) :
    PolyRed Γ l A B.
  Proof.
    assert [Γ |- A] by (eapply escape; now eapply instKripke).
    unshelve econstructor; tea.
    unshelve epose proof (h := RB _ (tRel 0) (tRel 0) (@wk1 Γ A) _ _).
    + gen_typing.
    + eapply var0; tea; now rewrite wk1_ren_on.
    + escape. now rewrite <- eq_id_subst_scons in Esch.
  Qed.

  Lemma mkPolyRed' {Γ l A B} (RA : [Γ ||-<l> A])
    (RB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> a ≅ b : _ | wk ρ wfΔ RA] -> [Δ ||-<l> B[a .: ρ >> tRel]])
    (RBext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (Rab : [Δ ||-<l> a ≅ b : _ | wk ρ wfΔ RA]),
      [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a b ρ wfΔ Rab]) :
    PolyRed Γ l A B.
  Proof.
    unshelve eapply mkPolyRed; tea.
    escape; gen_typing.
  Qed.


  Lemma polyCodSubstRed {Γ l F G} (RF : [Γ ||-<l> F]) :
    PolyRed Γ l F G -> forall t u, [Γ ||-<l> t ≅ u : _ | RF] -> [Γ ||-<l> G[t..]].
  Proof.
    intros PFG ???.
    assert (wfΓ : [|- Γ]) by (escape ; gen_typing).
    erewrite <- subst_wk_id_tail.
    eapply (PolyRed.posRed PFG wk_id wfΓ ).
    irrelevance.
  Qed.

  Lemma polyCodSubstExtRed {Γ l F G} (RF : [Γ ||-<l> F]) (PFG : PolyRed Γ l F G) (RG := polyCodSubstRed RF PFG) :
    forall t u (Rt : [Γ ||-<l> t ≅ u : _ | RF]),
    [Γ ||-<l> G[t..] ≅ G[u..]| RG t u Rt].
  Proof.
    intros. assert (wfΓ : [|- Γ]) by (escape; gen_typing).
    irrelevance0; erewrite <- subst_wk_id_tail; [reflexivity|].
    unshelve eapply (PolyRed.posExt PFG wk_id wfΓ); irrelevance.
  Qed.

  Lemma polyRedId {Γ l F G} : PolyRed Γ l F G -> [Γ ||-<l> F] × [Γ ,, F ||-<l> G].
  Proof.
    intros PFG; assert (wfΓ : [|- Γ]) by (destruct PFG; gen_typing).
    split; [exact (instKripke wfΓ (PolyRed.shpRed PFG))| exact (instKripkeSubst wfΓ (PolyRed.posRed PFG))].
  Qed.

  Lemma polyRedEqId {Γ l F F' G G'} (PFG : PolyRed Γ l F G) (RFG := polyRedId PFG) :
    PolyRedEq PFG F' G' -> [Γ ||-<l> F ≅ F' | fst RFG] × [Γ ,, F ||-<l> G ≅ G' | snd RFG].
  Proof.
    intros PFGeq; assert (wfΓ : [|- Γ]) by (destruct PFG; gen_typing).
    split.
    - pose (instKripkeEq wfΓ (PolyRedEq.shpRed PFGeq)); irrelevance.
    - unshelve epose proof (instKripkeSubstEq wfΓ  _).
      7: intros; eapply LRTransEq; [|unshelve eapply (PolyRedEq.posRed PFGeq _ _ (urefl hab))];
        try (unshelve eapply (PolyRed.posExt PFG); tea).
      irrelevance.
  Qed.

  Lemma polyRedEqCodSubstExt {Γ l F F' G G'} (RF : [Γ ||-<l> F]) (PFG : PolyRed Γ l F G) (RG := polyCodSubstRed RF PFG) :
    PolyRedEq PFG F' G' ->
    forall t u (Rt : [Γ ||-<l> t ≅ u : _ | RF]),
    [Γ ||-<l> G[t..] ≅ G'[u..]| RG t u Rt].
  Proof.
    intros Peq *; assert (wfΓ : [|- Γ]) by (destruct PFG; gen_typing).
    unshelve epose proof (h := posRedExt Peq wk_id wfΓ _).
    3: irrelevance.
    rewrite subst_wk_id_tail in h; irrelevance.
  Qed.

  Lemma polyRedSubst {Γ l A B t} (PAB : PolyRed Γ l A B)
    (Rt : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]),
      [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> t[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    (Rtext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]),
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> t[a .: ρ >> tRel] ≅ t[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    : PolyRed Γ l A B[t]⇑.
  Proof.
    destruct PAB; opector; tea.
    + intros; rewrite liftSubst_scons_eq.
      unshelve eapply posRed; [..| eapply Rt]; tea ; now irrelevanceRefl.
    + unshelve epose proof (posRed _ t t (@wk1 Γ A) _ _).
      - escape; gen_typing.
      - replace t with t[tRel 0 .: @wk1 Γ A >> tRel].
        2:now bsimpl.
        eapply Rt.
        eapply var0; tea; now rewrite wk1_ren_on.
      - escape.
        replace (B[_]) with B[t .: @wk1 Γ A >> tRel]; tea.
        now setoid_rewrite wk1_ren.
    + intros; irrelevance0; rewrite liftSubst_scons_eq;[reflexivity|].
      unshelve eapply posExt; tea; eapply Rt + eapply Rtext; cbn; irrelevanceRefl.
      1: now eapply lrefl.
      1: now eapply urefl.
      eassumption.
  Qed.

  Lemma polyRedEqSubst {Γ l A B t u} (PAB : PolyRed Γ l A B)
    (Rtu : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]),
      [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    (PABt : PolyRed Γ l A B[t]⇑)
    : PolyRedEq PABt A B[u]⇑.
  Proof.
    constructor.
    - intros; eapply reflLRTyEq.
    - intros; irrelevance0; rewrite liftSubst_scons_eq; [reflexivity|].
      unshelve eapply PolyRed.posExt; cycle 1; tea.
      eapply Rtu; irrelevanceRefl; now eapply lrefl.
  Qed.

End PolyValidity.
