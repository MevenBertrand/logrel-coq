From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Transitivity.
From LogRel.Substitution Require Import Irrelevance Properties Reflexivity.
From LogRel.Substitution.Introductions Require Import Universe.

Set Universe Polymorphism.

Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed.

Lemma subst_wk_id_tail Γ P t : P[t .: @wk_id Γ >> tRel] = P[t..].
Proof. setoid_rewrite id_ren; now bsimpl. Qed.

(* Also used in EqRedRight *)
Lemma eq_id_subst_scons {Γ A} B : B = B[tRel 0 .: @wk1 Γ A >> tRel].
Proof.
  clear; bsimpl; rewrite scons_eta'; now bsimpl.
Qed.


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
    PolyRed Γ l F G -> forall t, [Γ ||-<l> t : _ | RF] -> [Γ ||-<l> G[t..]].
  Proof.
    intros PFG ??.
    escape. assert (wfΓ : [|- Γ]) by gen_typing.
    erewrite <- subst_wk_id_tail.
    eapply (PolyRed.posRed PFG wk_id wfΓ).
    irrelevance.
  Qed.

  Lemma polyCodSubstExtRed {Γ l F G} (RF : [Γ ||-<l> F]) (PFG : PolyRed Γ l F G) (RG := polyCodSubstRed RF PFG) :
    forall t u (Rt : [Γ ||-<l> t : _ | RF]), [Γ ||-<l> u : _ | RF] -> [Γ ||-<l> t ≅ u : _ | RF] ->
    [Γ ||-<l> G[t..] ≅ G[u..]| RG t Rt].
  Proof.
    intros. escape. assert (wfΓ : [|- Γ]) by gen_typing.
    irrelevance0; erewrite <- subst_wk_id_tail; [reflexivity|].
    unshelve eapply (PolyRed.posExt PFG wk_id wfΓ); irrelevance.
  Qed.


  Lemma polyRedId {Γ l F G} : PolyRed Γ l F G -> [Γ ||-<l> F] × [Γ ,, F ||-<l> G].
  Proof.
    intros [?? RF RG]; split.
    -  rewrite <- (wk_id_ren_on Γ F). eapply RF; gen_typing.
    - replace G with G[tRel 0 .: @wk1 Γ F >> tRel].
      2: bsimpl; rewrite scons_eta'; now asimpl.
      eapply RG. eapply var0; tea; now bsimpl.
      Unshelve. gen_typing.
  Qed.

  Lemma polyRedEqId {Γ l F F' G G'} (PFG : PolyRed Γ l F G) (RFG := polyRedId PFG) :
    PolyRedEq PFG F' G' -> [Γ ||-<l> F ≅ F' | fst RFG] × [Γ ,, F ||-<l> G ≅ G' | snd RFG].
  Proof.
    intros [RFF' RGG']; destruct RFG; escape; split.
    - rewrite <- (wk_id_ren_on Γ F'); irrelevance0.
      2: unshelve eapply RFF'; gen_typing.
      apply wk_id_ren_on.
    - replace G' with G'[tRel 0 .: @wk1 Γ F >> tRel].
      2: bsimpl; rewrite scons_eta'; now asimpl.
      irrelevance0.
      2: eapply RGG'.
      bsimpl; rewrite scons_eta'; now asimpl.
      Unshelve. 2: gen_typing.
      2: eapply var0; tea; now bsimpl.
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
        2:{ bsimpl; rewrite scons_eta'; now asimpl. }
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

  Context {l Γ F G} (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ,, F ||-v< l > G | validSnoc VΓ VF]).

  Context {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ]).

  Lemma substPolyRed : PolyRed Δ l F[σ] G[up_term_term σ].
  Proof.
    pose proof (Vuσ := liftSubstEq' VF Vσσ').
    instValid Vσσ'; instValid Vuσ; escape.
    unshelve econstructor; tea.
    - intros; now eapply wk.
    - cbn; intros ??? ρ wfΔ' hab.
      rewrite eq_subst_2.
      pose proof (Vawkσ := consWkSubstEq VF Vσσ' ρ wfΔ' hab).
      now instValid Vawkσ.
    - cbn; intros ??? ρ wfΔ' hab.
      epose proof (Vabwkσ := consWkSubstEq VF (lrefl Vσσ') ρ wfΔ' hab).
      instValid Vabwkσ.
      rewrite !eq_subst_2; irrelevance.
  Qed.

  Lemma substEqPolyRedEq {F' G'} (VF' : [Γ ||-v< l > F' | VΓ ])
    (VG' : [Γ ,, F' ||-v< l > G' | validSnoc VΓ VF'])
    (VFF' : [Γ ||-v< l > F ≅ F' | VΓ | VF])
    (VGG' : [Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF | VG])
    (PFGσ : PolyRed Δ l F[σ] G[up_term_term σ])
    : PolyRedEq PFGσ F'[σ'] G'[up_term_term σ'].
  Proof.
     instValid Vσσ'.
    unshelve econstructor.
    - intros; irrelevanceRefl; now unshelve now eapply wkEq.
    - intros ??? ρ wfΔ' hab; rewrite eq_subst_2.
      unshelve epose proof (Vabwkσ := consWkSubstEq VF Vσσ' ρ wfΔ' (lrefl hab)).
      instValid Vabwkσ; irrelevance0; [|tea].
      now rewrite eq_subst_2.
  Qed.

  Lemma substPolyRedEq (PFGσ : PolyRed Δ l F[σ] G[up_term_term σ])
    : PolyRedEq PFGσ F[σ'] G[up_term_term σ'].
  Proof.
    eapply substEqPolyRedEq; tea.
    all: eapply reflValidTy.
  Qed.

End PolyValidity.


