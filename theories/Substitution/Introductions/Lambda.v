From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Escape Reflexivity Neutral Weakening Irrelevance Application Reduction Transitivity NormalRed EqRedRight InstKripke.
From LogRel.Substitution Require Import Irrelevance Properties SingleSubst Reflexivity Conversion Reduction.
From LogRel.Substitution.Introductions Require Import Pi.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Lemma isLRFun_isWfFun `{GenericTypingProperties}
  {l Γ F G t} (RΠFG : [Γ ||-< l > tProd F G])
  (Rt : isLRFun (normRedΠ0 (invLRΠ RΠFG)) t)
  : isWfFun Γ F G t.
Proof.
  assert (wfΓ: [|- Γ]) by (escape ; gen_typing).
  destruct Rt as [?? eqA eqt|]; cbn in *.
  2: now constructor.
  pose proof (RFA := instKripkeEq wfΓ eqA).
  pose proof (LRTyEqRedRight _ RFA).
  pose proof (instKripkeSubstTmEq wfΓ eqt).
  pose proof (instKripkeSubstConvTmEq wfΓ eqA eqt).
  escape.
  now constructor.
Qed.


Section LambdaValid.
Context `{GenericTypingProperties}.

Context {Γ F G l}
  {VΓ : [||-v Γ]}
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G | VΓF])
  (VΠFG := PiValid VΓ VF VG).


Lemma consWkEq {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma eq_subst_3 t a ρ σ : t[up_term_term σ][a .: ρ >> tRel] = t[up_term_term σ⟨ρ⟩][a..].
Proof.
  bsimpl ; now substify.
Qed.

Lemma eq_subst_4 t a σ : t[up_term_term σ][a..] = t[a .: σ].
Proof.
  bsimpl ; now substify.
Qed.


Lemma eq_upren t σ ρ : t[up_term_term σ]⟨upRen_term_term ρ⟩ = t[up_term_term σ⟨ρ⟩].
Proof. asimpl; unfold Ren1_subst; asimpl; substify; now asimpl. Qed.

Lemma eq_substren t σ ρ : t[σ]⟨ρ⟩ = t[σ⟨ρ⟩].
Proof. now asimpl. Qed.


Lemma lamPiRedTm {F' G'}
  (VF' : [Γ ||-v<l> F' | VΓ])
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VG' : [Γ ,, F ||-v<l> G' | VΓF])
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG])
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} (wfΔ : [|-Δ]) {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-Π<l> (tProd F G)[σ]])
  (R := normRedΠ0 R0)
  : PiRedTm R (tLambda F' t')[σ'].
Proof.
  refold.
  pose proof (VG'':=convCtx1 VΓ VΓF (validSnoc VΓ VF') VF  VFF' VG').
  epose proof (PiCong VΓ VF VG VF' VG'' VFF' VGG').
  epose proof (VtG' := conv VΓF VG VG' VGG' Vtt').
  epose proof (convTmEqCtx1 VΓ VΓF (validSnoc VΓ VF') VF  VG' VG'' VFF' VtG').
  instValid (liftSubstEq' VF' (urefl Vσσ'));
  instValid Vσσ'; instValid (urefl Vσσ'). escape.

  econstructor.
  1: eapply redtmwf_refl, ty_conv; [now eapply ty_lam| now symmetry].

  constructor; intros; cbn.
  2: epose (Vaσ := consWkSubstEq VF Vσσ' ρ h (lrefl ha)).
  all: irrelevanceRefl.
  1: now unshelve eapply wkEq.

  rewrite 2! consWkEq'.
  pose proof (ureflValidTm Vtt').
  unshelve epose (Vaσ' := consWkSubstEq VF (urefl Vσσ') ρ h _).
  4: eapply LRTmEqConv; [|tea]; irrelevanceRefl; eapply wkEq; tea.
  1: now eapply wk.
  instValid Vaσ'.
  eapply LRTmEqConv;[|tea].
  rewrite consWkEq'; eapply LRTyEqSym.
  now instValid Vaσ.
  Unshelve. 2: rewrite consWkEq'; now instValid Vaσ. tea.
Defined.

Lemma lamCongValid {F' G'}
  (VF' : [Γ ||-v<l> F' | VΓ])
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VG' : [Γ ,, F ||-v<l> G' | VΓF])
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG])

{t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
   :
    [Γ ||-v<l> tLambda F t ≅ tLambda F' t' : tProd F G | VΓ | VΠFG ].
Proof.
  econstructor; intros. cbn -[PiValid].
  normRedΠ R; refold.
  pose proof (VG'':=convCtx1 VΓ VΓF (validSnoc VΓ VF') VF VFF' VG').
  epose proof (PiCong VΓ VF VG VF' VG'' VFF' VGG').
  epose proof (VtG' := conv VΓF VG VG' VGG' Vtt').
  epose proof (convTmEqCtx1 VΓ VΓF (validSnoc VΓ VF') VF VG' VG'' VFF' VtG').
  simple refine (let ht : PiRedTm R (tLambda F t)[σ] := _ in _).
  1:{
    pose proof (VFF := reflValidTy VF).
    pose proof (VGG := reflValidTy VG).
    pose proof (Vtt := lreflValidTm _ Vtt').
    eapply (lamPiRedTm VF VFF VG VGG Vtt wfΔ (lrefl Vσσ') _).
  }
  simple refine (let ht' : PiRedTm R (tLambda F' t')[σ'] := _ in _).
  1: eapply (lamPiRedTm VF' VFF' VG' VGG' Vtt' wfΔ Vσσ' _).
  assert (h : forall (Δ0 : context) (a b : term),
    PiRedTmEq.appRed R (PiRedTmEq.nf ht) (PiRedTmEq.nf ht') Δ0 a b).
  1:{
    cbn; intros.
    set (RF := PolyRed.shpRed _ _ _) in hab.
    pose proof (Vσρ := wkSubstSEq VΓ wfΔ h ρ Vσσ').
    pose proof (Vσρ' := wkSubstSEq VΓ wfΔ h ρ (urefl Vσσ')).
    instValid Vσρ'; instValid (liftSubstEq' VF Vσρ).
    instValid Vσρ; instValid (liftSubstEq' VF' Vσρ').
    instValid (consWkSubstEq VF Vσσ' ρ h hab).
    escape. irrelevance0.
    1: now rewrite eq_subst_3.
    eapply redSubstTmEq; cycle 1.
    * eapply redtm_beta; tea.
      now rewrite eq_upren, eq_substren.
    * eapply redtm_beta.
      1,3: rewrite eq_substren; tea.
      1: eapply ty_conv; tea; cbn.
      1: replace F[_]⟨_⟩ with F[σ⟨ρ⟩]; tea; symmetry; apply eq_substren.
      now rewrite eq_upren, eq_substren.
      Unshelve. 2: now rewrite eq_subst_4.
    * now rewrite !eq_subst_4.
    * now rewrite !eq_upren, !eq_subst_4.
  }
  unshelve econstructor; tea.
  cbn; instValid (liftSubstEq' VF Vσσ'); instValid Vσσ'; escape.
  eapply convtm_eta; tea.
  * destruct ht; gen_typing.
  * eapply isLRFun_isWfFun; exact (PiRedTmEq.isfun ht).
  * destruct ht' as [? red ?]; cbn in red; gen_typing.
  * eapply isLRFun_isWfFun; exact (PiRedTmEq.isfun ht').
  * unshelve epose proof (r := h (Δ ,, F[σ]) (tRel 0) (tRel 0) (wk1 F[σ]) _ _).
    + gen_typing.
    + eapply var0; [now rewrite wk1_ren_on| assumption].
    + erewrite <- 2!wk1_ren_on; eapply convtm_meta_conv; [| | reflexivity].
      1: eapply escapeEqTerm, r.
      now rewrite <- eq_id_subst_scons.
  Qed.


Lemma singleSubst_subst_eq t a σ : t[a..][σ] = t[up_term_term σ][a[σ]..].
Proof. now bsimpl. Qed.

Lemma singleSubst_subst_eq' t a σ : t[a..][σ] = t[a[σ] .: σ].
Proof. now bsimpl. Qed.

Lemma betaValid {t a} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG])
  (Va : [Γ ||-v<l> a : F | VΓ | VF]) :
  [Γ ||-v<l> tApp (tLambda F t) a ≅ t[a..] : G[a..] | VΓ | substS VG Va].
Proof.
  eapply redSubstValid.
  2: eapply substSTm ; irrValid.
  constructor; intros; cbn.
  rewrite 2!singleSubst_subst_eq.
  instValid (lrefl Vσσ').
  instValid (liftSubstEq' VF (lrefl Vσσ')).
  escape; now eapply redtm_beta.
Qed.


Lemma redtm_app_helper {Δ Δ' f nf a σ} (ρ : Δ' ≤ Δ) :
  [|- Δ'] ->
  [Δ |- f[σ] ⤳* nf : (tProd F G)[σ]] ->
  [Δ' |- a : F[σ]⟨ρ⟩] ->
  [Δ' |- tApp f[σ]⟨ρ⟩ a ⤳* tApp nf⟨ρ⟩ a : G[up_term_term σ][a .: ρ >> tRel]].
Proof.
  intros red tya.
  rewrite eq_subst_3; eapply redtm_app; tea.
  eapply redtm_meta_conv; [now eapply redtm_wk| | reflexivity].
  cbn; now rewrite eq_upren.
Qed.


Lemma ηeqEqTermNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := normRedΠ0 (invLRΠ (validTy VΠFG wfΔ Vσ)))
  (RGσ : [Δ ,, F[σ] ||-<l> G[up_term_term σ]])
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | LRPi' RΠFG ]) :
  [RGσ | Δ ,, F[σ] ||- tApp f⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp Rf.(PiRedTmEq.redR).(PiRedTmEq.nf)⟨↑⟩ (tRel 0) : G[up_term_term σ]].
Proof.
  refold.
  pose (VσUp :=  liftSubstEq' VF Vσ).
  instValid Vσ; instValid VσUp; escape.
  assert (wfΔF : [|- Δ,, F[σ]]) by gen_typing.
  unshelve epose proof (r := PiRedTmEq.eqApp Rf (@wk1 Δ F[σ]) wfΔF (var0 _ _ _)); tea.
  1: now rewrite wk1_ren_on.
  irrelevance0; [ erewrite (eq_id_subst_scons (G[_])); reflexivity|].
  eapply redSubstLeftTmEq.
  + erewrite <- wk1_ren_on; irrelevance.
  + clear r; destruct Rf.(PiRedTmEq.redL) as [? [? red] ?]; cbn -[wk1] in *.
    replace f⟨ρ⟩[up_term_term σ] with f[σ]⟨@wk1 Δ F[σ]⟩.
    eapply redtm_app_helper; tea.
    1: rewrite wk1_ren_on; now eapply ty_var0.
    unfold ρ; now bsimpl.
    Unshelve. 2: now rewrite <- eq_id_subst_scons.
Qed.


Lemma ηeqEqTermConvNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := normRedΠ0 (invLRΠ (validTy VΠFG wfΔ Vσ)))
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | LRPi' RΠFG ]) :
  (* (Rf0 : PiRedTm RΠFG (f[σ])) : *)
  [Δ ,, F[σ] |- tApp f⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp Rf.(PiRedTmEq.redR).(PiRedTmEq.nf)⟨↑⟩ (tRel 0) : G[up_term_term σ]].
Proof.
  refold.
  pose (VσUp :=  liftSubstEq' VF Vσ); instValid VσUp.
  now unshelve eapply escapeEqTerm, ηeqEqTermNf.
Qed.


Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ F)
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ])
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := validTy VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠFG ])
  (Rg : [Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠFG ]) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | RΠFG ].
Proof.
  normRedΠin Rf; normRedΠin Rg; set (RΠ := normRedΠ0 _) in Rf, Rg; refold.
  enough [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | LRPi' RΠ ] by irrelevance.
  pose (Rf0 := Rf.(PiRedTmEq.redR)); pose (Rg0 := Rg.(PiRedTmEq.redR)).
  exists Rf0 Rg0.
  - cbn; pose (VσUp :=  liftSubstEq' VF Vσ).
    instValid Vσ; instValid VσUp; escape.
    eapply convtm_eta; tea.
    2,4: eapply isLRFun_isWfFun, PiRedTmEq.isfun.
    + destruct Rf0; cbn in *; gen_typing.
    + destruct Rg0; cbn in *; gen_typing.
    + etransitivity ; [symmetry| etransitivity]; tea; eapply ηeqEqTermConvNf.
  - cbn; intros ??? ρ' h ha.
    epose (Vν := consWkSubstEq VF Vσ ρ' h (lrefl ha)); instValid Vν.
    assert (eq : forall t a, t⟨ρ⟩[a .: σ⟨ρ'⟩] = t[σ]⟨ρ'⟩) by (intros; unfold ρ; now bsimpl).
    cbn in RVfg; rewrite 2!eq in RVfg.
    etransitivity; [| etransitivity].
    + symmetry; eapply redSubstLeftTmEq.
      1: pose proof (urefl (PiRedTmEq.eqApp Rf ρ' h (lrefl ha))); irrelevance.
      eapply redtm_app_helper; tea; [| now escape].
      now destruct (PiRedTmEq.redR Rf) as [? []].
    + irrelevance0; tea; now rewrite Poly.eq_subst_2.
    + eapply redSubstLeftTmEq.
      1: pose proof (rg := PiRedTmEq.eqApp Rg ρ' h ha); irrelevance.
      eapply redtm_app_helper; tea; [| now escape].
      now destruct (PiRedTmEq.redL Rg) as [? []].
Qed.

Lemma etaeqValid {f g} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd F G | VΓ | VΠFG ])
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd F G | VΓ | VΠFG].
Proof.
  constructor; intros ???? Vσ; instValid Vσ; instValid (lrefl Vσ).
  etransitivity.
  + irrelevanceRefl;eapply ηeqEqTerm; tea.
  + irrelevance.
Qed.

End LambdaValid.
