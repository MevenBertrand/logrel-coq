From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity Irrelevance.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Properties.
Context `{GenericTypingProperties}.

Lemma wellformedSubstEq {Γ Γ' σ σ' Δ} (VΓ : [||-v Γ ≅ Γ' ]) (wfΔ : [|- Δ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ] -> [Δ |-s σ ≅ σ' : Γ].
Proof.
  revert Δ wfΔ σ σ'; indValid VΓ.
  - intros. apply conv_sempty.
  - intros * ih ???? []. apply conv_scons.
    + now eapply ih.
    + now escape.
Qed.

Lemma consSubst {Γ Γ' σ σ' t u l A A' Δ} (VΓ : [||-v Γ ≅ Γ']) (wfΔ : [|- Δ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vtu : [Δ ||-<l> t ≅ u : A[σ] | validTyExt VA wfΔ Vσσ']) :
  [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ ].
Proof.
  unshelve econstructor; tea.
Qed.


Lemma consValidSubst {Γ Γ' σ σ' t u l A A' Δ} {VΓ : [||-v Γ ≅ Γ']} {wfΔ : [|- Δ]}
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  {VA : [Γ ||-v<l> A ≅ A' | VΓ]}
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Δ ||-v (t[σ] .: σ) ≅  (u[σ'] .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ ].
Proof.
  unshelve econstructor; intros; tea.
  now apply validTmExt.
Qed.

Lemma wkSubst {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) :
  forall {σ σ' Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ' ≤ Δ),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' ].
Proof.
  indValid VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply ih ; eassumption.
    + eapply irrLREq.
      2: now unshelve now eapply wkLR.
      now asimpl.
Qed.

Lemma wk1Subst {Γ Γ' σ σ' Δ F} (VΓ : [||-v Γ ≅ Γ'])
  (wfΔ : [|- Δ]) (wfF : [Δ |- F]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  let ρ := @wk1 Δ F in
  [Δ ,, F ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfc_cons wfΔ wfF ].
Proof.
  intro vσσ'. eapply wkSubst ; eassumption.
Qed.

Lemma consWkSubstEq {Γ Γ' Δ Ξ A A' B σ σ' a b l} {VΓ : [||-v Γ ≅ Γ']} {wfΔ : [|- Δ]}
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  (ρ : Ξ ≤ Δ) wfΞ {RA : [Ξ ||-<l> A[σ]⟨ρ⟩ ≅ B]}
  (Rab : [Ξ ||-<l> a ≅ b : A[σ]⟨ρ⟩ | RA]) :
  [Ξ ||-v (a .: σ⟨ρ⟩) ≅  (b .: σ'⟨ρ⟩) : Γ ,, A | validSnoc VΓ VA | wfΞ ].
Proof.
  unshelve eapply consSubst.
  1: now eapply wkSubst.
  eapply irrLREq; tea; now asimpl.
Qed.


Lemma liftSubst {Γ Γ' σ σ' Δ lF F F'}
  (VΓ : [||-v Γ ≅ Γ']) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (escape (validTyExt VF wfΔ Vσσ')) in
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) ≅ (tRel 0 .: σ' ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros; unshelve econstructor.
  + now apply wk1Subst.
  + eapply var0; unfold ρ; [now bsimpl|].
    now eapply escape, VF.
Qed.

Lemma liftSubst' {Γ Γ' σ σ' Δ lF F F'} {VΓ : [||-v Γ ≅ Γ' ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσ : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let wfΔF := wfc_cons wfΔ (escape (validTyExt VF wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v up_term_term σ ≅ up_term_term σ' : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros; eapply irrelevanceSubstEqExt.
  3: unshelve eapply liftSubst.
  1-2: intros ?; now bsimpl.
Qed.

Lemma liftSubstSym' {Γ Γ' σ σ' Δ lF F F'} {VΓ : [||-v Γ ≅ Γ' ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσ : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := symValid (validSnoc VΓ VF) in
  let wfΔF := wfc_cons wfΔ (escape (validTyExt (symValidTy' VF) wfΔ (symSubst _ _ _ _ Vσ))) in
  [Δ ,, F'[σ'] ||-v up_term_term σ' ≅ up_term_term σ : Γ' ,, F' | VΓF | wfΔF ].
Proof.
  unshelve eapply irrelevanceSubst, liftSubst'; cycle 3; [now eapply symValidTy'|..]; tea.
  now eapply symSubst.
Qed.




Lemma wk1ValidTy {Γ Γ' lA A A' lF F F'} {VΓ : [||-v Γ ≅ Γ']} (VF : [Γ ||-v<lF> F ≅ F' | VΓ]) :
  [Γ ||-v<lA> A ≅ A' | VΓ] ->
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ ≅ A' ⟨ @wk1 Γ' F' ⟩ | validSnoc VΓ VF ].
Proof.
  intros VA; constructor; intros * [tl hd].
  rewrite 2!wk1_subst; now eapply validTyExt.
Qed.

Lemma wk1ValidTm {Γ Γ' lA t u A A' lF F F'} {VΓ : [||-v Γ ≅ Γ']}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (VA : [Γ ||-v<lA> A ≅ A' | VΓ])
  (Vt : [Γ ||-v<lA> t ≅ u : A | VΓ | VA]) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  constructor; intros ???? [] ; rewrite !wk1_subst.
  now unshelve (eapply irrLREq, validTmExt ; tea; now rewrite wk1_subst).
Qed.

Lemma embValidTy@{u i j k l} {Γ Γ' l l' A A'}
    {VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']} (h : l << l')
    (VA : typeValidity@{u i j k l} Γ _ VΓ l A A' (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ _ VΓ l' A A' (*[Γ ||-v<l'> A |VΓ]*).
Proof.
  constructor; intros ???? [pack]%(validTyExt VA _).
  exists pack; now eapply LR_embedding.
Defined.

Lemma embValidTyOne @{u i j k l} {Γ Γ' l A A'}
    {VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']}
    (VA : typeValidity@{u i j k l} Γ Γ' VΓ l A A' (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ Γ' VΓ one A A' (*[Γ ||-v<one> A |VΓ]*).
Proof.
  destruct l; tea; now eapply (embValidTy Oi).
Defined.

Lemma soundCtxId {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) :
  ∑ wfΓ : [|- Γ], [Γ ||-v tRel : Γ | VΓ | wfΓ].
Proof.
  indValid VΓ.
  - exists wfc_nil; constructor.
  - intros ????? VΓ VA [wfΓ ih].
    pose proof (RA := validTyExt VA _ ih).
    assert (hA : [Γ |- A]) by (rewrite <- subst_rel; exact (escape RA)).
    pose (wfΓA := wfc_cons wfΓ hA).
    assert (Vs : [VΓ | _ ||-v ↑ >> tRel : _ | wfΓA]).
    1:{
      eapply irrelevanceSubstEqExt.
      3: eapply (wkSubst _ _ _ (@wk1 Γ A)), ih.
      all: intros ?; now bsimpl.
    }
    exists wfΓA; exists Vs.
    eapply var0; tea.
    rewrite <-(subst_rel A⟨↑⟩); now asimpl.
Qed.


Definition escapeValid {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) : [|-Γ] := (soundCtxId VΓ).π1.

Definition idSubst {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v tRel : Γ | VΓ | _] := (soundCtxId VΓ).π2.

Lemma redValidTy {Γ Γ' A A' l} {VΓ : [||-v Γ ≅ Γ']} (vA : [_ ||-v<l> A ≅ A' | VΓ ]) : [Γ ||-<l> A ≅ A'].
Proof. intros; instValid (idSubst VΓ); now rewrite !subst_rel in *. Qed.

Lemma redValidTm {Γ Γ' A A' l t t'} {VΓ : [||-v Γ ≅ Γ']} {VA : [_ ||-v<l> A ≅ A' | VΓ ]}
  (Vt : [Γ ||-v<l> t ≅ t' : _ | _ | VA]) :  [Γ ||-<l> t ≅ t' : _ | redValidTy VA ].
Proof. intros; instValid (idSubst VΓ); rewrite !subst_rel in *; eapply irrLREq; tea; now rewrite subst_rel. Qed.

Lemma redValidTm' {Γ Γ' A A' l t t'} {VΓ : [||-v Γ ≅ Γ']} {VA : [_ ||-v<l> A ≅ A' | VΓ ]}
  (RA : [Γ ||-<l> A ≅ A']) (Vt : [Γ ||-v<l> t ≅ t' : _ | _ | VA]) :  [Γ ||-<l> t ≅ t' : _ | RA].
Proof. now eapply irrLR, redValidTm. Qed.


Lemma wkrenSubst {Γ Δ} (ρ : Δ ≤ Γ) :
  forall {Γ' Δ'} (VΓ : [||-v Γ ≅ Γ']) (VΔ : [||-v Δ ≅ Δ'])  {Ξ σ σ'} (wfΞ : [|- Ξ]),
  [VΔ | Ξ ||-v σ ≅ σ' : _ | wfΞ] -> [VΓ | Ξ ||-v ρ >> σ ≅ ρ >> σ' : _ | wfΞ].
Proof.
  destruct ρ as [? wwk]; induction wwk.
  + intros; pose proof (invValidity VΓ) as [? h]; subst; cbn in h; subst ; constructor.
  + intros * Vσ.
    pose proof (invValidity VΔ) as (?&?&?&?&?&?&h); subst; cbn in h; subst.
    destruct Vσ as [tl hd].
    eapply irrelevanceSubstEqExt.
    3: eapply IHwwk, tl.
    - rewrite <- (scons_eta' σ) at 1; reflexivity.
    - rewrite <- (scons_eta' σ') at 1; reflexivity.
  + intros * Vσ.
    pose proof (invValidity VΔ) as (?&?&?&?&?&?&h); subst; cbn in h; subst.
    pose proof (invValidity VΓ) as (?&?&?&?&?&?&h); subst; cbn in h; subst.
    destruct Vσ as [tl hd].
    eapply irrelevanceSubstEqExt.
    1:{ rewrite <- (scons_eta' σ); cbn; unfold up_ren; rewrite scons_comp'; cbn. reflexivity. }
    1:{ rewrite <- (scons_eta' σ'); cbn; unfold up_ren; rewrite scons_comp'; cbn. reflexivity. }
    opector; [now eapply IHwwk|].
    cbn;  eapply irrLREqCum; tea; now bsimpl.
Qed.

Lemma wkValidTy {l Γ Γ' Δ Δ' A A'} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ ≅ Γ'])
  (VΔ : [||-v Δ ≅ Δ'])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ]) :
  [Δ ||-v<l> A⟨ρ⟩ ≅ A'⟨ρ⟩ | VΔ].
Proof.
  constructor; intros; cbn; rewrite !ren_subst.
    eapply validTyExt; tea; now eapply wkrenSubst.
Qed.

Lemma wkValidTm {l Γ Γ' Δ Δ' A A' t u} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ ≅ Γ'])
  (VΔ : [||-v Δ ≅ Δ'])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vt : [Γ ||-v<l> t ≅ u: A | VΓ | VA]) :
  [Δ ||-v<l> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | VΔ | wkValidTy ρ VΓ VΔ VA].
Proof.
  econstructor; intros; rewrite 2!ren_subst.
  (unshelve now eapply irrLREq, validTmExt; tea; rewrite ren_subst); tea.
  now eapply wkrenSubst.
Qed.

Lemma escapeValidTy {Γ Γ' A A' l} (VΓ : [||-v Γ ≅ Γ']) : [_ ||-v<l> A ≅ A' | VΓ ] -> [Γ |- A] × [Γ |- A'] × [Γ |-  A ≅ A'].
Proof.
  intros VA;  generalize (validTyExt VA _ (idSubst VΓ)); rewrite 2!subst_rel; intros; now escape.
Qed.

Lemma escapeValidTm {Γ Γ' A A' l t t'} (VΓ : [||-v Γ ≅ Γ'])
  (VA : [_ ||-v<l> A ≅ A' | VΓ ]) :
  [_ ||-v<l> t ≅ t' : _ | _ | VA] -> [Γ |- t : A] × [Γ |- t' : A] × [Γ |- t ≅ t' : A].
Proof.
  intros Vt; pose proof (validTmExt Vt _ (idSubst VΓ)); escape.
  rewrite !subst_rel in *. now repeat split.
Qed.

Lemma redSubstValid {Γ Γ' A A' t u l}
  (VΓ : [||-v Γ ≅ Γ'])
  (red : [Γ ||-v t ⤳* u : A | VΓ])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vu : [Γ ||-v<l> u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA].
Proof.
  constructor; intros. eapply redSubstLeftTmEq.
  1: now eapply validTmExt.
  now eapply validRed.
Qed.

Lemma substS {Γ Γ' F F' G G' t t' l} {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VG : [Γ,, F ||-v<l> G ≅ G' | validSnoc VΓ VF])
  (Vt : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ].
Proof.
  constructor; intros; rewrite 2!singleSubstComm.
  eapply validTyExt; tea; now eapply consValidSubst.
Qed.

Lemma substSTm {Γ Γ' F F' G G' t t' f f' l} (VΓ : [||-v Γ ≅ Γ'])
  (VF : [Γ ||-v<l> F ≅ F' | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF])
  (Vff' : [Γ ,, F ||-v<l> f ≅ f' : G | VΓF | VG]) :
  [Γ ||-v<l> f[t..] ≅ f'[t'..] : G[t..] | VΓ | substS VG Vtt'].
Proof.
  constructor; intros; rewrite !singleSubstComm.
  eapply irrLREq.
  1: symmetry; apply singleSubstComm.
  (unshelve now eapply validTmExt); tea.
  now eapply consValidSubst.
Qed.

Lemma substLiftS {Γ Γ' F F' G G' t t' l} (VΓ : [||-v Γ ≅ Γ'])
  (VF : [Γ ||-v<l> F ≅ F'| VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G ≅ G' | VΓF])
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t ≅ t' : F⟨@wk1 Γ F⟩ | VΓF | VF']) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t']⇑ | VΓF].
Proof.
  constructor; intros; erewrite 2! liftSubstComm.
  eapply validTyExt; tea; opector.
  1: now eapply wkrenSubst.
  now unshelve now eapply irrLREq, validTmExt; tea; rewrite ren_subst.
Qed.


End Properties.
