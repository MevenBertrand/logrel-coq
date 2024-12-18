From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral Induction.
From LogRel.Substitution Require Import Irrelevance.

Set Universe Polymorphism.

Section Properties.
Context `{GenericTypingProperties}.

Definition validTyEqLeft {Γ A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  {Δ} (wfΔ : [|- Δ]) {σ σ'}
  (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ]) :
  [validTy VA wfΔ Vσσ' | _ ||- _ ≅ B[σ]].
Proof.
  eapply LRTransEq; [eapply validTyEq| eapply validTyExt]; tea.
  Unshelve.
  (* 6: now symmetry. *)
   (* why is the instance not found here and found later in this file ? *)
  6: now eapply symmetrySubstEq. all: tea.
Qed.


Lemma wellformedSubstEq {Γ σ σ' Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ] -> [Δ |-s σ ≅ σ' : Γ].
Proof.
  revert σ σ'; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. apply conv_sempty.
  - intros * ih ?? []. apply conv_scons.
    + now eapply ih.
    + now escape.
Qed.


Lemma consSubstEq {Γ σ σ' t u l A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vtu : [Δ ||-<l> t ≅ u : A[σ] | validTy VA wfΔ Vσσ']) :
  [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ ].
Proof.
  unshelve econstructor; tea.
Qed.

Set Printing Primitive Projection Parameters.

Lemma consSubstEqvalid {Γ σ σ' t u l A Δ} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  {VA : [Γ ||-v<l> A | VΓ]}
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Δ ||-v (t[σ] .: σ) ≅  (u[σ'] .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ ].
Proof.
  unshelve econstructor; intros; tea.
  now apply validTmEq.
Qed.

Lemma wkSubstSEq {Γ} (VΓ : [||-v Γ]) :
  forall {σ σ' Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ' ≤ Δ),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' ].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply ih ; eassumption.
    + eapply LRTmEqIrrelevant'.
      2: eapply (wkTermEq _ wfΔ') ; exact hd.
      now asimpl.
Qed.


Lemma wk1SubstSEq {Γ σ σ' Δ F} (VΓ : [||-v Γ])
  (wfΔ : [|- Δ]) (wfF : [Δ |- F]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  let ρ := @wk1 Δ F in
  [Δ ,, F ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfc_cons wfΔ wfF ].
Proof.
  intro vσσ'. eapply wkSubstSEq ; eassumption.
Qed.

Lemma consWkSubstEq {Γ Δ Ξ A σ σ' a b l} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (VA : [Γ ||-v<l> A | VΓ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  (ρ : Ξ ≤ Δ) wfΞ {RA}
  (Rab : [Ξ ||-<l> a ≅ b : A[σ]⟨ρ⟩ | RA]) :
  [Ξ ||-v (a .: σ⟨ρ⟩) ≅  (b .: σ'⟨ρ⟩) : Γ ,, A | validSnoc VΓ VA | wfΞ ].
Proof.
  unshelve eapply consSubstEq.
  - unshelve eapply irrelevanceSubstEq.
    3: now eapply wkSubstSEq.
    tea.
  - irrelevance0; tea. now bsimpl.
Qed.


Lemma liftSubstEq {Γ σ σ' Δ lF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσσ')) in
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) ≅ (tRel 0 .: σ' ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros; unshelve econstructor.
  + now apply wk1SubstSEq.
  + cbn. eapply var0; unfold ρ; [now bsimpl|].
    now eapply escape, VF.
Qed.

Lemma liftSubstEq' {Γ σ σ' Δ lF F} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let ρ := wk_up F (@wk_id Γ) in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v up_term_term σ ≅ up_term_term σ' : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros.
  eapply irrelevanceSubstEq.
  unshelve eapply irrelevanceSubstEqExt.
  5: unshelve eapply liftSubstEq.
  6,8: tea.
  1-2: intros ?; now bsimpl.
Qed.


Lemma wk1ValidTy {Γ lA A lF F} {VΓ : [||-v Γ]} (VF : [Γ ||-v<lF> F | VΓ]) :
  [Γ ||-v<lA> A | VΓ] ->
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ | validSnoc VΓ VF ].
Proof.
  assert (forall σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren) ;
  intros [VA VAext]; unshelve econstructor.
  - abstract (intros * [tl _]; rewrite h; exact (VA _ wfΔ _ _ tl)).
  - intros ???? [tleq ?].
    rewrite (h σ'); unshelve eapply LRTyEqSym.
    2: eapply VA; now symmetry.
    rewrite (h σ); eapply VAext.
Qed.

Lemma wk1ValidTyEq {Γ lA A B lF F} {VΓ : [||-v Γ]} (VF : [Γ ||-v<lF> F | VΓ])
  {VA : [Γ ||-v<lA> A | VΓ]} :
  [Γ ||-v<lA> A ≅ B | VΓ | VA] ->
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ ≅ B ⟨ @wk1 Γ F ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  intros []; constructor; intros.
  rewrite h. irrelevance0.
  1: symmetry; apply h.
  unshelve intuition; tea; now eapply eqTail.
Qed.

Lemma wk1ValidTm {Γ lA t A lF F} {VΓ : [||-v Γ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  (VA : [Γ ||-v<lA> A | VΓ])
  (Vt : [Γ ||-v<lA> t : A | VΓ | VA]) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros; repeat rewrite h.
  instValid (eqTail Vσσ'); irrelevance.
Qed.

Lemma wk1ValidTmEq {Γ lA t u A lF F} {VΓ : [||-v Γ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  (VA : [Γ ||-v<lA> A | VΓ])
  (Vtu : [Γ ||-v<lA> t ≅ u : A | VΓ | VA]) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros; repeat rewrite h.
  instValid (eqTail Vσσ'); irrelevance.
Qed.


Lemma embValidTy@{u i j k l} {Γ l l' A}
    {VΓ : [VR@{i j k l}| ||-v Γ]} (h : l << l')
    (VA : typeValidity@{u i j k l} Γ VΓ l A (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ VΓ l' A (*[Γ ||-v<l'> A |VΓ]*).
Proof.
  unshelve econstructor.
  - intros ???? Vσ; destruct (validTy VA _ Vσ) as [pack]; exists pack.
    eapply LR_embedding; tea.
  - intros; now eapply validTyExt.
Defined.

Lemma embValidTyOne @{u i j k l} {Γ l A}
    {VΓ : [VR@{i j k l}| ||-v Γ]}
    (VA : typeValidity@{u i j k l} Γ VΓ l A (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ VΓ one A (*[Γ ||-v<one> A |VΓ]*).
Proof.
  destruct l; tea; now eapply (embValidTy Oi).
Defined.

Lemma soundCtxId {Γ} (VΓ : [||-v Γ]) :
  ∑ wfΓ : [|- Γ], [Γ ||-v tRel : Γ | VΓ | wfΓ].
Proof.
  enough (G : ∑ Δ (e : Δ = Γ) (wfΔ : [|-Δ]), [VΓ |Δ ||-v tRel : Γ | wfΔ]).
  1: now destruct G as [? [-> ?]].
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - exists ε, eq_refl, wfc_nil; constructor.
  - intros * [Δ [e [wfΔ Vid]]].
    exists (Δ,, A[tRel]); unshelve eexists.
    1: asimpl; now rewrite e.
    unshelve eexists.
    + apply wfc_cons; tea.
      eapply escape.
      apply (validTy VA wfΔ Vid).
    + eapply irrelevanceSubstEqExt.
      3: eapply irrelevanceSubstEq.
      3: unshelve eapply liftSubstEq; cycle 2; tea.
      all:intros []; [| bsimpl]; reflexivity.
Qed.

Definition soundCtx {Γ} (VΓ : [||-v Γ]) : [|-Γ] := (soundCtxId VΓ).π1.

Definition idSubstS {Γ} (VΓ : [||-v Γ]) : [Γ ||-v tRel : Γ | VΓ | _] := (soundCtxId VΓ).π2.

Lemma substEq_wk {Γ Δ} (ρ : Δ ≤ Γ) :
  forall (VΓ : [||-v Γ])
  (VΔ : [||-v Δ])
  {Ξ σ σ'} (wfΞ : [|- Ξ]), [VΔ | Ξ ||-v σ ≅ σ' : _ | wfΞ] -> [VΓ | Ξ ||-v ρ >> σ ≅ ρ >> σ' : _ | wfΞ].
Proof.
  destruct ρ as [? wwk]; induction wwk.
  + intros; rewrite (invValidityEmpty VΓ); constructor.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    rewrite eq in X; cbn in X; inversion X.
    eapply irrelevanceSubstEqExt.
    1: rewrite <- (scons_eta' σ); reflexivity.
    1: rewrite <- (scons_eta' σ'); reflexivity.
    cbn. asimpl.
    now eapply IHwwk.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    rewrite eq in X; cbn in X; inversion X.
    eapply irrelevanceSubstEqExt.
    1:{ rewrite <- (scons_eta' σ); cbn; unfold up_ren; rewrite scons_comp'; cbn. reflexivity. }
    1:{ rewrite <- (scons_eta' σ'); cbn; unfold up_ren; rewrite scons_comp'; cbn. reflexivity. }
    asimpl.
    pose proof (invValiditySnoc VΓ) as [? [? [? eq']]].
    rewrite eq'; unshelve econstructor.
    * now eapply IHwwk.
    * irrelevance.
Defined.

Lemma wkValidTy {l Γ Δ A} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ])
  (VΔ : [||-v Δ])
  (VA : [Γ ||-v<l> A | VΓ]) :
  [Δ ||-v<l> A⟨ρ⟩ | VΔ].
Proof.
  assert (h : forall σ, A⟨ρ⟩[σ] = A[ ρ >> σ]) by (intros; now asimpl).
  unshelve econstructor.
  - intros; rewrite h.
    eapply validTy; tea.
    now eapply substEq_wk.
  - intros; irrelevance0; rewrite h; [reflexivity|].
    unshelve eapply validTyExt.
    5: now eapply substEq_wk.
    tea.
Qed.

Lemma wkValidTm {l Γ Δ A t} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ])
  (VΔ : [||-v Δ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Δ ||-v<l> t⟨ρ⟩ : A⟨ρ⟩ | VΔ | wkValidTy ρ VΓ VΔ VA].
Proof.
  assert (hA : forall σ, A⟨ρ⟩[σ] = A[ρ >> σ]) by (intros; now asimpl).
  assert (ht : forall σ, t⟨ρ⟩[σ] = t[ρ >> σ]) by (intros; now asimpl).
  econstructor; intros; rewrite 2!ht.
  irrelevance0; [symmetry; apply hA|].
  eapply validTmExt, Vt.
  Unshelve. 1: tea. now eapply substEq_wk.
Qed.

Lemma wkValidTyEq {l Γ Δ A B} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ])
  (VΔ : [||-v Δ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VAB : [Γ ||-v<l> A ≅ B | VΓ | VA]) :
  [Δ ||-v<l> A⟨ρ⟩ ≅ B⟨ρ⟩ | VΔ | wkValidTy ρ VΓ VΔ VA].
Proof.
  assert (h : forall A σ, A⟨ρ⟩[σ] = A[ ρ >> σ]) by (intros; now asimpl).
  unshelve econstructor; intros; irrelevance0; rewrite h; [reflexivity|].
  now eapply validTyEq.
  Unshelve. 1: tea.
  now eapply substEq_wk.
Qed.

Lemma subst_rel t : t[tRel] = t.
Proof. now bsimpl. Qed.

Lemma validTyWf {Γ A l} (VΓ : [||-v Γ]) : [_ ||-v<l> A | VΓ ] -> [Γ |- A].
Proof.
  intros h; generalize (validTy h _ (idSubstS VΓ)); rewrite subst_rel.
  eapply escape.
Qed.

Lemma validWf {Γ} (VΓ: [||-v Γ]) :  [|- Γ].
Proof.
  induction Γ, VΓ using validity_rect.
  gen_typing.
  eapply wfc_cons; tea; now eapply validTyWf.
Qed.

(* Lemma compSubstS {Γ} (VΓ : [||-v Γ])  :
  forall Δ (VΔ : [||-v Δ])
    {σ σ'} (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | validWf VΔ])
    Ξ (wfΞ : [|- Ξ])
    {τ τ'} (Vττ' : [_ ||-v τ ≅ τ' : _ | VΔ | wfΞ]),
    [_ ||-v  σ >> subst_term τ ≅ σ' >> subst_term τ' : _ | VΓ | wfΞ].
Proof.
  induction Γ, VΓ using validity_rect.
  1: intros; constructor.
  intros ; unshelve econstructor.
  - eapply irrelevanceSubstEqExt.
    3:{ eapply IHVΓ; [eapply eqTail, Vσσ'|]; tea.  }
    1,2: intros ?; reflexivity.
  - cbn.  unfold funcomp. cbv. bsimpl. substify. asimpl.

  intros Δ VΔ; induction Δ, VΔ using validity_rect. unshelve econstructor. *)





End Properties.
