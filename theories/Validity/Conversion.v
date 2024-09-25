From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
From LogRel.Validity Require Import Validity Properties Irrelevance.

Set Universe Polymorphism.

Section Conversion.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma conv {Γ t u A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : B | VΓ | VB].
Proof.
  constructor; intros; eapply LRTmEqConv.
  2: now unshelve now eapply validTmEq.
  now eapply validTyEqLeft.
Qed.

Lemma convsym {Γ t u A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t ≅ u : B | VΓ | VB]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA].
Proof.
  eapply conv; tea; now eapply symValidTyEq.
Qed.

#[deprecated(note="Use conv")]
Lemma convEq {Γ t u A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : B | VΓ | VB].
Proof. now eapply conv. Qed.


Lemma convSubstEqCtx1 {Γ Δ A B l σ σ'}
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (Vσσ': [_ ||-v σ ≅ σ' : _ | VΓA | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB | wfΔ].
Proof.
  pose proof (invValiditySnoc VΓA) as [? [? [?]]]; subst.
  pose proof (invValiditySnoc VΓB) as [? [? [?]]]; subst.
  eapply irrelevanceSubstEqExt.
  1: rewrite <- scons_eta'; reflexivity.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstEq.
  1: epose (eqTail Vσσ'); irrValid.
  eapply LRTmEqConv.
  2: irrelevanceRefl; eapply eqHead.
  eapply validTyEqLeft; [eapply ureflValidTy |]; exact VAB.
  Unshelve. 6: tea.
    3: eapply irrelevanceSubstEq; now eapply eqTail.
    tea.
Qed.

Lemma convCtx1 {Γ A B P l}
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VP : [_ ||-v<l> P | VΓA]) :
  [_ ||-v<l> P | VΓB].
Proof.
  opector; intros.
  - eapply validTy; tea; eapply convSubstEqCtx1; tea; now eapply symValidTyEq.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea.
    eapply convSubstEqCtx1; tea; now eapply symValidTyEq.
    Unshelve. all: tea; now eapply ureflValidTy.
Qed.

Lemma convEqCtx1 {Γ A B P Q l}
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VP : [_ ||-v<l> P | VΓA])
  (VPB : [_ ||-v<l> P | VΓB])
  (VPQ : [_ ||-v<l> P ≅ Q | VΓA | VP]) :
  [_ ||-v<l> P ≅ Q | VΓB | VPB].
Proof.
  constructor; intros; irrelevanceRefl.
  eapply validTyEq; tea.
  Unshelve. 1: tea.
  unshelve eapply convSubstEqCtx1; cycle 5; tea.
  1: now eapply symValidTyEq.
  now eapply ureflValidTy.
Qed.

Lemma convTmEqCtx1 {Γ A B C t u l}
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VC : [_ ||-v<l> C | VΓA])
  (VC' : [_ ||-v<l> C | VΓB])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VPtu : [_ ||-v<l> t ≅ u : _ | VΓA | VC]) :
  [_ ||-v<l> t ≅ u : _ | VΓB | VC'].
Proof.
  constructor; intros; irrelevanceRefl.
  (unshelve now eapply validTmEq); tea.
  unshelve (eapply convSubstEqCtx1; tea; now eapply symValidTyEq).
  2: now eapply ureflValidTy.
Qed.


Lemma convSubstEqCtx2 {Γ Δ A1 B1 A2 B2 l σ σ'}
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 := validSnoc VΓ VA1)
  (VΓB1 := validSnoc VΓ VB1)
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2)
  (VΓB12 := validSnoc VΓB1 VB2')
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ].
Proof.
  eapply irrelevanceSubstEqExt.
  1,2: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstEq.
  + unshelve (eapply convSubstEqCtx1; tea); tea.
    now eapply eqTail.
  + unshelve eapply LRTmEqConv; cycle 3.
    2: now eapply eqHead.
    1: eapply validTyEqLeft; [|tea]; tea.
  Unshelve. all: tea.
Qed.

Lemma convSubstEqCtx2' {Γ Δ A1 B1 A2 B2 l σ σ'}
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VΓA1 : [||-v Γ ,, A1])
  (VΓA12 : [||-v Γ ,, A1 ,, A2])
  (VΓB12 : [||-v Γ ,, B1 ,, B2])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ].
Proof.
  pose proof (ureflValidTy VAB1).
  pose proof (ureflValidTy VAB).
  eapply irrelevanceSubstEq.
  eapply convSubstEqCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.

Lemma convCtx2 {Γ A1 B1 A2 B2 P l}
  (VΓ : [||-v Γ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 := validSnoc VΓ VA1)
  (VΓB1 := validSnoc VΓ VB1)
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2)
  (VΓB12 := validSnoc VΓB1 VB2')
  (VP : [_ ||-v<l> P | VΓA12]) :
  [_ ||-v<l> P | VΓB12].
Proof.
  assert [_ ||-v<l> A2 | VΓB1] by now eapply convCtx1.
  assert [_ ||-v<l> B1 ≅ A1 | _ | VB1] by now eapply symValidTyEq.
  assert [_ ||-v<l> B2 ≅ A2 | _ | VB2'] by (eapply convEqCtx1; tea; now eapply symValidTyEq).
  opector; intros.
  - eapply validTy; tea; now eapply convSubstEqCtx2'.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea.
    eapply convSubstEqCtx2'; tea.
    Unshelve. tea.
Qed.

Lemma convCtx2' {Γ A1 A2 B1 B2 P l}
  (VΓ : [||-v Γ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 : [||-v Γ ,, A1])
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VΓA12 : [||-v Γ ,, A1 ,, A2])
  (VΓB12 : [||-v Γ ,, B1,, B2])
  (VP : [_ ||-v<l> P | VΓA12]) :
  [_ ||-v<l> P | VΓB12].
Proof.
  pose proof (ureflValidTy VAB1).
  pose proof (ureflValidTy VAB).
  eapply irrelevanceTy; eapply convCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.




Inductive validCtxEq : forall {Γ Γ'}, [||-v Γ] -> [||-v Γ'] -> Type :=
  | validCtxNil : validCtxEq validEmpty validEmpty
  | validCtxSnoc {l l' Γ Γ' A A'} (VΓ :[||-v Γ]) (VΓ' : [||-v Γ'])
    (VA : [_ ||-v<l> A| VΓ])
    (VA' : [_ ||-v<l'> A'| VΓ']) :
    validCtxEq VΓ VΓ' -> [_ ||-v<l> A ≅ A'| VΓ| VA] -> validCtxEq (validSnoc VΓ VA) (validSnoc VΓ' VA').

Import EqNotations.

Definition transpValidCtxEq {Γ1 Γ1' Γ2 Γ2'}
  {VΓ1 : [||-v Γ1]}
  {VΓ1' : [||-v Γ1']}
  {VΓ2 : [||-v Γ2]}
  {VΓ2' : [||-v Γ2']}
  (h1 : validCtxEq VΓ1 VΓ1')
  (h2 : validCtxEq VΓ2 VΓ2')
  (e : Γ1 = Γ2) (e' : Γ1' = Γ2')
  (eV : rew [fun Δ => [||-v Δ]] e in VΓ1 = VΓ2)
  (eV' : rew [fun Δ => [||-v Δ]] e' in VΓ1' = VΓ2') : Type.
Proof. subst; cbn in *; exact (h1 = h2). Defined.


Lemma invValidCtxEq {Γ Γ'} {VΓ : [||-v Γ]} {VΓ' : [||-v Γ']} (h : validCtxEq VΓ VΓ'):
  match Γ as Γ return forall Γ' (VΓ : [||-v Γ]) (VΓ' : [||-v Γ']) (h : validCtxEq VΓ VΓ'), Type with
  | nil => fun Γ' VΓ  VΓ' h =>
    ∑ (eΓ' : Γ' = ε),
      transpValidCtxEq h validCtxNil eq_refl eΓ' (invValidityEmpty _) (invValidityEmpty _)
  | (A :: Γ)%list => fun ΓA' VΓA  VΓA' h =>
    let '(l;VΓ; VA;eVΓA) := invValiditySnoc VΓA in
    ∑ l' A' Γ' (eΓ' : ΓA' = (A' :: Γ')%list)
      (VΓ' : [||-v Γ'])
      (VA' : [_ ||-v<l'> A'| VΓ'])
      (VΓΓ' : validCtxEq VΓ VΓ')
      (VAA' : [_ ||-v<l> A ≅ A'| VΓ| VA])
      (eVΓA' : rew [fun Δ => [||-v Δ]] eΓ' in VΓA' = validSnoc VΓ' VA'),
      transpValidCtxEq h (validCtxSnoc VΓ VΓ' VA VA' VΓΓ' VAA') eq_refl eΓ' eVΓA eVΓA'
  end Γ' VΓ  VΓ' h.
Proof.
  induction h.
  + exists eq_refl; reflexivity.
  + unshelve eexists _,_, _, eq_refl, _, _, _, _, eq_refl; tea.
    reflexivity.
Defined.


Notation "[||-v Γ ≅ Γ' ]" := (∑ VΓ VΓ', @validCtxEq Γ Γ' VΓ VΓ').

Lemma reflValidCtxEq {Γ} (VΓ : [||-v Γ]) : validCtxEq VΓ VΓ.
Proof.
  induction Γ, VΓ using validity_rect; constructor; tea.
  now eapply reflValidTy.
Qed.

Lemma convSubsS [Γ Γ'] [VΓ : [||-v Γ]] [VΓ' : [||-v Γ']] : validCtxEq VΓ VΓ' ->
  forall {Δ} (wfΔ : [|-Δ]) {σ σ'},
  [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ ] -> [_ ||-v σ ≅ σ' : _ | VΓ' | wfΔ ].
Proof.
  intros h; induction h.
  1: constructor.
  intros ???? Vσ.
  exists (IHh _ _ _ _ (eqTail Vσ)).
  eapply LRTmEqConv. 2: exact (eqHead Vσ).
  instValid (lrefl (eqTail Vσ)); irrelevance.
Qed.

(* If needed there is a much easier proof using convSubstS and idSubstS *)
(* Lemma convValidCtxEqIdSubst {Γ Γ'} (VΓ : [||-v Γ]) (VΓ' : [||-v Γ']) : validCtxEq VΓ VΓ' ->
  [_ ||-v tRel : _ | VΓ | validWf VΓ'].
Proof.
  intros h; induction h; unshelve econstructor.
  - eapply irrelevanceSubstEqExt.
    3: eapply (wkSubstSEq _ _ _ (wk1 A') IHh).
    all: intros a; cbn -[wk1]; now rewrite (wk1_ren a).
  - eapply var0conv. 2: now eapply validTyWf.
    replace A[↑ >> tRel] with A⟨↑⟩ by (bsimpl; now substify).
    erewrite <-2!wk1_ren_on; symmetry; unshelve eapply escapeEq, wkEq; tea.
    1: now eapply validWf, validSnoc.
    1: generalize (validTy VA _ IHh); now rewrite subst_rel.
    rewrite <-(subst_rel A'); irrelevance0; [apply subst_rel|].
    eapply (validTyEq t _ IHh).
Qed. *)

Lemma convValidTy [Γ Γ'] [VΓ : [||-v Γ]] [VΓ' : [||-v Γ']] : validCtxEq VΓ VΓ' ->
  forall [l A], [_ ||-v<l> A | VΓ'] -> [_ ||-v<l> A | VΓ].
Proof.
  intros h l A VA; unshelve econstructor; intros ???? Vσ.
  all: instValid (convSubsS h wfΔ Vσ); tea ; irrelevance.
Qed.

Lemma convValidTyEq [Γ Γ'] [VΓ : [||-v Γ]] [VΓ' : [||-v Γ']] : validCtxEq VΓ VΓ' ->
  forall [l A A'] (VAΓ : [_ ||-v<l> A | VΓ]) (VAΓ' : [_ ||-v<l> A | VΓ']),
  [_ ||-v<l> A ≅ A' | VΓ' | VAΓ'] -> [_ ||-v<l> A ≅ A' | VΓ | VAΓ].
Proof.
  intros * h ** ; unshelve econstructor; intros ???? Vσ.
  instValid (convSubsS h wfΔ Vσ); irrelevance.
Qed.

Lemma convValidTyEq' [Γ Γ'] [VΓ : [||-v Γ]] [VΓ' : [||-v Γ']] (h : validCtxEq VΓ VΓ') :
  forall [l A A'] (VAΓ' : [_ ||-v<l> A | VΓ']),
  [_ ||-v<l> A ≅ A' | VΓ' | VAΓ'] -> [_ ||-v<l> A ≅ A' | VΓ | convValidTy h VAΓ'].
Proof. intros; now eapply convValidTyEq. Qed.

Lemma convValidTmEq {Γ Γ'} (VΓ : [||-v Γ]) (VΓ' : [||-v Γ']) : validCtxEq VΓ VΓ' ->
  forall l A t u (VAΓ : [_ ||-v<l> A | VΓ]) (VAΓ' : [_ ||-v<l> A | VΓ']),
  [_ ||-v<l> t ≅ u : _ | VΓ' | VAΓ'] -> [_ ||-v<l> t ≅ u  : _ | VΓ | VAΓ].
Proof.
  intros * h ** ; unshelve econstructor; intros ???? Vσ.
  instValid (convSubsS h wfΔ Vσ); irrelevance.
Qed.

Lemma convValidTmEq' [Γ Γ'] [VΓ : [||-v Γ]] [VΓ' : [||-v Γ']] (h : validCtxEq VΓ VΓ') :
  forall [l A t u] (VAΓ' : [_ ||-v<l> A | VΓ']),
  [_ ||-v<l> t ≅ u : _ | VΓ' | VAΓ'] -> [_ ||-v<l> t ≅ u  : _ | VΓ | convValidTy h VAΓ'].
Proof. intros; now eapply convValidTmEq. Qed.

Lemma symValidCtxEq [Γ Δ] [VΓ : [||-v Γ]] [VΔ : [||-v Δ]] : validCtxEq VΓ VΔ -> validCtxEq VΔ VΓ.
Proof.
  intros h; induction h; constructor; tea.
  eapply symValidTyEq.
  now unshelve now eapply convValidTyEq'.
Qed.

Lemma transValidCtxEq [Γ Δ Ξ] [VΓ : [||-v Γ]] [VΔ : [||-v Δ]] [VΞ : [||-v Ξ]] :
  validCtxEq VΓ VΔ -> validCtxEq VΔ VΞ -> validCtxEq VΓ VΞ.
Proof.
  intros h; induction h in Ξ, VΞ |- *; intros h'; pose proof (h'' := invValidCtxEq h'); cbn in h''.
  - destruct h'' as []; subst; rewrite (invValidityEmpty VΞ); constructor.
  - destruct h'' as (l''&A''&Γ''&?&?&?&?&?&?&?); do 3 (subst; cbn in *); econstructor.
    + now eapply IHh.
    + eapply transValidTyEq; tea.
      now eapply convValidTyEq.
      Unshelve. now eapply convValidTy.
Qed.

Lemma irrValidCtxEq [Γ Δ] [VΓ1 VΓ2 : [||-v Γ]] [VΔ1 VΔ2 : [||-v Δ]] : validCtxEq VΓ1 VΔ1 -> validCtxEq VΓ2 VΔ2.
Proof.
  intros h; induction h.
  - rewrite (invValidityEmpty VΓ2), (invValidityEmpty VΔ2); constructor.
  - pose proof (invValiditySnoc VΓ2) as (l1&VΓ1&?&->).
    pose proof (invValiditySnoc VΔ2) as (l2&VΓ1'&?&->).
    econstructor. 1: now eapply IHh. irrValid.
Qed.

Lemma reflValidCtx {Γ} : [||-v Γ] -> [||-v Γ ≅ Γ].
Proof.
  intros VΓ; exists VΓ, VΓ; apply reflValidCtxEq.
Defined.

Lemma symValidCtx [Γ Δ] : [||-v Γ ≅ Δ] -> [||-v Δ ≅ Γ].
Proof.
  intros (?&?&?); eexists _, _; now eapply symValidCtxEq.
Defined.

Lemma transValidCtx [Γ Δ Ξ] : [||-v Γ ≅ Δ] -> [||-v Δ ≅ Ξ] -> [||-v Γ ≅ Ξ].
Proof.
  intros (VΓ&VΔ&?) (?&?& h); eexists VΓ, _; eapply transValidCtxEq; tea.
  eapply irrValidCtxEq, h.
  Unshelve. tea.
Qed.

Lemma validCtxSnoc' [l Γ Γ' A A'] (VΓΓ' :[||-v Γ ≅ Γ']) (VA : [_ ||-v<l> A| VΓΓ'.π1]) :
  [_ ||-v<l> A ≅ A'| _ | VA] -> [||-v Γ,,A ≅ Γ',,A'].
Proof.
  intros VAA'; destruct VΓΓ' as (VΓ& VΓ'& VΓΓ').
  unshelve eexists (validSnoc _ VA), (validSnoc (l:=l) VΓ' _).
  1: eapply convValidTy; [now eapply symValidCtxEq| exact (ureflValidTy VAA')].
  econstructor; cbn; tea.
Defined.

Lemma convVTy [Γ Γ' l A] (Veq : [||-v Γ ≅ Γ']) :
  [_ ||-v<l> A | Veq.π1] -> [_ ||-v<l> A | Veq.π2.π1].
Proof. apply convValidTy, symValidCtxEq, Veq.π2.π2. Qed.

Lemma convVTyEq [Γ Γ' l A B] (Veq : [||-v Γ ≅ Γ']) (VA : [_ ||-v<l> A | Veq.π1]) :
  [_ ||-v<l> A ≅ B | Veq.π1 | VA ] -> [_ ||-v<l> A ≅ B | Veq.π2.π1 | convVTy Veq VA].
Proof. apply convValidTyEq, symValidCtxEq, Veq.π2.π2. Qed.

Lemma convVTmEq [Γ Γ' l A t u] (Veq : [||-v Γ ≅ Γ']) (VA : [_ ||-v<l> A | Veq.π1]) :
  [_ ||-v<l> t ≅ u : _ | Veq.π1 | VA ] -> [_ ||-v<l> t ≅ u : _ | Veq.π2.π1 | convVTy Veq VA].
Proof. apply convValidTmEq, symValidCtxEq, Veq.π2.π2. Qed.


End Conversion.

Notation "[||-v Γ ≅ Γ' ]" := (∑ VΓ VΓ', validCtxEq (Γ:=Γ) (Γ':=Γ') VΓ VΓ').
