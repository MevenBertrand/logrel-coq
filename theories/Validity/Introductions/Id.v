From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Reflexivity Irrelevance Weakening Neutral Transitivity Reduction EqRedRight NormalRed InstKripke.
From LogRel.LogicalRelation.Introductions Require Import Universe Id.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion SingleSubst Reflexivity Reduction Universe Var Poly.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Set Universe Polymorphism.

Section Id.
Context `{GenericTypingProperties}.

  Lemma IdValid {Γ l A x x' y y'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA]) :
    [_ ||-v<l> tId A x y | VΓ].
  Proof.
    pose proof (lreflValidTm _ Vx).
    pose proof (lreflValidTm _ Vy).
    unshelve econstructor; intros.
    - instValid (lrefl vσ); cbn; now eapply IdRed.
    - instValid vσσ'; eapply IdCongRed; refold; tea.
      eapply wft_Id; escape; tea; now eapply ty_conv.
  Qed.

  Lemma IdCongValid {Γ l A A' x x' y y'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vyy' : [_ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [_ ||-v<l> tId A x y | VΓ]) :
    [_ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ | VId].
  Proof.
    constructor; intros.
    instValid Vσσ'; eapply IdCongRed; refold; tea.
    escape; eapply wft_Id; tea; now eapply ty_conv.
  Qed.

  Lemma IdTmCongValid {Γ l A A' x x' y y'}
    (VΓ : [||-v Γ])
    (VU := UValid VΓ)
    (VAUeq : [_ ||-v<one> A ≅ A' : U | VΓ | VU])
    (VAU := (lreflValidTm _ VAUeq))
    (VA := univValid VΓ VU VAU)
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA]) :
    [_ ||-v<one> tId A x y ≅ tId A' x' y' : _ | VΓ | VU].
  Proof.
    constructor; intros; instValid Vσσ'.
    unshelve eapply IdCongRedU; refold; tea.
    1: now eapply univValid.
    1: now eapply lrefl.
    all: irrelevance.
  Qed.

  Lemma IdTmValid {Γ l A x y}
    (VΓ : [||-v Γ])
    (VU := UValid VΓ)
    (VAU : [_ ||-v<one> A : U | VΓ | VU])
    (VA := univValid VΓ VU VAU)
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) :
    [_ ||-v<one> tId A x y : _ | VΓ | VU].
  Proof.
    unshelve eapply IdTmCongValid; tea; irrValid.
  Qed.

  Lemma reflCongValid {Γ l A A' x x'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VId : [_ ||-v<l> tId A x x | VΓ]) :
    [_ ||-v<l> tRefl A x ≅ tRefl A' x' : _ | _ | VId].
  Proof.
    constructor; intros; instValid Vσσ'.
    escape; now unshelve eapply reflCongRed.
  Qed.

  Lemma reflValid {Γ l A x x'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (Vx : [_ ||-v<l> x ≅ x': _ | _ | VA])
    (VId : [_ ||-v<l> tId A x x | VΓ]) :
    [_ ||-v<l> tRefl A x : _ | _ | VId].
  Proof.
    eapply reflCongValid;[eapply reflValidTy| now eapply lreflValidTm].
  Qed.

  Lemma subst_scons2 (P e y : term) (σ : nat -> term) : P[e .: y..][σ] = P [e[σ] .: (y[σ] .: σ)].
  Proof. now asimpl. Qed.

  Lemma subst_upup_scons2 (P e y : term) (σ : nat -> term) : P[up_term_term (up_term_term σ)][e .: y..] = P [e .: (y .: σ)].
  Proof. now asimpl. Qed.

  (* Lemma consSubstS' {Γ σ t l A Δ}
    (VΓ : [||-v Γ])
    (VΓA : [||-v Γ ,, A])
    (wfΔ : [|- Δ])
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
    (VA : [Γ ||-v<l> A | VΓ])
    (Vt : [ Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]) :
    [Δ ||-v (t .: σ) : Γ ,, A | VΓA | wfΔ].
  Proof.
    pose proof (invValiditySnoc VΓA) as [? [? [? ->]]].
    unshelve eapply consSubstS; [ irrValid| irrelevance].
  Qed.

  Lemma consSubstSEq'' {Γ σ σ' t u l A Δ}
    (VΓ : [||-v Γ])
    (VΓA : [||-v Γ ,, A])
    (wfΔ : [|- Δ])
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
    (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
    (VA : [Γ ||-v<l> A | VΓ])
    (Vt : [Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ])
    (Vtu : [Δ ||-<l> t ≅ u : A[σ] | validTy VA wfΔ Vσ])
    (Vσt : [_ ||-v (t .: σ) : _ | VΓA | wfΔ]) :
    [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | VΓA | wfΔ | Vσt].
  Proof.
    pose proof (invValiditySnoc VΓA) as [? [? [? ->]]].
    pose proof (consSubstSEq' VΓ wfΔ Vσ Vσσ' VA Vt Vtu).
    irrValid.
  Qed.

  consSubstEq *)

  Lemma idElimMotiveCtxIdValid {Γ l A x x'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA]) :
    [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) | validSnoc VΓ VA].
  Proof.
    unshelve eapply IdValid.
    3: now eapply wk1ValidTy.
    3: now eapply wk1ValidTmEq.
    2: exact (var0Valid VΓ VA).
  Qed.

  Lemma idElimMotiveCtxIdCongValid {Γ l A A' x x'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VId : [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) | validSnoc VΓ VA]) :
    [_ ||-v<l> _ ≅ tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) | validSnoc VΓ VA | VId].
  Proof.
    assert (h : forall t, t⟨@wk1 Γ A'⟩ = t⟨@wk1 Γ A⟩) by reflexivity.
    unshelve eapply IdCongValid; rewrite ?h.
    - now eapply wk1ValidTy.
    - now eapply wk1ValidTyEq.
    - now eapply wk1ValidTmEq.
    - eapply var0Valid.
  Qed.

  Lemma idElimMotiveCtxEq {Γ l A A' x x'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]) :
    [||-v (Γ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) ≅ (Γ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0))].
  Proof.
    unshelve eapply validCtxSnoc'.
    2: unshelve eapply validCtxSnoc'; [| now eapply reflValidCtx|..]; cbn; tea.
    3: cbn; now eapply idElimMotiveCtxIdCongValid.
    cbn; now eapply idElimMotiveCtxIdValid.
  Defined.


  Lemma idElimMotiveScons2Valid {Γ l A x x' y y' e e'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    Δ (wfΔ: [ |-[ ta ] Δ]) {σ σ'} (Vσσ': [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ]) :
      [VΓext | Δ ||-v (e[σ] .: (y[σ] .: σ)) ≅ (e'[σ'] .: (y'[σ'] .: σ')) : _ | wfΔ].
  Proof.
    epose (Vσy := consSubstEqvalid Vσσ' Vy).
    unshelve epose (consSubstEq _ _ Vσy (idElimMotiveCtxIdValid VΓ VA Vx) _).
    4: irrValid.
    instValid Vσσ'; irrelevance.
  Qed.

  Lemma substIdElimMotive {Γ l A x x' P y y' e e'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (Vy : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId]) :
    [_ ||-v<l> P[e .: y ..] | VΓ].
  Proof.
    opector; intros.
    - rewrite subst_scons2; eapply validTy; tea; now eapply idElimMotiveScons2Valid.
    - irrelevance0 ; rewrite subst_scons2;[reflexivity|].
      unshelve eapply validTyExt.
      5: eapply idElimMotiveScons2Valid; cycle 1; first [now eapply lreflValidTm| tea].
      tea.
  Qed.

  Lemma up_twice_subst t a b σ :
    t[up_term_term (up_term_term σ)][a[σ] .: b[σ]..] =
    t[a .: b..][σ].
  Proof. now bsimpl. Qed.

  Lemma idElimMotive_Idsubst_eq {Γ Δ A x σ} :
    tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) = (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0))[up_term_term σ].
  Proof. now bsimpl. Qed.

  Lemma idElimMotiveScons2Red {Γ l A x x' y y' e e'}
    {VΓ : [||-v Γ]}
    {VA : [_ ||-v<l> A | VΓ]}
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    {Δ} {wfΔ : [|-Δ]}
    {σ σ'} (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ])
    {RVA : [Δ ||-<l> A[σ]]}
    (Ry : [ RVA |  _ ||- y ≅ y' : _])
    {RId : [Δ ||-<l> tId A[σ] x[σ] y]}
    (Re : [RId | _ ||- e ≅ e' : _]) :
      [VΓext | Δ ||-v (e .: (y .: σ)) ≅ (e' .: (y' .: σ')) : _ | wfΔ].
  Proof.
    pose proof (invValiditySnoc VΓext) as (?&VΓA& VIdA &->).
    pose proof (invValiditySnoc VΓA) as (?&?& ? &->).
    do 2 (unshelve eapply consSubstEq; [|irrelevance]); irrValid.
  Qed.

  Lemma IdElimValid {Γ l A A' x x' P P' hr hr' y y' e e'}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VPP' : [_ ||-v<l> P ≅ P' | VΓext | VP])
    (VIdxx := (IdValid VΓ VA Vx Vx))
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx VIdxx (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr ≅ hr' : _ | _ | VPhr ])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId])
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId Ve) :
    [_ ||-v<l> tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _ | _ | VPye].
  Proof.
    constructor; intros; cbn.
    instValid Vσσ'.
    pose proof (Vuu0 := liftSubstEq' (idElimMotiveCtxIdValid VΓ VA Vx) (liftSubstEq' VA Vσσ')).
    set (wfΔ' := wfc_cons _ _) in Vuu0.
    epose proof (Vuu := irrelevanceSubstEq _ VΓext _ wfΔ' Vuu0).
    instValid Vuu.
    irrelevance0; [now rewrite <-up_twice_subst|].
    unshelve (eapply idElimCongRed; tea); tea.
    - intros * Ry ? Re.
      epose proof (Vext := idElimMotiveScons2Red Vx VΓext Vσσ' Ry Re).
      instValid Vext; now rewrite subst_upup_scons2.
    - erewrite idElimMotive_Idsubst_eq; now eapply escape.
    - erewrite idElimMotive_Idsubst_eq.
      epose proof (VA' := ureflValidTy VAA').
      epose proof (X := liftSubstEq' VA' (urefl Vσσ')).
      epose proof (X0 :=idElimMotiveCtxIdValid _ VA' (conv _ _ VA' VAA' (ureflValidTm Vx))).
      pose proof (Vuu1 := liftSubstEq' X0 X).
      set (wfΔ'' := wfc_cons _ _) in Vuu1.
      pose proof (eqvCtx := idElimMotiveCtxEq VΓ VA VAA' Vx).
      pose proof (Vuu2 := irrelevanceSubstEq _ eqvCtx.π2.π1 _ wfΔ'' Vuu1).
      pose proof (VP' := convVTy eqvCtx (irrelevanceTy _ _ (ureflValidTy VPP'))).
      instValid Vuu2; now eapply escape.
    - erewrite idElimMotive_Idsubst_eq; now eapply escapeEq.
    - intros ???? Ry ? Re.
      epose proof (Vext := idElimMotiveScons2Red Vx VΓext Vσσ' Ry Re).
      instValid Vext; irrelevance0; now rewrite subst_upup_scons2.
    - intros ???????? Ry ? Re.
      pose proof (reflValidTy VP).
      epose proof (Vext := idElimMotiveScons2Red Vx VΓext (lrefl Vσσ') Ry Re).
      instValid Vext; irrelevance0; now rewrite subst_upup_scons2.
    - irrelevance0; tea; clear; now bsimpl.
  Qed.

  Lemma subst_subst_twice t a b σ :
    t[a .: b..][σ] = t[a[σ] .: (b[σ] .: σ)].
  Proof. now bsimpl. Qed.

  Lemma subst_refl A x σ : (tRefl A x)[σ] = tRefl A[σ] x[σ].
  Proof. reflexivity. Qed.

  Lemma IdElimReflValid {Γ l A x P hr y B z}
    (VΓ : [||-v Γ])
    (VA : [_ ||-v<l> A | VΓ])
    (Vxy : [_ ||-v<l> x ≅ y : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VIdxx := (IdValid VΓ VA Vxy Vxy))
    (Vrflx := reflValid VΓ VA Vxy _)
    (VPhr := substIdElimMotive VΓ VA Vxy VΓext VP Vxy VIdxx Vrflx)
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ])
    (VAB : [_ ||-v<l> _ ≅ B | VΓ | VA])
    (Vxz : [_ ||-v<l> x ≅ z : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (VRefl : [_ ||-v<l> tRefl B z : _ | _ | VId])
    (VPye := substIdElimMotive VΓ VA Vxy VΓext VP (ureflValidTm Vxy) VId VRefl) :
    [_ ||-v<l> tIdElim A x P hr y (tRefl B z) ≅ hr : _ | _ | VPye].
  Proof.
    eapply redSubstValid.
    + constructor; intros; cbn; rewrite <-up_twice_subst.
      pose proof (Vuu0 := liftSubstEq' (idElimMotiveCtxIdValid VΓ VA Vxy) (liftSubstEq' VA Vσσ')).
      set (wfΔ' := wfc_cons _ _) in Vuu0.
      epose proof (Vuu := irrelevanceSubstEq _ VΓext _ wfΔ' Vuu0).
      instValid (lrefl Vσσ') ; instValid Vuu ; escape.
      eapply redtm_idElimRefl; tea.
      - now erewrite idElimMotive_Idsubst_eq.
      - now rewrite <-subst_refl, up_twice_subst.
    + eapply conv; tea.
      constructor; intros.
      epose (Vr := reflCongValid _ _ VAB Vxz VIdxx).
      epose (Vext := idElimMotiveScons2Valid _ VA Vxy Vxy _ Vr VΓext _ _ Vσσ').
      instValid Vext.
      irrelevance0; now rewrite subst_subst_twice.
  Qed.

End Id.




