From Coq Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Id.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly Var ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Set Universe Polymorphism.

Section Id.
Context `{GenericTypingProperties}.

  Lemma IdValid {Γ Γ' l A A' x x' y y'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA]) :
    [_ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ].
  Proof.
    constructor; intros; instValid vσσ'; now eapply IdRed.
  Qed.

  Lemma IdValidU {Γ Γ' l A A' x x' y y'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VU := UValid VΓ)
    (VAU : [_ ||-v<one> A ≅ A' : U | VΓ | VU])
    (VA := univValid l VAU)
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA]) :
    [_ ||-v<one> tId A x y ≅ tId A' x' y' : _ | VΓ | VU].
  Proof.
    constructor; intros; instValid Vσσ'.
    unshelve eapply IdCongRedU; refold; tea.
    1: now eapply univValid.
    1,2: now eapply irrLR.
  Qed.

  Lemma reflValid {Γ Γ' l A A' B x x'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VId : [_ ||-v<l> tId A x x ≅ B | VΓ]) :
    [_ ||-v<l> tRefl A x ≅ tRefl A' x' : _ | _ | VId].
  Proof.
    constructor; intros; instValid Vσσ'; escape.
    now eapply reflCongRed0.
  Qed.


  Lemma subst_scons2 (P e y : term) (σ : nat -> term) : P[e .: y..][σ] = P [e[σ] .: (y[σ] .: σ)].
  Proof. now asimpl. Qed.

  Lemma subst_upup_scons2 (P e y : term) (σ : nat -> term) : P[up_term_term (up_term_term σ)][e .: y..] = P [e .: (y .: σ)].
  Proof. now asimpl. Qed.


  Lemma idElimMotiveCtxIdValid {Γ Γ' l A A' x x'}
    (VΓ : [||-v Γ ≅ Γ' ])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA]) :
    [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ≅ tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0) | validSnoc VΓ VA].
  Proof.
    unshelve eapply IdValid.
    3: eapply var0Valid.
    erewrite wk1_irr; now eapply wk1ValidTm.
  Qed.


  Definition idElimMotiveCtxEqStmt Γ Γ' A A' x x' :=
    [||-v (Γ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) ≅ (Γ',, A' ,, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0))].

  Lemma idElimMotiveCtxEq {Γ Γ' l A A' x x'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ ])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]) :
    idElimMotiveCtxEqStmt Γ Γ' A A' x x'.
  Proof.
    now eapply validSnoc, idElimMotiveCtxIdValid.
  Defined.


  Lemma idElimMotiveScons2Valid {Γ Γ' l A A' x x' y y' e e'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    Δ (wfΔ: [ |-[ ta ] Δ]) {σ σ'} (Vσσ': [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ]) :
      [VΓext | Δ ||-v (e[σ] .: (y[σ] .: σ)) ≅ (e'[σ'] .: (y'[σ'] .: σ')) : _ | wfΔ].
  Proof.
    epose (Vσy := consValidSubst Vσσ' Vy).
    unshelve epose (consSubst _ _ Vσy (idElimMotiveCtxIdValid VΓ VA Vx) _).
    4: now eapply irrelevanceSubst.
    instValid Vσσ'; eapply irrLREq; tea; now bsimpl.
  Qed.

  Lemma substIdElimMotive {Γ Γ' l A A' x x' P P' y y' e e'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    (VP : [_ ||-v<l> P ≅ P' | VΓext])
    (Vy : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId]) :
    [_ ||-v<l> P[e .: y ..] ≅ P'[e' .: y' ..] | VΓ].
  Proof.
    constructor; intros.
    rewrite 2!subst_scons2; eapply validTyExt; tea.
    now eapply idElimMotiveScons2Valid.
  Qed.

  Lemma up_twice_subst t a b σ :
    t[up_term_term (up_term_term σ)][a[σ] .: b[σ]..] =
    t[a .: b..][σ].
  Proof. now bsimpl. Qed.

  Lemma idElimMotive_Idsubst_eq {Γ Δ A x σ} :
    tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) = (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0))[up_term_term σ].
  Proof. now bsimpl. Qed.

  Lemma idElimMotiveScons2Red {Γ Γ' l A A' x x' y y' e e'}
    {VΓ : [||-v Γ ≅ Γ']}
    {VA : [_ ||-v<l> A ≅ A' | VΓ]}
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    {Δ} {wfΔ : [|-Δ]}
    {σ σ'} (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ])
    {RVA : [Δ ||-<l> A[σ] ≅ A'[σ']]}
    (Ry : [ RVA |  _ ||- y ≅ y' : _])
    {RId : [Δ ||-<l> tId A[σ] x[σ] y ≅ tId A'[σ'] x'[σ'] y']}
    (Re : [RId | _ ||- e ≅ e' : _]) :
      [VΓext | Δ ||-v (e .: (y .: σ)) ≅ (e' .: (y' .: σ')) : _ | wfΔ].
  Proof.
    pose proof (invValiditySnoc VΓext) as (?&VΓA& VIdA &->).
    pose proof (invValiditySnoc VΓA) as (?&?& ? &->).
    unshelve eapply consSubst.
    1: unshelve eapply consSubst; [now eapply irrelevanceSubst|now eapply irrLR].
    eapply irrLREqCum; tea; now bsimpl.
  Qed.

  Lemma IdElimValid {Γ Γ' l A A' x x' P P' hr hr' y y' e e'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    (VP : [_ ||-v<l> P ≅ P' | VΓext])
    (VIdxx := (IdValid VΓ VA Vx Vx))
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx VIdxx (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr ≅ hr' : _ | _ | VPhr ])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId])
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId Ve) :
    [_ ||-v<l> tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _ | _ | VPye].
  Proof.
    constructor; intros; cbn.
    instValid Vσσ'.
    pose proof (Vuu0 := liftSubst' (idElimMotiveCtxIdValid VΓ VA Vx) (liftSubst' VA Vσσ')).
    set (wfΔ' := wfc_cons _ _) in Vuu0.
    epose proof (Vuu := irrelevanceSubst _ VΓext _ wfΔ' Vuu0).
    instValid Vuu.
    eapply irrLREq; [now rewrite <-up_twice_subst|].
    (unshelve (eapply idElimCongRed; tea)); tea.
    - intros * Ry ? Re.
      epose proof (Vext := idElimMotiveScons2Red Vx VΓext Vσσ' Ry Re).
      instValid Vext; now rewrite 2!subst_upup_scons2.
    - erewrite idElimMotive_Idsubst_eq; now eapply escape.
    - erewrite idElimMotive_Idsubst_eq.
      pose (t := idElimMotiveCtxIdValid _ (symValidTy' VA) (symValidTm' Vx)).
      pose proof (Vuu1 := liftSubst' t (liftSubst' (symValidTy' VA) (symSubst _ _ _ wfΔ Vσσ'))).
      set (wfΔ'' := wfc_cons _ _) in Vuu1.
      now unshelve eapply (escape (validTyExt (symValidTy' VP) _ (irrelevanceSubst _ _ _ _ Vuu1))).
    - erewrite idElimMotive_Idsubst_eq; now eapply escapeEq.
    - eapply irrLREq; tea; clear; now bsimpl.
  Qed.

  Lemma subst_subst_twice t a b σ :
    t[a .: b..][σ] = t[a[σ] .: (b[σ] .: σ)].
  Proof. now bsimpl. Qed.

  Lemma subst_refl A x σ : (tRefl A x)[σ] = tRefl A[σ] x[σ].
  Proof. reflexivity. Qed.

  Lemma IdElimReflValid {Γ Γ' l A x P  P' hr y B z}
    (VΓ : [||-v Γ ≅ Γ' ])
    (VA : [_ ||-v<l> A ≅ B | VΓ])
    (Vxy : [_ ||-v<l> x ≅ y : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A B x y)
    (VP : [_ ||-v<l> P ≅ P' | VΓext])
    (VIdxx := (IdValid VΓ VA Vxy Vxy))
    (Vrflx := reflValid VΓ VA Vxy _)
    (VPhr := substIdElimMotive VΓ VA Vxy VΓext VP Vxy VIdxx Vrflx)
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ])
    (Vxz : [_ ||-v<l> x ≅ z : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId B y y | VΓ])
    (VRefl : [_ ||-v<l> tRefl B z : _ | _ | VId])
    (Vyy := urefl Vxy)
    (VPye := substIdElimMotive VΓ VA Vxy VΓext VP Vyy VId VRefl) :
    [_ ||-v<l> tIdElim A x P hr y (tRefl B z) ≅ hr : _ | _ | VPye].
  Proof.
    eapply redSubstValid.
    + constructor; intros; cbn; rewrite <-up_twice_subst.
      pose proof (Vuu0 := liftSubst' (idElimMotiveCtxIdValid VΓ VA Vxy) (liftSubst' VA Vσσ')).
      set (wfΔ' := wfc_cons _ _) in Vuu0.
      epose proof (Vuu := irrelevanceSubst _ VΓext _ wfΔ' Vuu0).
      instValid (lrefl Vσσ') ; instValid Vuu ; escape.
      eapply redtm_idElimRefl; tea.
      - now erewrite idElimMotive_Idsubst_eq.
      - now rewrite <-subst_refl, up_twice_subst.
    + unfold idElimMotiveCtxEqStmt in *. (* TODO: there should be something cleaner here !!! *)
      unshelve (eapply irrValidTm; [|tea]); tea.
      1: now eapply lrefl.
      eapply substIdElimMotive.
      2: eapply lrefl, irrValidTy; tea; now eapply lrefl.
      1,2: irrValid.
      eapply reflValid; irrValid.
      Unshelve. 1,3,4: irrValid.
      unfold idElimMotiveCtxEqStmt; irrValid.
  Qed.

End Id.




