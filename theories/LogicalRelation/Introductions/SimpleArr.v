From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Weakening Neutral Escape Reflexivity NormalRed Reduction Transitivity.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrow.
  Context `{GenericTypingProperties}.

  Lemma shiftPolyRed {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> PolyRed Γ l A B⟨↑⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros; now eapply wk.
    - intros; bsimpl; rewrite <- rinstInst'_term; now eapply wk.
    - now escape.
    - renToWk; eapply wft_wk; gen_typing.
    - intros; irrelevance0.
      2: replace (subst_term _ _) with B⟨ρ⟩.
      2: eapply wkEq, reflLRTyEq.
      all: bsimpl; now rewrite rinstInst'_term.
      Unshelve. all: tea.
  Qed.


  Lemma ArrRedTy0 {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> [Γ ||-Π<l> arr A B].
  Proof.
    intros RA RB.
    now apply LRPiPoly0, shiftPolyRed.
  Qed.

  Lemma ArrRedTy {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> [Γ ||-<l> arr A B].
  Proof. intros; eapply LRPi'; now eapply ArrRedTy0. Qed.

  Lemma shiftPolyRedEq {Γ l A A' B B'} (RA : [Γ ||-<l> A]) (RB : [Γ ||-<l> B]) (PAB : PolyRed Γ l A B⟨↑⟩) :
    [Γ ||-<l> A ≅ A' | RA] ->
    [Γ ||-<l> B ≅ B' | RB] ->
    PolyRedEq PAB A' B'⟨↑⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros; irrelevanceRefl; now eapply wkEq.
    - intros; irrelevance0; rewrite shift_subst_scons; [reflexivity|].
      now eapply wkEq.
      Unshelve. all: tea.
  Qed.

  Lemma arrRedCong0 {Γ l A A' B B'} (RA : [Γ ||-<l> A]) (RB : [Γ ||-<l> B])
    (tyA' : [Γ |- A']) (tyB' : [Γ |- B']) (RAB : [Γ ||-Π<l> arr A B]) :
    [Γ ||-<l> A ≅ A' | RA] ->
    [Γ ||-<l> B ≅ B' | RB] ->
    [Γ ||-Π arr A B ≅ arr A' B' | normRedΠ0 RAB].
  Proof.
    intros RAA' RBB'; escape.
    unshelve econstructor; cycle 2.
    + eapply redtywf_refl; now eapply wft_simple_arr.
    + now cbn.
    + now eapply convty_simple_arr.
    + now eapply shiftPolyRedEq.
  Qed.


  Lemma arrRedCong {Γ l A A' B B'} (RA : [Γ ||-<l> A]) (RB : [Γ ||-<l> B])
    (tyA' : [Γ |- A']) (tyB' : [Γ |- B']) :
    [Γ ||-<l> A ≅ A' | RA] ->
    [Γ ||-<l> B ≅ B' | RB] ->
    [Γ ||-<l> arr A B ≅ arr A' B' | normRedΠ (ArrRedTy RA RB)].
  Proof.
    intros; now eapply arrRedCong0.
  Qed.

  Lemma arrRedCong' {Γ l A A' B B'} (RA : [Γ ||-<l> A]) (RB : [Γ ||-<l> B])
    (tyA' : [Γ |- A']) (tyB' : [Γ |- B']) (RAB : [Γ ||-<l> arr A B]) :
    [Γ ||-<l> A ≅ A' | RA] ->
    [Γ ||-<l> B ≅ B' | RB] ->
    [Γ ||-<l> arr A B ≅ arr A' B' | RAB].
  Proof.
    intros; irrelevanceRefl; now eapply arrRedCong.
  Qed.


  Lemma polyRedArrExt {Γ l A B C} : PolyRed Γ l A B -> PolyRed Γ l A C -> PolyRed Γ l A (arr B C).
  Proof.
    intros [tyA tyB RA RB RBext] [_ tyC RA' RC RCext].
    opector; tea.
    2: now eapply wft_simple_arr.
    + intros; rewrite subst_arr; refold.
      apply ArrRedTy; [eapply RB| eapply RC]; now irrelevanceRefl.
      Unshelve. all: tea.
    + intros.
      irrelevance0; rewrite subst_arr; [refold; reflexivity|]; refold.
      eapply arrRedCong.
      1,2: eapply escape; first [eapply RB| eapply RC]; symmetry; now irrelevanceRefl.
      1,2: first [eapply RBext| eapply RCext]; now irrelevanceRefl.
      Unshelve. all: now irrelevanceRefl + tea.
  Qed.

  Lemma polyRedEqArrExt {Γ l A A' B B' C C'}
    (PAB : PolyRed Γ l A B) (PAC : PolyRed Γ l A C)
    (PAB' : PolyRed Γ l A' B') (PAC' : PolyRed Γ l A' C')
    (PABC : PolyRed Γ l A (arr B C))
    (PABeq : PolyRedEq PAB A' B')
    (PACeq : PolyRedEq PAC A' C')
    : PolyRedEq PABC A' (arr B' C').
  Proof.
    constructor.
    + intros; irrelevanceRefl; now unshelve eapply (PolyRedEq.shpRed PABeq).
    + intros; irrelevance0; rewrite subst_arr; refold; [reflexivity|].
      apply arrRedCong.
      * eapply escape; unshelve eapply (PolyRed.posRed); cycle 1; tea.
        eapply LRTmEqConv ; tea; irrelevanceRefl; now unshelve eapply (PolyRedEq.shpRed PABeq).
      * eapply escape; unshelve eapply (PolyRed.posRed); cycle 1; tea.
        eapply LRTmEqConv; tea; irrelevanceRefl; now unshelve eapply (PolyRedEq.shpRed PABeq).
      * unshelve eapply (PolyRedEq.posRed PABeq); tea; now irrelevanceRefl.
      * unshelve eapply (PolyRedEq.posRed PACeq); tea; now irrelevanceRefl.
  Qed.


  (* Section SimpleAppTerm.
    Context {Γ t u F G l}
      {RF : [Γ ||-<l> F]}
      (RG : [Γ ||-<l> G])
      (hΠ := normRedΠ0 (ArrRedTy0 RF RG))
      (Rt : [Γ ||-<l> t : arr F G | LRPi' hΠ])
      (Ru : [Γ ||-<l> u : F | RF]). *)

    (* Lemma simple_app_id : [Γ ||-<l> tApp (PiRedTm.nf Rt) u : G | RG ].
    Proof.
      irrelevance0.
      2: now eapply app_id.
      now bsimpl.
      Unshelve. 1: tea.
      now bsimpl.
    Qed.

    Lemma simple_appTerm0 :
        [Γ ||-<l> tApp t u : G | RG]
        × [Γ ||-<l> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G | RG].
    Proof.
      irrelevance0.
      2: now eapply appTerm0.
      now bsimpl.
      Unshelve. 1: tea.
      now bsimpl.
    Qed.

  End SimpleAppTerm.

  Lemma simple_appTerm {Γ t u F G l}
    {RF : [Γ ||-<l> F]}
    (RG : [Γ ||-<l> G])
    (RΠ : [Γ ||-<l> arr F G])
    (Rt : [Γ ||-<l> t : arr F G | RΠ])
    (Ru : [Γ ||-<l> u : F | RF]) :
    [Γ ||-<l> tApp t u : G| RG].
  Proof.
    unshelve eapply simple_appTerm0.
    3: irrelevance.
    all: tea.
  Qed. *)


  Lemma simple_appcongTerm {Γ t t' u u' F G l}
    {RF : [Γ ||-<l> F]}
    (RG : [Γ ||-<l> G])
    (RΠ : [Γ ||-<l> arr F G])
    (Rtt' : [Γ ||-<l> t ≅ t' : _ | RΠ])
    (Ruu' : [Γ ||-<l> u ≅ u' : F | RF ]) :
      [Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    irrelevance0.
    2: eapply appcongTerm; tea.
    now bsimpl.
    Unshelve. now bsimpl.
  Qed.

  (* Lemma wkRedArr {Γ l A B f}
    (RA : [Γ ||-<l> A])
    (RB : [Γ ||-<l> B])
    {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    [Γ ||-<l> f : arr A B | ArrRedTy RA RB] ->
    [Δ ||-<l> f⟨ρ⟩ : arr A⟨ρ⟩ B⟨ρ⟩ | ArrRedTy (wk ρ wfΔ RA) (wk ρ wfΔ RB)].
  Proof.
    intro; irrelevance0.
    2: unshelve eapply wkTerm; cycle 3; tea.
    symmetry; apply wk_arr.
  Qed.

  Lemma compred {Γ l A B C f g}
    (RA : [Γ ||-<l> A])
    (RB : [Γ ||-<l> B])
    (RC : [Γ ||-<l> C]) :
    [Γ ||-<l> f : arr A B | ArrRedTy RA RB] ->
    [Γ ||-<l> g : arr B C | ArrRedTy RB RC] ->
    [Γ ||-<l> comp A g f : arr A C | ArrRedTy RA RC].
  Proof.
    intros Rf Rg.
    normRedΠin Rf; normRedΠin Rg; normRedΠ ΠAC.
    assert (h : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) RA (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]),
      [Δ ||-<l> tApp g⟨ρ⟩ (tApp f⟨ρ⟩ a) : _ | wk ρ wfΔ RC]).
    1:{
      intros; eapply simple_appTerm; [|eapply simple_appTerm; tea].
      1,2: eapply wkRedArr; irrelevance.
      Unshelve. 1: eapply wk. all: tea.
    }
    assert (heq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) RA
      (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]) (hb : [Δ ||-<l> b : A⟨ρ⟩ | RA])
      (ha : [Δ ||-<l> a ≅ b: A⟨ρ⟩ | RA]),
      [Δ ||-<l> tApp g⟨ρ⟩ (tApp f⟨ρ⟩ a) ≅ tApp g⟨ρ⟩ (tApp f⟨ρ⟩ b) : _ | wk ρ wfΔ RC]).
    1:{
      intros.
      eapply simple_appcongTerm; [| | |eapply simple_appcongTerm; tea].
      1,4: eapply reflLRTmEq; eapply wkRedArr; irrelevance.
      1,2: eapply simple_appTerm; tea; eapply wkRedArr; irrelevance.
      Unshelve. 1: eapply wk. all: tea.
    }
    escape.
    assert (beta : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) RA (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]),
      [Δ ||-<l> tApp (comp A g f)⟨ρ⟩ a : _ | wk ρ wfΔ RC] ×
      [Δ ||-<l> tApp (comp A g f)⟨ρ⟩ a ≅ tApp g⟨ρ⟩ (tApp f⟨ρ⟩ a) : _ | wk ρ wfΔ RC]).
    1:{
      intros; cbn.
      assert (eq : forall t : term, t⟨↑⟩⟨upRen_term_term ρ⟩ = t⟨ρ⟩⟨↑⟩) by (intros; now asimpl).
      do 2 rewrite eq.
      eapply redSubstTerm.
      + now eapply h.
      + eapply redtm_comp_beta.
        6: cbn in *; now escape.
        5: erewrite wk_arr; eapply ty_wk; tea.
        4: eapply typing_meta_conv.
        4: eapply ty_wk; tea.
        4: now rewrite <- wk_arr.
        1-3: now eapply wft_wk.
    }
    econstructor.
    - eapply redtmwf_refl.
      eapply ty_comp; cycle 2; tea.
    - constructor; intros; cbn.
      + apply reflLRTyEq.
      + assert (Hrw : forall t, t⟨↑⟩[a .: ρ >> tRel] = t⟨ρ⟩).
        { intros; bsimpl; symmetry; now apply rinstInst'_term. }
        do 2 rewrite Hrw; irrelevance0; [symmetry; apply Hrw|].
        unshelve eapply h; tea.
    - cbn. eapply convtm_comp; cycle 6; tea.
      erewrite <- wk1_ren_on.
      eapply escapeEqTerm.
      eapply reflLRTmEq.
      do 2 erewrite <- wk1_ren_on.
      eapply h.
      eapply var0; now bsimpl.
      { now eapply wfc_ty. }
      unshelve eapply escapeEq, reflLRTyEq; tea.
      unshelve eapply escapeEq, reflLRTyEq; tea.
      Unshelve. 1: gen_typing.
      eapply wk; tea; gen_typing.
    - intros; cbn.
      irrelevance0.
      2: unshelve eapply beta; tea.
      bsimpl; now rewrite rinstInst'_term.
    - intros; irrelevance0; cycle 1.
      1: eapply transEqTerm;[|eapply transEqTerm].
      + unshelve eapply beta; tea.
      + unshelve eapply heq; tea.
      + eapply LRTmEqSym.
        unshelve eapply beta; tea.
      + cbn; bsimpl; now rewrite rinstInst'_term.
  Qed. *)

End SimpleArrow.
