From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Weakening Neutral Reflexivity NormalRed Reduction Transitivity EqRedRight Introductions.Universe.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section IdRed.
  Context `{GenericTypingProperties}.

  Lemma IdRed0 {Γ l A t u} (RA : [Γ ||-<l> A]) :
      [RA | Γ ||- t : _] ->
      [RA | Γ ||- u : _] ->
      [Γ ||-Id<l> tId A t u].
  Proof.
    intros; eapply mkIdRedTy.
    1: eapply redtywf_refl; escape; gen_typing.
    all: tea.
  Defined.

  Lemma IdRed {Γ l A t u} (RA : [Γ ||-<l> A]) :
      [RA | Γ ||- t : _] ->
      [RA | Γ ||- u : _] ->
      [Γ ||-<l> tId A t u].
  Proof. intros; apply LRId'; now eapply IdRed0. Defined.

  Lemma IdRedTy_inv {Γ l A t u} (RIA : [Γ ||-Id<l> tId A t u]) :
    [× A = RIA.(IdRedTy.ty), t = RIA.(IdRedTy.lhs) & u = RIA.(IdRedTy.rhs)].
  Proof.
    pose proof (redtywf_whnf RIA.(IdRedTy.red) whnf_tId) as e; injection e; now split.
  Qed.

  Lemma IdCongRed {Γ l A A' t t' u u'}
    (RA : [Γ ||-<l> A])
    (RIA : [Γ ||-<l> tId A t u]) :
    [Γ |- tId A' t' u'] ->
    [RA | _ ||- _ ≅ A'] ->
    [RA | _ ||- t ≅ t' : _] ->
    [RA | _ ||- u ≅ u' : _] ->
    [RIA | _ ||- _ ≅ tId A' t' u'].
  Proof.
    intros.
    enough [LRId' (invLRId RIA) | _ ||- _ ≅ tId A' t' u'] by irrelevance.
    pose proof (IdRedTy_inv (invLRId (RIA))) as [ety elhs erhs].
    econstructor.
    + now eapply redtywf_refl.
    + unfold_id_outTy; rewrite <- ety, <- elhs, <- erhs; eapply convty_Id; now escape.
    + irrelevance.
    + cbn; rewrite <- elhs; irrelevance.
    + cbn; rewrite <- erhs; irrelevance.
  Qed.

  (* Lemma IdRedU@{i j k l} {Γ l A t u}
      (RU : [LogRel@{i j k l} l | Γ ||- U])
      (RU' := invLRU RU)
      (RA : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A]) :
      [RU | Γ ||- A ≅ A' : U] ->
      [RA | Γ ||- t ≅ t': _] ->
      [RA | Γ ||- u ≅: _] ->
      [RU | Γ ||- tId A t u : U].
  Proof.
    intros RAU Rt Ru.
    enough [LRU_ RU' | _ ||- tId A t u : U] by irrelevance.
    econstructor.
    (* - eapply redtmwf_refl; escape; now eapply ty_Id. *)
    - constructor.
    - eapply convtm_Id; eapply escapeEq + eapply escapeEqTerm; now eapply reflLRTmEq + eapply reflLRTyEq.
    - eapply RedTyRecBwd. eapply IdRed; irrelevanceCum.
    Unshelve. irrelevanceCum.
  Qed. *)

  Lemma IdCongRedU@{i j k l} {Γ l A A' t t' u u'}
      (RU : [LogRel@{i j k l} l | Γ ||- U])
      (RU' := invLRU RU)
      (RA : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A]) :
    [RU | Γ ||- A : U] ->
    [RU | _ ||- A ≅ A' : U] ->
    [RA | _ ||- t ≅ t' : _] ->
    [RA | _ ||- u ≅ u' : _] ->
    [RU | _ ||- tId A t u ≅ tId A' t' u' : U].
  Proof.
    intros RAU RAAU' Rtt' Ruu'.
    enough [LRU_ RU' | _ ||- tId A t u ≅ tId A' t' u': U] by irrelevance.
    assert (hAA' : [RA | _ ||- A ≅ A']).
    1: unshelve eapply UnivEqEq; try irrelevance + irrelevanceCum0.
    escape. opector.
    1,2: eexists (tId _ _ _); [eapply redtmwf_refl; gen_typing| constructor].
    - eapply RedTyRecBwd; unshelve eapply IdRed.
      all: try eapply lrefl; irrelevanceCum.
    - pose proof (redtmwf_whnf (URedTm.red u0) whnf_tId) as <-.
      pose proof (redtmwf_whnf (URedTm.red u1) whnf_tId) as <-.
      now eapply convtm_Id.
    - eapply RedTyRecBwd; unshelve eapply IdRed.
      1: unshelve eapply UnivEq; [| |irrelevanceCum0| symmetry; irrelevanceCum].
      all: eapply urefl; eapply LRTmEqConv; tea.
    - eapply TyEqRecFwd.
      unshelve eapply LRTyEqIrrelevantCum.
      2: eapply RedTyRecFwd in l0 ; irrelevanceCum.
      unshelve eapply IdCongRed; tea; gen_typing.
  Qed.



(* Lemma reflRed {Γ l A x} (RA : [Γ ||-<l> A]) (Rx : [RA | _ ||- x : _]) (RIA : [Γ ||-<l> tId A x x]) :
  [RIA | _ ||- tRefl A x : _].
Proof.
  set (RIA' := invLRId RIA).
  enough [LRId' RIA' | _ ||- tRefl A x : _] by irrelevance.
  pose proof (IdRedTy_inv RIA') as [eA ex ex'].
  assert (e : tId (IdRedTy.ty RIA') (IdRedTy.lhs RIA') (IdRedTy.rhs RIA') = tId A x x).
  1: f_equal; now symmetry.
  econstructor; unfold_id_outTy; cbn; rewrite ?e.
  + eapply redtmwf_refl; eapply ty_refl; now escape.
  + eapply convtm_refl; [eapply escapeEq; eapply reflLRTyEq|eapply escapeEqTerm; now eapply reflLRTmEq].
  + constructor; cbn.
    1,2: now escape.
    all: irrelevance0; tea.
    1: eapply reflLRTyEq.
    * rewrite <- ex; now eapply reflLRTmEq.
    * rewrite <- ex'; now eapply reflLRTmEq.
  Unshelve.  all: tea.
Qed.

Lemma reflRed' {Γ l A x} (RA : [Γ ||-<l> A]) (Rx : [RA | _ ||- x : _])
  (RIA := IdRed RA Rx Rx): [RIA | _ ||- tRefl A x : _].
Proof. now eapply reflRed. Qed. *)

Lemma reflCongRed {Γ l A A' x x'}
  (RA : [Γ ||-<l> A])
  (RAA : [RA | _ ||- _ ≅ A'])
  (Rxx : [RA | _ ||- x ≅ x' : _])
  (RIA : [Γ ||-<l> tId A x x]) :
  [RIA | _ ||- tRefl A x ≅ tRefl A' x' : _].
Proof.
  set (RIA' := normRedId RIA).
  enough [RIA' | _ ||- tRefl A x ≅ tRefl A' x' : _] by irrelevance.
  escape.
  assert [Γ |- tId A' x' x' ≅ tId A x x] by (symmetry; timeout 1 gen_typing).
  (* assert [Γ |- tId Ar xr xr ≅ tId A x x] by (symmetry; timeout 1 gen_typing). *)
  exists (tRefl A x) (tRefl A' x').
  1,2: eapply redtmwf_refl; unfold_id_outTy; cbn.
  1: gen_typing.
  1: eapply ty_conv; [|tea]; gen_typing.
  1:  unfold_id_outTy; cbn; timeout 1 gen_typing.
  constructor; tea.
  1: eapply ty_conv; tea.
  all: try irrelevance.
  2,3: eapply lrefl; cbn; irrelevance.
  eapply reflLRTyEq.
Qed.


Lemma reflCongRed' {Γ l A Al Ar x xl xr}
  (RA : [Γ ||-<l> A])
  (RAAl : [RA | _ ||- _ ≅ Al])
  (RAAr : [RA | _ ||- _ ≅ Ar])
  (Rxxl : [RA | _ ||- x ≅ xl : _])
  (Rxxr : [RA | _ ||- x ≅ xr : _])
  (RIA : [Γ ||-<l> tId A x x]) :
  [RIA | _ ||- tRefl Al xl ≅ tRefl Ar xr : _].
Proof. etransitivity; [symmetry|]; now eapply reflCongRed. Qed.


Lemma idElimPropCongRed {Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : [Γ ||-<l> A])
  (RA' : [Γ ||-<l> A'])
  (RAA' : [RA | Γ ||- A ≅ A'])
  (Rxx' : [RA | _ ||- x ≅ x' : _])
  (RIAxx : [Γ ||-<l> tId A x x])
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P])
  (RP0' : [Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) |- P'])
  (RPP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'])
  (RP : forall {y y' e e'} (Ryy' : [RA | Γ ||- y ≅ y' : _]) {RIAxy : [Γ ||-<l> tId A x y]},
    [ RIAxy | _ ||- e ≅ e' : _] -> [Γ ||-<l> P[e .: y..]])
  (RPP' : forall y y' e e'
    (Ryy' : [RA | _ ||- y ≅ y' : _])
    (RIAxy : [Γ ||-<l> tId A x y])
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]),
    [RP Ryy' Ree' | _ ||- P[e .: y..] ≅ P'[e' .: y'..]])
  (RPeq : forall A' x' y y' e e'
    (RAA' : [RA | _ ||- _ ≅ A'])
    (Rxx' : [RA | _ ||- x ≅ x' : _])
    (Ryy' : [RA | Γ ||- y ≅ y' : _])
    (RIAxy : [Γ ||-<l> tId A x y])
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]),
    [RP Ryy' Ree' | Γ ||- P[e .: y..] ≅ P[e' .: y' ..]])
  (Rhrhr' : [RP Rxx' (reflCongRed RA RAA' Rxx' RIAxx) | _ ||- hr ≅ hr' : _])
  (Ryy' : [RA | _ ||- y ≅ y' : _])
  (RIAxy : [Γ ||-<l> tId A x y])
  (Ree' : [RIAxy | _ ||- e ≅ e' : _])
  (Pee' : IdPropEq (normRedId0 (invLRId RIAxy)) e e') :
  [RP Ryy' Ree' | _ ||- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _].
Proof.
  pose proof (RPP' _ _ _ _ Rxx' _ (reflCongRed RA RAA' Rxx' RIAxx)).
  pose proof (RPP' _ _ _ _ Ryy' _ Ree').
  destruct Pee'; cbn in *; escape.
  - eapply redSubstTmEq; cycle 1.
    + eapply redtm_idElimRefl; tea.
      transitivity x'0; [|symmetry]; tea.
    + eapply redtm_idElimRefl; tea.
      1-4: eapply ty_conv; tea.
      1: transitivity A; tea; now symmetry.
      2: eapply convtm_conv; tea; transitivity x; tea; now symmetry.
      eapply convtm_conv; tea.
      transitivity y; tea.
      transitivity x0; symmetry; tea.
      transitivity x; tea. now symmetry.
    + unshelve eapply escapeEq, RPP'; tea.
    + eapply LRTmEqConv; tea.
      irrelevanceRefl.
      eapply RPeq; tea.
      Unshelve.
      * transitivity x0; [|symmetry]; irrelevance.
      * tea.
      * now eapply reflCongRed.
  - eapply neuTermEq.
    + now eapply ty_IdElim.
    + eapply ty_conv; [|symmetry; tea].
      eapply ty_IdElim; tea.
      all: eapply ty_conv; tea.
      now eapply convty_Id.
    + eapply convneu_IdElim; tea.
      destruct r; unfold_id_outTy; now cbn in *.
Qed.





Lemma idElimCongRed {Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : [Γ ||-<l> A])
  (RA' : [Γ ||-<l> A'])
  (RAA' : [RA | Γ ||- A ≅ A'])
  (Rxx' : [RA | _ ||- x ≅ x' : _])
  (RIAxx : [Γ ||-<l> tId A x x])
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P])
  (RP0' : [Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) |- P'])
  (RPP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'])
  (RP : forall {y y' e e'} (Ryy' : [RA | Γ ||- y ≅ y' : _]) {RIAxy : [Γ ||-<l> tId A x y]},
    [ RIAxy | _ ||- e ≅ e' : _] -> [Γ ||-<l> P[e .: y..]])
  (RPP' : forall y y' e e'
    (Ryy' : [RA | _ ||- y ≅ y' : _])
    (RIAxy : [Γ ||-<l> tId A x y])
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]),
    [RP Ryy' Ree' | _ ||- P[e .: y..] ≅ P'[e' .: y'..]])
  (RPeq : forall A' x' y y' e e'
    (RAA' : [RA | _ ||- _ ≅ A'])
    (Rxx' : [RA | _ ||- x ≅ x' : _])
    (Ryy' : [RA | Γ ||- y ≅ y' : _])
    (RIAxy : [Γ ||-<l> tId A x y])
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]),
    [RP Ryy' Ree' | Γ ||- P[e .: y..] ≅ P[e' .: y' ..]])
  (Rhrhr' : [RP Rxx' (reflCongRed RA RAA' Rxx' RIAxx) | _ ||- hr ≅ hr' : _])
  (Ryy' : [RA | _ ||- y ≅ y' : _])
  (RIAxy : [Γ ||-<l> tId A x y])
  (Ree' : [RIAxy | _ ||- e ≅ e' : _]) :
  [RP Ryy' Ree' | _ ||- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _].
Proof.
  assert (nRee' : [normRedId RIAxy | Γ ||- e ≅ e' : _]) by irrelevance.
  destruct nRee' as [nfL nfR ??? prop]; unfold_id_outTy; cbn in *.
  pose proof (RPP' _ _ _ _ Rxx' _ (reflCongRed RA RAA' Rxx' RIAxx)).
  pose proof (RPP' _ _ _ _ Ryy' _ Ree').
  pose proof (IdPropEq_whnf _ _ _ prop) as [].
  assert (RenfL : [RIAxy | _ ||- e ≅ nfL : _]).
  1: symmetry; eapply redTmEqFwd; tea; now eapply lrefl.
  assert (RnfLR : [RIAxy | _ ||- nfL ≅ nfR : _])
  by (eapply redTmEqFwdBoth; cycle 1; tea).
  assert (Ryy : [RA | _ ||- y ≅ y : _]) by now eapply lrefl.
  pose proof (RAA := reflLRTyEq RA).
  pose proof (RPeq _ _ _ _ _ _ RAA Rxx' Ryy _ RenfL).
  escape.
  assert [Γ |- tId A x y ≅ tId A' x' y'] by gen_typing.
  eapply redSubstTmEq; cycle 1; tea.
  1,2: eapply redtm_idElim; tea.
  1: gen_typing.
  1-3: now eapply ty_conv.
  1: eapply redtm_conv; tea; gen_typing.
  eapply LRTmEqConv. 1: now eapply LRTyEqSym.
  now unshelve eapply idElimPropCongRed.
Qed.

End IdRed.