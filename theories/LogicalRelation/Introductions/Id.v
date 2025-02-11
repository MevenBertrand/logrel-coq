From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section IdRed.
  Context `{GenericTypingProperties}.

  Lemma IdRed0 {Γ l A A' t t' u u'} (RA : [Γ ||-<l> A ≅ A']) :
      [RA | Γ ||- t ≅ t' : _] ->
      [RA | Γ ||- u ≅ u' : _] ->
      [Γ ||-Id<l> tId A t u ≅ tId A' t' u'].
  Proof.
    intros; exists A A' t t' u u' RA; tea.
    1,2: eapply redtywf_refl; escape; gtyping.
    1: escape; gtyping.
    typeclasses eauto.
  Defined.

  Lemma IdRed {Γ l A A' t t' u u'} (RA : [Γ ||-<l> A ≅ A']) :
      [RA | Γ ||- t ≅ t' : _] ->
      [RA | Γ ||- u ≅ u' : _] ->
      [Γ ||-<l> tId A t u ≅ tId A' t' u'].
  Proof. intros; apply LRId'; now eapply IdRed0. Defined.

  (* Lemma IdRedTy_inv {Γ l A t u B} (RIA : [Γ ||-Id<l> tId A t u]) :
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
  Qed. *)

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
      (RU : [LogRel@{i j k l} l | Γ ||- U ≅ U])
      (RU' := invLRU RU)
      (RA : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A ≅ A']) :
    [RU | _ ||- A ≅ A' : U] ->
    [RA | _ ||- t ≅ t' : _] ->
    [RA | _ ||- u ≅ u' : _] ->
    [RU | _ ||- tId A t u ≅ tId A' t' u' : U].
  Proof.
    intros RAU Rtt' Ruu'.
    enough [LRU_ RU' | _ ||- tId A t u ≅ tId A' t' u': U] by now eapply irrLREq.
    escape.
    unshelve eexists {| URedTm.te := tId A t u |} {| URedTm.te := tId A' t' u' |}; cbn.
    2,4: constructor.
    1,2: eapply redtmwf_refl.
    1-3: gtyping.
    unshelve eapply redTyRecBwd, IdRed.
    1: now eapply cumLR.
    all: now eapply irrLR.
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

Lemma reflCongRed {Γ l A A0 A' B x x'}
  (RA : [Γ ||-<l> A ≅ A0])
  (wfA' : [Γ |- A'])
  (eqA : [Γ |- A ≅ A'])
  (Rxx : [RA | _ ||- x ≅ x' : _])
  (RIA : [Γ ||-<l> tId A x x ≅ B]) :
  [RIA | _ ||- tRefl A x ≅ tRefl A' x' : _].
Proof.
  set (RIA' := normRedIdl (invLRId RIA)).
  enough [LRId' RIA' | _ ||- tRefl A x ≅ tRefl A' x' : _] by now eapply irrLREq.
  escape.
  assert [Γ |- tId A' x' x' ≅ tId A x x] by (symmetry; gtyping).
  exists (tRefl A x) (tRefl A' x').
  1,2: eapply redtmwf_refl; cbn.
  1: gtyping.
  1: eapply ty_conv; [|tea]; gtyping.
  1: cbn; gtyping.
  constructor; tea.
  1: eapply ty_conv; tea.
  1: cbn; now eapply lrefl.
  all: first [now eapply irrLREq| now eapply lrefl, irrLREq].
Qed.


Lemma reflCongRed' {Γ l A Al Ar x xl xr}
  (RA : [Γ ||-<l> A])
  (wtyAl : [Γ |- Al])
  (wtyAr : [Γ |- Ar])
  (convtyAAl : [Γ |- A ≅ Al])
  (convtyAAr : [Γ |- A ≅ Ar])
  (Rxxl : [RA | _ ||- x ≅ xl : _])
  (Rxxr : [RA | _ ||- x ≅ xr : _])
  (RIA : [Γ ||-<l> tId A x x]) :
  [RIA | _ ||- tRefl Al xl ≅ tRefl Ar xr : _].
Proof. etransitivity; [symmetry|]; now eapply (reflCongRed RA), irrLR. Qed.

Lemma idElimPropCongRed {Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : [Γ ||-<l> A])
  (RA' : [Γ ||-<l> A'])
  (wtyA' := escape RA')
  (convtyAA' : [Γ |- A ≅ A' ])
  (Rxx' : [RA | _ ||- x ≅ x' : _])
  (RIAxx : [Γ ||-<l> tId A x x])
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P])
  (RP0' : [Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) |- P'])
  (RPP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'])
  (RP : forall {y y' e e'}
    (Ryy' : [RA | _ ||- y ≅ y' : _])
    {RIAxy : [Γ ||-<l> tId A x y]}
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]),
    [Γ ||-<l> P[e .: y..] ≅ P'[e' .: y'..]])
  (Rrfl := (reflCongRed RA wtyA' convtyAA' Rxx' RIAxx))
  (Rhrhr' : [RP Rxx' Rrfl | _ ||- hr ≅ hr' : _])
  (Ryy' : [RA | _ ||- y ≅ y' : _])
  (RIAxy : [Γ ||-<l> tId A x y])
  (Ree' : [RIAxy | _ ||- e ≅ e' : _])
  (Pee' : IdPropEq (normRedId RIAxy) e e') :
  [RP Ryy' Ree' | _ ||- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _].
Proof.
  pose proof (RP _ _ _ _ Rxx' _ Rrfl).
  pose proof (RP _ _ _ _ Ryy' _ Ree').
  destruct Pee'; cbn in *; escape.
  - eapply redSubstTmEq; cycle 1.
    + eapply redtm_idElimRefl; tea.
      transitivity x'0; [|symmetry]; tea.
    + eapply redtm_idElimRefl; tea.
      1-4: eapply ty_conv; tea.
      1: transitivity A; tea; now symmetry.
      2: eapply convtm_conv; [transitivity x; tea; now symmetry|tea].
      eapply convtm_conv; [transitivity y; tea|tea].
      transitivity x0; symmetry; tea.
      transitivity x; tea; now symmetry.
    + eapply irrLRConv; tea.
      etransitivity; [|symmetry]; eapply RP.
      4: now eapply lrefl.
      1,3: eapply irrLR; first [eapply e| eapply e1].
      eapply reflCongRed; tea.
      Unshelve. tea.
  - eapply reflectLR.
    + now eapply ty_IdElim.
    + eapply ty_conv; [|symmetry; tea].
      eapply ty_IdElim; tea.
      all: eapply ty_conv; tea.
      now eapply convty_Id.
    + eapply convneu_IdElim; tea.
      destruct r;  now cbn in *.
Qed.


Lemma idElimCongRed {Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : [Γ ||-<l> A])
  (RA' : [Γ ||-<l> A'])
  (wtyA' := escape RA')
  (convtyAA' : [Γ |- A ≅ A' ])
  (Rxx' : [RA | _ ||- x ≅ x' : _])
  (RIAxx : [Γ ||-<l> tId A x x])
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P])
  (RP0' : [Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) |- P'])
  (RPP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'])
  (RP : forall {y y' e e'}
    (Ryy' : [RA | _ ||- y ≅ y' : _])
    {RIAxy : [Γ ||-<l> tId A x y]}
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]),
    [Γ ||-<l> P[e .: y..] ≅ P'[e' .: y'..]])
  (Rrfl := (reflCongRed RA wtyA' convtyAA' Rxx' RIAxx))
  (Rhrhr' : [RP Rxx' Rrfl | _ ||- hr ≅ hr' : _])
  (Ryy' : [RA | _ ||- y ≅ y' : _])
  (RIAxy : [Γ ||-<l> tId A x y])
  (Ree' : [RIAxy | _ ||- e ≅ e' : _]) :
  [RP Ryy' Ree' | _ ||- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _].
Proof.
  assert (nRee' : [LRId' (normRedId RIAxy) | Γ ||- e ≅ e' : _]) by now eapply irrLREq.
  pose proof (redTmFwd' nRee') as [].
  eapply redSubstTmEq.
  + eapply irrLRConv.
    2: unshelve (eapply idElimPropCongRed; cycle 3; tea; exact (nRee'.(IdRedTmEq.prop)));
     [|tea|now eapply irrLR].
    etransitivity; [|symmetry]; eapply RP; cycle 1; [now eapply lrefl| tea..].
  + escape; eapply redtm_idElim; tea; eapply tmr_wf_red; exact (whredtmL nRee').(tmred_whnf_red).
  + escape; eapply redtm_idElim; tea.
    1,3: now eapply ty_conv.
    2: eapply redtm_conv; [eapply tmr_wf_red; exact (whredtmR nRee').(tmred_whnf_red)|].
    2: unfold IdRedTy.outTy; cbn; gtyping.
    eapply ty_conv; tea; eapply escapeEq, RP; tea.
Qed.




End IdRed.