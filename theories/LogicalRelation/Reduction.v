From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Reflexivity Escape Irrelevance.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma redSubst {Γ A B l} :
  [Γ ||-<l> B] ->
  [Γ |- A ⤳* B] ->
  ∑ (RA : [Γ ||-<l> A]), [Γ ||-<l> A ≅ B | RA].
Proof.
  intros RB; revert A; pattern l, Γ, B, RB; apply LR_rect_TyUr; clear l Γ B RB; intros l Γ.
  - intros ? [] ? redA. unshelve eexists.
    + apply LRU_; econstructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [t] A ?. unshelve eexists.
    + apply LRne_; exists t; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + exists t; tea.
  - intros B [dom cod] A ? ihdom ihcod; cbn in *; unshelve eexists.
    + apply LRPi'; unshelve eexists dom cod; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + unshelve eexists dom cod; tea; cbn.
      unshelve econstructor;intros; apply reflLRTyEq.
  - intros B [red] A ?; unshelve eexists.
    + apply LRNat_; constructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [red] A ?; unshelve eexists.
    + apply LREmpty_; constructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [dom cod] A ? ihdom ihcod; cbn in *; unshelve eexists.
    + apply LRSig'; unshelve eexists dom cod; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + unshelve eexists dom cod; tea; cbn.
      unshelve econstructor;intros; apply reflLRTyEq.
  - intros ? [ty lhs rhs] ih _ X redX; unshelve eexists.
    + apply LRId'; unshelve eexists ty lhs rhs _ _; tea.
      etransitivity; tea; constructor; tea; gen_typing.
    + exists ty lhs rhs; tea; eapply reflLRTyEq.
Qed.


Lemma redwfSubst {Γ A B l} :
  [Γ ||-<l> B] ->
  [Γ |- A :⤳*: B] ->
  ∑ (RA : [Γ ||-<l> A]), [Γ ||-<l> A ≅ B | RA].
Proof.
  intros ? []; now eapply redSubst.
Qed.


Lemma redURedTm {Γ l A t u} {h : [Γ ||-U<l> A]} :
  [Γ |- t ⤳* u : A] ->
  URedTm (LogRelRec l) Γ u A h ->
  URedTm (LogRelRec l) Γ t A h.
Proof.
  intros redtu ru; pose proof (invLRConvU h).
  assert [Γ |- t : U] by (eapply ty_conv; [gen_typing| now escape]).
  destruct ru as [nf]; exists nf; tea.
  etransitivity; tea; gen_typing.
Defined.

Lemma redPiRedTm {Γ l A t u} {h : [Γ ||-Π<l> A]} :
  [Γ |- t ⤳* u : A] ->
  PiRedTm h u ->
  PiRedTm h t.
Proof.
  intros redtu ru; pose proof (invLRConvPi h).
  assert [Γ |-[ ta ] t ⤳* u : h.(outTy)] by now eapply redtm_conv.
  destruct ru as [nf]; exists nf; tea.
  constructor; destruct red; tea; now etransitivity.
Defined.

Lemma redSigRedTm {Γ l A t u} {h : [Γ ||-Σ<l> A]} :
  [Γ |- t ⤳* u : A] ->
  SigRedTm h u ->
  SigRedTm h t.
Proof.
  intros redtu ru; pose proof (invLRConvSig h).
  assert [Γ |-[ ta ] t ⤳* u : h.(outTy)] by now eapply redtm_conv.
  destruct ru as [nf]; exists nf; tea.
  constructor; destruct red; tea; now etransitivity.
Defined.

Lemma eqAppLRefl {Γ l A u v} (ΠA : [Γ ||-Π<l> A]):
  (forall Δ a b, PiRedTmEq.appRed ΠA u v Δ a b) ->
  (forall Δ a b, PiRedTmEq.appRed ΠA u u Δ a b).
Proof.
  cbn; intros eqApp; etransitivity.
  1: eapply eqApp.
  symmetry; eapply LRTmEqConv.
  2: unshelve eapply eqApp; tea; now eapply urefl.
  irrelevanceRefl; unshelve eapply (ΠA.(PolyRed.posExt) ρ h).
  now symmetry.
Qed.

Lemma redSubstLeftTmEq {Γ A t u v l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u ≅ v : A | RA] ->
  [Γ |- t ⤳* u : A ] ->
  [Γ ||-<l> t ≅ v : A | RA].
Proof.
  intros uv tu; transitivity u; [|assumption].
  revert t u v uv tu; pattern l, Γ, A, RA; apply LR_rect_TyUr; clear l Γ A RA; intros l Γ.
  - intros ? h ??? [ru] redtu ; pose proof (invLRConvU h).
    assert (redtu' : [Γ |-[ ta ] t ⤳* u]) by (eapply redty_term; gen_typing).
    destruct (redSubst (A:=t) (RedTyRecFwd h relL) redtu') as [rTyt0 ?].
    unshelve eexists (redURedTm redtu ru) ru (RedTyRecBwd h rTyt0); tea.
    1: now eapply lrefl.
    apply TyEqRecFwd; irrelevance.
  - intros ????? ru' ?; pose (ru := ru'); destruct ru' as [n].
    assert [Γ |- A ≅ neRedTy.ty neA] by now eapply invLRConvNe.
    assert [Γ |-[ ta ] t ⤳* u : neRedTy.ty neA] by (eapply redtm_conv; tea).
    assert [Γ |-[ ta ] t : neRedTy.ty neA] by (eapply ty_conv; tea; gen_typing).
    exists n n; tea.
    2: now eapply lrefl.
    etransitivity; tea; gen_typing.
  - intros ? ΠA ihdom ihcod ??? ru redtu.
    pose proof (lrefl ru); destruct ru as [ru].
    exists (redPiRedTm redtu ru) ru ; tea.
    1: cbn; now eapply lrefl.
    now eapply eqAppLRefl.
  - intros ? NA t u ? Ru red.
    inversion Ru as [?? nfL ???? [? _]%reflNatRedTmEq]; subst.
    pose proof (invLRConvNat NA).
    assert [Γ |- t :⤳*: nfL : tNat]. 1:{
      constructor. 1: gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    econstructor; tea; now eapply lrefl.
  - intros ? NA t u ? Ru red.
    inversion Ru as [?? nfL ???? [? _]%(reflEmptyRedTmEq (NA:=NA))]; subst.
    pose proof (invLRConvEmpty NA).
    assert [Γ |- t :⤳*: nfL : tEmpty]. 1:{
      constructor. 1: gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    econstructor; tea; now eapply lrefl.
  - intros ? PA ihdom ihcod ??? [ru] redtu.
    unshelve eexists (redSigRedTm redtu ru) ru _.
    all:cbn; intros; eapply lrefl; eauto.
    irrelevanceRefl; unshelve eauto; tea.
   - intros ? IA ih _ t u ? [nf ? redL ?? prop] redt.
    assert [Γ |- A ≅ IA.(IdRedTy.outTy)] by now eapply invLRConvId.
    assert [Γ |-[ ta ] t ⤳* u : IA.(IdRedTy.outTy)] by now eapply redtm_conv.
    assert [Γ |-[ ta ] t : IA.(IdRedTy.outTy)] by (eapply ty_conv; gen_typing).
    assert [Γ |-[ ta ] t :⤳*: nf : IA.(IdRedTy.outTy)].
    1: destruct redL; constructor; tea; now etransitivity.
    eexists; tea; [now eapply lrefl|].
    now eapply reflIdPropEq in prop as [].
Qed.

Lemma redSubstTmEq {Γ A A' tl tr ul ur l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> ul ≅ ur : A | RA] ->
  [Γ |- tl ⤳* ul : A ] ->
  [Γ |- tr ⤳* ur : A' ] ->
  [Γ |- A ≅ A'] ->
  [Γ ||-<l> tl ≅ tr : A | RA].
Proof.
  intros.
  assert [Γ |- tr ⤳* ur : A ].
  1: eapply redtm_conv; tea; now symmetry.
  eapply redSubstLeftTmEq; tea; symmetry.
  eapply redSubstLeftTmEq; tea; now symmetry.
Qed.

Lemma redwfSubstTmEq {Γ A t u v l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u ≅ v : A | RA] ->
  [Γ |- t :⤳*: u : A ] ->
  [Γ ||-<l> t ≅ v : A | RA].
Proof.
  intros ? []; now eapply redSubstLeftTmEq.
Qed.

Lemma redFwd {Γ l A B} : [Γ ||-<l> A] -> [Γ |- A :⤳*: B] -> whnf B -> [Γ ||-<l> B].
Proof.
  intros RA; revert B; pattern l, Γ, A, RA; apply LR_rect_TyUr; clear l Γ A RA.
  - intros ??? [??? red] ? red' ?.
    eapply LRU_.  unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor. econstructor; tea. eapply redtywf_refl; gen_typing.
  - intros ??? [? red] ? red' ?.
    eapply LRne_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [?? red] ?? ? red' ?.
    eapply LRPi'.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor.
    + eapply redtywf_refl; gen_typing.
    + eassumption.
    + eassumption.
    + eassumption.
  - intros ??? [red] ? red' ?.
    eapply LRNat_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [red] ? red' ?.
    eapply LREmpty_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [?? red] ?? ? red' ?.
    eapply LRSig'.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor.
    + eapply redtywf_refl; gen_typing.
    + eassumption.
    + eassumption.
    + eassumption.
  - intros ??? [???? red] _ _ ? red' ?.
    eapply LRId'; unshelve erewrite (redtywf_det _ _ red' red); tea; [constructor|].
    econstructor; tea. eapply redtywf_refl; gen_typing.
Qed.

Lemma redFwdConv {Γ l A B} (RA : [Γ ||-<l> A]) : [Γ |- A :⤳*: B] -> whnf B -> [Γ ||-<l> B] × [Γ ||-<l> A ≅ B | RA].
Proof.
  intros red wh. pose (RB := redFwd RA red wh).
  destruct (redwfSubst RB red).
  split; tea; irrelevance.
Qed.

Lemma redFwdURedTm {Γ l A t u} {h : [Γ ||-U<l> A]} :
  [Γ |- t :⤳*: u : A] ->
  whnf u ->
  URedTm (LogRelRec l) Γ t A h ->
  URedTm (LogRelRec l) Γ u A h.
Proof.
  intros redtu whu rt.
  destruct rt as [nf rednf]; exists nf; tea.
  unshelve erewrite (redtmwf_det _ _ redtu rednf); tea.
  1: now eapply isType_whnf.
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma redFwdPiRedTm {Γ l A t u} {h : [Γ ||-Π<l> A]} :
  [Γ |- t :⤳*: u : A] ->
  whnf u ->
  PiRedTm h t ->
  PiRedTm h u.
Proof.
  intros redtu whu rt; pose proof (PiRedTmEq.whnf rt).
  destruct rt as [nf rednf]; exists nf; tea.
  unshelve erewrite (redtmwf_det _ _ redtu rednf); tea.
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma redFwdSigRedTm {Γ l A t u} {h : [Γ ||-Σ<l> A]} :
  [Γ |- t :⤳*: u : A] ->
  whnf u ->
  SigRedTm h t ->
  SigRedTm h u.
Proof.
  intros redtu whu rt; pose proof (SigRedTmEq.whnf rt).
  destruct rt as [nf rednf]; exists nf; tea.
  unshelve erewrite (redtmwf_det _ _ redtu rednf); tea.
  eapply redtmwf_refl; gen_typing.
Defined.


Lemma IdProp_whnf {Γ l A} (IA : [Γ ||-Id<l> A]) t u : IdPropEq IA t u -> whnf t × whnf u.
Proof.
  intros []; split; constructor.
  1: destruct r; now eapply convneu_whne.
  destruct r as[?? conv]; symmetry in conv; now eapply convneu_whne.
Qed.

Lemma redTmEqFwd {Γ l A t u v} {RA : [Γ ||-<l> A]} :
  [Γ ||-<l> t ≅ v : A | RA] -> [Γ |- t :⤳*: u : A] -> whnf u -> [Γ ||-<l> u ≅ v : A | RA].
Proof.
  intros tv tu wu; transitivity t; tea.
  revert t u tv tu wu; pattern l,Γ,A,RA; apply LR_rect_TyUr; clear l Γ A RA.
  - intros ?????? [red] red' ?.
    pose proof (invLRConvU h).
    assert [Γ |- t :⤳*: u] by (eapply redtywf_term; gen_typing).
    assert (ru : [Γ ||-<h.(URedTy.level)> u]).
    1:eapply redFwd; tea; now eapply RedTyRecFwd.
    exists (redFwdURedTm red' wu red) red (RedTyRecBwd _ ru); cbn; tea.
    1: now eapply lrefl.
    eapply TyEqRecBwd.
    eapply LRTyEqSym.
    eapply redSubst in ru as []; [| now eapply tyr_wf_red ].
    irrelevance.
    Unshelve. 2: now eapply RedTyRecFwd.
  - intros ??? ??? [?? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
    now eapply lrefl.
  - intros ???????? [red] red' wu.
    pose proof (PiRedTmEq.whnf red).
    unshelve eexists (redFwdPiRedTm red' wu red) red.
    1: now eapply lrefl.
    now eapply eqAppLRefl.
  - intros ?????? Rt red' ?; inversion Rt as [???? red ?? prop] ; subst.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply fst, NatPropEq_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
    1: now eapply lrefl.
    now eapply reflNatRedTmEq in prop as [].
  - intros ?????? Rt red' ?; inversion Rt as [???? red ?? prop]; subst.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1:now eapply fst, (EmptyPropEq_whnf (NA:=NA)).
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
    1: now eapply lrefl.
    now eapply (reflEmptyRedTmEq (NA:=NA)) in prop as [].
  - intros ???????? [red] red' ?.
    pose proof (SigRedTmEq.whnf red).
    unshelve eexists (redFwdSigRedTm red' wu red) red _.
    all:cbn; intros; eapply lrefl; eauto.
    irrelevanceRefl; unshelve eauto; tea.
  - intros ???????? [?? red ?? prop] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply fst, IdPropEq_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
    1: now eapply lrefl.
    now eapply fst, reflIdPropEq.
Qed.


Lemma redTmEqNf {Γ l A t u} {RA : [Γ ||-<l> A]} :
  [Γ ||-<l> t ≅ u : A | RA] -> ∑ (v : term), [Γ |- t :⤳*: v : A] × whnf v.
Proof.
  revert t u; pattern l,Γ,A,RA; apply LR_rect_TyUr; clear l Γ A RA.
  - intros ??? h ??  [[]]; eexists; split; tea.
    2: now eapply isType_whnf.
    eapply redtmwf_conv; tea.
    destruct h; cbn in *; gen_typing.
  - intros ??? h ?? []; eexists; split; tea.
    1: eapply redtmwf_conv; tea; destruct h; timeout 2 gen_typing.
    constructor; now eapply convneu_whne.
  - intros ??? h ???? [Rt]; pose proof (PiRedTmEq.whnf Rt); destruct Rt; cbn in *.
    eexists; split; tea.
    eapply redtmwf_conv; tea; destruct h; cbn in *; timeout 2 gen_typing.
  - intros ??? h ?? [??????? []%NatPropEq_whnf]; eexists; split.
    1: eapply redtmwf_conv; tea; destruct h; cbn in *; eapply convty_exp; gen_typing.
    assumption.
  - intros ??? h ?? [??????? []%(EmptyPropEq_whnf (NA:=h))]; eexists; split.
    1: eapply redtmwf_conv; tea; destruct h; cbn in *; eapply convty_exp; gen_typing.
    assumption.
  - intros ??? h ???? [Rt]; pose proof (SigRedTmEq.whnf Rt); destruct Rt.
    eexists; split; tea; cbn in *.
    eapply redtmwf_conv; tea; destruct h; cbn in *; eapply convty_exp; gen_typing.
  - intros ??? h ???? [????? [? _]%IdPropEq_whnf]; eexists; split; tea; cbn in *.
    eapply redtmwf_conv; tea; destruct h; cbn in *; tea; unfold_id_outTy; cbn.
    eapply convty_exp; gen_typing.
  Qed.

Lemma redTmEqFwdBoth {Γ l A t t' w w'} {RA : [Γ ||-<l> A]} :
  [Γ ||-<l> t ≅ t' : A | RA] -> [Γ |- t :⤳*: w : A] -> [Γ |- t' :⤳*: w' : A] -> whnf w -> whnf w' -> [Γ ||-<l> w ≅ w' : A | RA].
Proof.
  intros; eapply redTmEqFwd; tea; symmetry; eapply redTmEqFwd; tea; now symmetry.
Qed.

End Reduction.
