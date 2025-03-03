From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry.
From Equations Require Import Equations.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.
Set Primitive Projections.


Section Transitivity.
  Context `{GenericTypingProperties}.

  Section TransitivityLemmas.
  Universe i j k l i' j' k' l' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record trans {Γ l1 l2 A B C}
   {RAB : [LogRel@{i j k l} l1 | Γ ||- A ≅ B]}
   {RBC : [LogRel@{i' j' k' l'} l2 | Γ ||- B ≅ C]}
  := {
    transRed : [LogRel@{i j k l} l1 | Γ ||- A ≅ C] ;
    transRedTm : forall t u v,
      [_ ||-<l1> t ≅ u : _ | RAB] ->
      [_ ||-<l2> u ≅ v : _ | RBC] ->
      [_ ||-<l1> t ≅ v : _ | transRed ]
  }.

  Arguments trans {_ _ _ _ _ _}.

  Section ConducheHelper.
    Context {Γ l1 l2 A B C}
      {RAB : [LogRel@{i j k l} l1 | Γ ||- A ≅ B]}
      {RBC : [LogRel@{i' j' k' l'} l2 | Γ ||- B ≅ C]}
      (RAC : trans RAB RBC)
      {a b} (hab : [Γ ||-<l1> a ≅ b : _ | RAC.(transRed)]).

      #[local]
      Lemma factor_right : [Γ ||-<l2> a ≅ b : _ | RBC].
      Proof.
        now eapply (symLR RBC).(symRedTm), irrLR, (symLR RAC.(transRed)).(symRedTm).
      Qed.

      #[local]
      Lemma factor_left : [Γ ||-<l1> a ≅ a : _ | RAB].
      Proof.
        eapply irrLR, RAC.(transRedTm).
        2: eapply irrLR, (symLR RAB).(symRedTm).
        all: now eapply irrLR.
      Qed.

      Definition factor : [Γ ||-<l1> a ≅ a : _ | RAB] × [Γ ||-<l2> a ≅ b : _ | RBC] :=
        (factor_left, factor_right).
  End ConducheHelper.



  Definition transPolyRed {Γ l1 l2 A1 B1 C1 A2 B2 C2}
    (PAB : PolyRed@{i j k l} Γ l1 A1 B1 A2 B2)
    (PBC : PolyRed@{i' j' k' l'} Γ l2 B1 C1 B2 C2)
    (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > B1⟨ρ⟩ ≅ C]),
      trans (PolyRed.shpRed PAB ρ h) RBC)
    (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
      (ha : [PolyRed.shpRed PAB ρ h | Δ ||- a ≅ b: _]) l2 C
      (RBC : [Δ ||-< l2 > B2[b .: ρ >> tRel] ≅ C]),
      trans (PolyRed.posRed PAB ρ h ha) RBC) :
    PolyRed@{i j k l} Γ l1 A1 C1 A2 C2.
  Proof.
    unshelve econstructor.
    - intros; unshelve eapply transRed, ihdom.
      2: eapply PBC.(PolyRed.shpRed).
      all: tea.
    - cbn; intros ????? hab.
      pose proof (factor _ hab) as [haa hab'].
      unshelve eapply transRed, ihcod.
      2: now eapply PBC.(PolyRed.posRed).
      all: tea.
  Qed.


  Context {Γ : context} {l1 l2 : TypeLevel} {A B C : term}.

  Definition transLRne (neAB : [Γ ||-ne A ≅ B]) (neBC : [Γ ||-ne B ≅ C]) :
    neRedTy.tyL neBC = neRedTy.tyR neAB ->
    trans (LRne_ l1 neAB) (LRne_ l2 neBC).
  Proof.
    unshelve econstructor.
    + apply LRne_; destruct neAB, neBC;  unshelve econstructor.
      3,4: tea.
      cbn in *; subst; now etransitivity.
    + cbn; intros ??? rtu ruv.
      pose proof (whredtm_det (whredtmR rtu) (whredtmL ruv)).
      assert [Γ |- neRedTy.tyL neBC ≅ neRedTy.tyL neAB].
      1:{ symmetry; destruct neBC, neAB; cbn in *; subst;
        eapply convty_term, convtm_convneu; tea; constructor. }
      destruct rtu, ruv; cbn in *; subst.
      econstructor; cbn; [tea|..].
      * eapply redtmwf_conv; tea.
      * etransitivity; tea; now eapply convneu_conv.
  Qed.


  Section transΠ.
    Context (ΠAB : [Γ ||-Π<l1> A ≅ B]) (ΠBC : [Γ ||-Π<l2> B ≅ C])
      (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > (ParamRedTy.domR ΠAB)⟨ρ⟩ ≅ C]),
        trans (PolyRed.shpRed ΠAB ρ h) RBC)
      (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
        (ha : [PolyRed.shpRed ΠAB ρ h | Δ ||- a ≅ b: _]) l2 C
        (RBC : [Δ ||-< l2 > (ParamRedTy.codR ΠAB) [b .: ρ >> tRel] ≅ C]),
        trans (PolyRed.posRed ΠAB ρ h ha) RBC)
      (eqdom : ParamRedTy.domL ΠBC = ParamRedTy.domR ΠAB)
      (eqcod : ParamRedTy.codL ΠBC = ParamRedTy.codR ΠAB).

    Let eqΠ : outTyL ΠBC = outTyR ΠAB.
    Proof. cbn; now rewrite eqdom, eqcod. Qed.

    Definition transΠ : [Γ ||-Π<l1> A ≅ C].
    Proof.
      destruct ΠAB, ΠBC; econstructor; tea; cbn in *; subst.
      1,2: now etransitivity.
      now eapply transPolyRed.
    Defined.

    #[local]
    Definition piRedTmLeft {t} : PiRedTm ΠAB t -> PiRedTm transΠ t.
    Proof.
      intros [?? isfun]; cbn in *; econstructor; tea.
      destruct isfun as [???? eqbody|]; constructor; tea.
      intros; unshelve eapply irrLR, eqbody; tea.
      now eapply irrLR.
    Defined.

    #[local]
    Definition piRedTmRight {t} : PiRedTm ΠBC t -> PiRedTm transΠ t.
    Proof.
      intros [?? isfun]; econstructor; cbn in *.
      1: eapply redtmwf_conv; tea; rewrite eqΠ; symmetry; eapply ParamRedTy.eq.
      destruct isfun as [???? eqbody|]; constructor; tea.
      - etransitivity; tea; cbn; rewrite eqdom; apply ParamRedTy.eqdom.
      - intros ??? ρ h hab.
        cbn in *; destruct ΠAB; cbn in *; subst; cbn.
        unshelve epose proof (factor (ihdom _ ρ h _ _ (PolyRed.shpRed ΠBC ρ h)) _) as [haa hab'].
        3: eapply irrLR, hab.
        unshelve eapply irrLR, ihcod.
        9: now unshelve eapply eqbody.
        1,2: tea.
        eapply (symLR _).(symRedTm).
        unshelve eapply irrLR, eqbody; tea.
        now eapply irrLR, (symLR _).(symRedTm).
      - eapply convneu_conv; tea; cbn; rewrite eqΠ; symmetry; apply ParamRedTy.eq.
    Defined.

    Definition transLRΠ : trans (LRPi' ΠAB) (LRPi' ΠBC).
    Proof.
      exists (LRPi' transΠ); intros ??? [? ru ? appl] [ru' ? ? appr].
      pose proof (equ := whredtm_det (whredtm ru) (whredtm ru')); cbn in equ.
      unshelve econstructor.
      - now eapply piRedTmLeft.
      - now eapply piRedTmRight.
      - cbn; etransitivity; tea.
        replace (PiRedTmEq.nf ru) with (PiRedTmEq.nf ru').
        eapply convtm_conv; tea; cbn in *; rewrite eqΠ; symmetry;apply ParamRedTy.eq.
      - intros ????? hab.
        cbn in *; destruct ΠAB; cbn in *; subst; cbn.
        unshelve epose proof (factor (ihdom _ ρ h _ _ (PolyRed.shpRed ΠBC ρ h)) _) as [haa hab'].
        3: eapply irrLR, hab.
        unshelve eapply irrLR, ihcod.
        8: eapply appl.
        3,4: tea.
        3: now eapply PolyRed.posRed.
        replace (PiRedTmEq.nf ru) with (PiRedTmEq.nf ru').
        unshelve eapply appr; tea.
    Qed.

  End transΠ.

  Section transΣ.
    Context (ΣAB : [Γ ||-Σ<l1> A ≅ B]) (ΣBC : [Γ ||-Σ<l2> B ≅ C])
      (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > (ParamRedTy.domR ΣAB)⟨ρ⟩ ≅ C]),
        trans (PolyRed.shpRed ΣAB ρ h) RBC)
      (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
        (ha : [PolyRed.shpRed ΣAB ρ h | Δ ||- a ≅ b: _]) l2 C
        (RBC : [Δ ||-< l2 > (ParamRedTy.codR ΣAB) [b .: ρ >> tRel] ≅ C]),
        trans (PolyRed.posRed ΣAB ρ h ha) RBC)
      (eqdom : ParamRedTy.domL ΣBC = ParamRedTy.domR ΣAB)
      (eqcod : ParamRedTy.codL ΣBC = ParamRedTy.codR ΣAB).

    Let eqΣ : outTyL ΣBC = outTyR ΣAB.
    Proof. cbn; now rewrite eqdom, eqcod. Qed.

    Definition transΣ : [Γ ||-Σ<l1> A ≅ C].
    Proof.
      destruct ΣAB, ΣBC; econstructor; tea; cbn in *; subst.
      1,2: now etransitivity.
      now eapply transPolyRed.
    Defined.

    #[local]
    Definition sigRedTmLeft {t} : SigRedTm ΣAB t -> SigRedTm transΣ t.
    Proof.
      intros [?? ispair]; cbn in *; econstructor; tea.
      destruct ispair as [???????? rfst rsnd|].
      2:now constructor.
      unshelve eapply PairLRPair; tea.
      - intros ; now unshelve eapply irrLR, rfst.
      - intros ; now unshelve eapply irrLR, rsnd.
    Defined.

    #[local]
    Definition sigRedTmRight {t} : SigRedTm ΣBC t -> SigRedTm transΣ t.
    Proof.
      intros [?? ispair]; econstructor; cbn in *.
      1: eapply redtmwf_conv; tea; rewrite eqΣ; symmetry; eapply ParamRedTy.eq.
      destruct ispair as [???????? rfst rsnd|].
      2: constructor; eapply convneu_conv; tea; cbn; rewrite eqΣ; symmetry; apply ParamRedTy.eq.
      unshelve eapply PairLRPair; tea.
      1,4: intros; now unshelve now eapply (symLR _).(symRedTm), irrLR, (symLR _).(symRedTm).
      1: etransitivity; tea; cbn; rewrite eqdom; apply ParamRedTy.eqdom.
      etransitivity; tea; cbn; destruct ΣAB as [???????? PAB]; cbn in *; subst.
      erewrite 2!eq_subst_scons; eapply escapeEq.
      unshelve eapply PAB.(PolyRed.posRed).
      2: unshelve eapply (symLR _).(symRedTm), irrLR, rfst.
      all: gtyping.
    Defined.

    Definition transLRΣ : trans (LRSig' ΣAB) (LRSig' ΣBC).
    Proof.
      exists (LRSig' transΣ); intros ??? [? ru ? fsttu sndtu] [ru' ? ? fstuv snduv].
      pose proof (equ := whredtm_det (whredtm ru) (whredtm ru')); cbn in equ.
      unshelve econstructor.
      - now eapply sigRedTmLeft.
      - now eapply sigRedTmRight.
      - intros.
        cbn in *; destruct ΣAB; cbn in *; subst; cbn.
        unshelve (eapply irrLR, ihdom; [eapply fsttu|]).
        5: replace (SigRedTmEq.nf ru) with (SigRedTmEq.nf ru'); now unshelve apply fstuv.
        tea.
      - cbn; etransitivity; tea.
        replace (SigRedTmEq.nf ru) with (SigRedTmEq.nf ru').
        eapply convtm_conv; tea; cbn in *; rewrite eqΣ; symmetry;apply ParamRedTy.eq.
      - intros.
        cbn in *; destruct ΣAB; cbn in *; subst; cbn.
        unshelve (eapply irrLR, ihcod; [eapply sndtu|]).
        4: replace (SigRedTmEq.nf ru) with (SigRedTmEq.nf ru'); eapply PolyRed.posRed, fstuv.
        1: tea.
        eapply (symLR _).(symRedTm), irrLR, (symLR _).(symRedTm).
        replace (SigRedTmEq.nf ru) with (SigRedTmEq.nf ru').
        eapply snduv.
        Unshelve. all: tea.
    Qed.

  End transΣ.

  Section transId.
  Context (IAB : [Γ ||-Id<l1> A ≅ B]) (IBC : [Γ ||-Id<l2> B ≅ C])
    (ihty: forall l2 C (RBC : [Γ ||-< l2 > IdRedTy.tyR IAB ≅ C]), trans (IdRedTy.tyRed IAB) RBC)
    (* (ihkr: forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > (IdRedTy.tyR IAB)⟨ρ⟩ ≅ C]),
      trans (IdRedTy.tyKripke IAB ρ wfΔ) RBC) *)
    ( eqty: IdRedTy.tyL IBC = IdRedTy.tyR IAB )
    ( eqlhs: IdRedTy.lhsL IBC = IdRedTy.lhsR IAB )
    ( eqrhs: IdRedTy.rhsL IBC = IdRedTy.rhsR IAB ).

  Arguments IdRedTy.outTy _ /.

  Let eqId : IdRedTy.outTy IBC = tId (IdRedTy.tyR IAB) (IdRedTy.lhsR IAB) (IdRedTy.rhsR IAB).
  Proof. cbn; now rewrite eqty, eqlhs, eqrhs. Qed.

  Definition transId : [Γ ||-Id<l1> A ≅ C].
  Proof.
    unshelve econstructor.
    8: exact (IdRedTy.redL IAB).
    5: exact (IdRedTy.redR IBC).
    1: eapply ihty; rewrite <- eqty; eapply IdRedTy.tyRed.
    all: destruct IAB, IBC; cbn in *; subst; tea.
    - now etransitivity.
    - now eapply ihty.
    - now eapply ihty.
    - cbn; constructor.
      + intros ?? ?%(irrLR tyRed) ; eapply (irrLR _ tyRed); now symmetry.
      + intros ??? ?%(irrLR tyRed) ?%(irrLR tyRed); eapply (irrLR _ tyRed); now etransitivity.
  Defined.

  Definition transIdPropEq {t u v} : IdPropEq IAB t u -> IdPropEq IBC u v -> IdPropEq transId t v.
  Proof.
    intros [|?? [?? conv]].
    - intros ruv; inversion ruv as [| ?? [?? whr%convneu_whne] ]; subst.
      2: inversion whr.
      constructor; cbn in *; destruct IAB as [????? rhsR], IBC ; cbn in *; subst; tea.
      2,4: now eapply irrLR.
      + etransitivity; [|tea]; now eapply escapeEq.
      + eapply ihty; [|tea]; tea.
      + unshelve eapply ihty. 1: exact rhsR. all: tea.
    - intros ruv; inversion ruv as [|?? []]; subst.
      1: symmetry in conv; eapply convneu_whne in conv; inversion conv.
      constructor; cbn in *; destruct IAB, IBC; cbn in *; subst; tea.
      constructor; tea.
      1: now eapply ty_conv.
      etransitivity; tea; now eapply convneu_conv.
  Qed.

  Definition transIdRedTmEq {t u v} : [Γ ||-Id<l1> t ≅ u : _ | IAB] -> [Γ ||-Id<l2> u ≅ v : _ | IBC] -> [Γ ||-Id<l1> t ≅ v : _ | transId].
  Proof.
    intros rtu ruv; pose proof (whredtm_det (whredtmR rtu) (whredtmL ruv)).
    destruct rtu, ruv; cbn in *; subst; econstructor.
    + tea.
    + eapply redtmwf_conv; tea; rewrite eqId; symmetry; apply IAB.(IdRedTy.eq).
    + etransitivity; tea; eapply convtm_conv; tea.
      rewrite eqId; symmetry; apply IAB.(IdRedTy.eq).
    + now eapply transIdPropEq.
  Qed.

  Definition transLRId : trans (LRId' IAB) (LRId' IBC).
  Proof. exists (LRId' transId). intros; now eapply transIdRedTmEq. Qed.

  End transId.

  End TransitivityLemmas.

  Arguments trans : clear implicits.
  Arguments trans {_ _ _ _ _ _}.

  Lemma transNatRedTmEq {Γ} :
    (forall t u, NatRedTmEq Γ t u -> forall v, NatRedTmEq Γ u v -> NatRedTmEq Γ t v) ×
    (forall t u, NatPropEq Γ t u -> forall v, NatPropEq Γ u v -> NatPropEq Γ t v).
  Proof.
    apply NatRedEqInduction.
    - intros * rL rR eq prop ih ? Ruv.
      set (Rtu := Build_NatRedTmEq _ _ rL rR eq prop).
      pose proof (equ := whredtm_det (whredtmR Rtu) (whredtmL Ruv)); cbn in equ; subst.
      depelim Ruv; cbn in *; econstructor; tea.
      + etransitivity; tea.
      + now eapply ih.
    - intros ? h; inversion h as [| | ?? [?? whz%convneu_whne]]; subst.
      1: constructor.
      inversion whz.
    - intros ??? ih ? h; inversion h as [| | ?? [?? whs%convneu_whne]]; subst.
      2: inversion whs.
      constructor; eauto.
    - intros ?? [?? conv] ? h; inversion h as [ | |??  []]; subst.
      1,2: symmetry in conv; eapply convneu_whne in conv; inversion conv.
      do 2 constructor; tea; now etransitivity.
  Qed.


  Definition transLRU@{h i j k l h' i' j' k' l' v} {l1}
    (ih : forall l', l' << l1 ->
      forall Γ l2 A B C (RAB : [Γ ||-<l'> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]),
        trans@{h i j k h' i' j' k' v} RAB RBC)
    {Γ l2 A B C}
    (h : [Γ ||-U<l1> A ≅ B]) (h' : [Γ ||-U<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} (LRU_ h) (LRU_ h').
  Proof.
    unshelve econstructor.
    + apply LRU_; destruct h, h'; now econstructor.
    + assert (eq : h.(URedTy.level) = h'.(URedTy.level)) by now destruct h.(URedTy.lt), h'.(URedTy.lt).
      cbn; intros ??? [? ru] [ru' rv]; unshelve econstructor; tea; cbn.
      * destruct rv; now econstructor.
      * cbn; etransitivity; tea.
        replace (URedTm.te ru) with (URedTm.te ru'); tea.
        refine (whredtm_det (whredtm ru') (whredtm ru)).
      * eapply redTyRecBwd; eapply ih.
        1: apply URedTy.lt.
        all: now eapply redTyRecFwd.
  Qed.

  Lemma transLR_rec@{h i j k l h' i' j' k' l' v} {l}
    (ih : forall l', l' << l ->
      forall Γ l2 A B C (RAB : [Γ ||-<l'> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]),
        trans@{h i j k h' i' j' k' v} RAB RBC)
    Γ l2 A B C (RAB : [Γ ||-<l> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    pose (i := invLREqL_whred' RAB RBC).
    revert ih l2 C RBC i; indLR RAB.
    - intros h ih ? ? ? [h']; subst; now eapply transLRU.
    - intros neAB _ ??? [neBC []]; subst; now eapply transLRne.
    - intros ΠAB ? ihdom ihcod ??? [ΠBC []]; cbn in *; subst; eapply transLRΠ; eauto.
    - intros NAB _ ??? [NBC]; subst; unshelve econstructor.
      + apply LRNat_; destruct NAB, NBC; now econstructor.
      + intros ???; cbn; intros ?; now eapply transNatRedTmEq.
    - intros EAB _ ??? [EBC]; subst; unshelve econstructor.
      + apply LREmpty_; destruct EAB, EBC; now econstructor.
      + intros ???; cbn; intros Rtu Ruv.
        pose proof (equ := whredtm_det (whredtmR Rtu) (whredtmL Ruv)); cbn in equ.
        destruct Rtu as [???? []], Ruv as [???? []] ; econstructor; tea.
        constructor; tea; subst; now etransitivity.
    - intros ΣAB ? ihdom ihcod ??? [ΣBC []]; cbn in *; subst; eapply transLRΣ; eauto.
    - intros IAB ihty ???? [IBC []]; cbn in *; subst.
      eapply transLRId; eauto.
  Qed.

  Theorem transLR0@{i j k l i' j' k' l' v}  {Γ l2 A B C} (RAB : [Γ ||-<zero> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    eapply transLR_rec; intros ? h; inversion h.
  Qed.

  Theorem transLR@{h i j k l h' i' j' k' l' v} {Γ l1 l2 A B C}
    (RAB : [Γ ||-<l1> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    destruct l1; [eapply transLR0| apply transLR_rec].
    intros ? h; inversion h; intros; eapply transLR0.
  Qed.

End Transitivity.

Instance perLRTy `{GenericTypingProperties} {Γ l} : PER (LRAdequate Γ (LogRel l)).
Proof.
  constructor.
  - intros A B RAB; exact (symLR RAB).(symRed).
  - intros A B C RAB RBC; exact (transLR RAB RBC).(transRed).
Defined.

Section Consequences.
Context `{GenericTypingProperties}.

Lemma lreflRedTm  {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ t : _ | RAB].
Proof. intros Rtu; eapply irrLR, (transLR RAB _).(transRedTm); tea; now eapply (symLR _).(symRedTm). Qed.

Lemma ureflRedTm  {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> u ≅ u : _ | RAB].
Proof. intros Rtu%((symLR _).(symRedTm)); eapply (symLR _).(symRedTm); now eapply lreflRedTm. Qed.

Lemma symRedTm' {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> u ≅ t : _ | RAB].
Proof.
  intros Rtu. eapply irrLR, (transLR RAB _).(transRedTm).
  2: now eapply (symLR _).(symRedTm).
  now eapply ureflRedTm.
Qed.

Lemma irrLRConv {Γ l A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (RA : [Γ ||-<l> A ≅ A']) (RB : [Γ ||-<l> B ≅ B']) {t u} :
  [Γ ||-<l> t ≅ u : _ | RA ] -> [Γ ||-<l> t ≅ u : _ | RB ].
Proof.
  intros Rtu%(irrLR _ RAB)%((symLR _).(symRedTm))%symRedTm'; now eapply irrLR.
Qed.

Lemma irrLRCum@{i j k l i' j' k' l' i0 j0 k0 l0} {Γ l0 l l' A A' B B'}
  (RAB : [LogRel@{i0 j0 k0 l0} l0 | Γ ||- A ≅ B])
  (RA : [LogRel@{i j k l} l | Γ ||- A ≅ A'])
  (RB : [LogRel@{i' j' k' l'} l' | Γ ||- B ≅ B']) {t u} :
  [Γ ||-<l> t ≅ u : _ | RA ] -> [Γ ||-<l'> t ≅ u : _ | RB ].
Proof.
  intros Rtu%(irrLR _ RAB)%((symLR _).(symRedTm))%symRedTm'; now eapply irrLR.
Qed.


Lemma irrLRSym {Γ l A B} (RAB : [Γ ||-<l> A ≅ B]) (RBA : [Γ ||-<l> B ≅ A]) {t u} :
  [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ u : _ | RBA].
Proof. intros; now eapply irrLRConv. Qed.

Lemma irrLREq {Γ l A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (RAB' : [Γ ||-<l> A' ≅ B']) (eqA : A = A') {t u}
  : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ u : _ | RAB'].
Proof. eapply irrLRConv; subst; now eapply lrefl. Qed.

Lemma irrLREqCum@{i j k l i' j' k' l'} {Γ l l' A A' B B'}
  (RAB : [LogRel@{i j k l} l | Γ ||- A ≅ B])
  (RAB' : [LogRel@{i' j' k' l'} l' | Γ ||- A' ≅ B'])
   (eqA : A = A') {t u}
  : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l'> t ≅ u : _ | RAB'].
Proof. eapply irrLRCum; subst; now eapply lrefl. Qed.

End Consequences.

Instance perLRTm `{GenericTypingProperties} {Γ l A B} (RAB : [Γ ||-<l> A ≅ B]) :
  PER (RAB.(LRPack.eqTm)).
Proof.
  constructor.
  - intros ?? Rtu; now eapply symRedTm'.
  - intros ??? Rtu Ruv; eapply irrLR, (transLR _ _).(transRedTm); tea.
    now eapply irrLRConv.
    Unshelve. 2: now symmetry.
Qed.

Instance iperLRTm `{GenericTypingProperties} {Γ l} :
  IPER (LRAdequate Γ (LogRel l)) (fun _ => term) (fun _ _ RA => RA.(LRPack.eqTm)).
Proof.
  constructor.
  - intros; now eapply symLR.
  - intros; now eapply transLR.
Qed.

Lemma kripkeLRlrefl `{GenericTypingProperties} {Γ l A A' B B'}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  [Δ a b] (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]) :
  [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel]].
Proof.
  etransitivity; [eauto|].
  symmetry; now eapply hB, urefl.
Qed.

Lemma kripkeLRurefl `{GenericTypingProperties} {Γ l A A' B B'}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  [Δ a b] (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]) :
  [Δ ||-<l> B'[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]].
Proof.
  eapply kripkeLRlrefl; tea; intros; symmetry; eapply hB; now symmetry.
Qed.