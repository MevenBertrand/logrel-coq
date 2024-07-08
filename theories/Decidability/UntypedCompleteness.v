(** * LogRel.Decidability.UntypedCompleteness: the inductive predicates imply the implementation answer positively. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel Require Import UntypedAlgorithmicConversion.
From LogRel Require Import Utils. (* at the end, to get the right easy tactic… *)
From LogRel.Decidability Require Import Functions UntypedFunctions Soundness UntypedSoundness Completeness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.

Import DeclarativeTypingProperties.

Section ConversionComplete.

Let PEq (t u : term) :=
  (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> graph _uconv (tm_state,t,u) ok) ×
  (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> graph _uconv (tm_state,t,u) ok).

Let PRedEq (t u : term) :=
  (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> graph _uconv (tm_red_state,t,u) ok) ×
  (forall Γ A, isType A ->
    [Γ |-[de] t : A] × [Γ |-[de] u : A] -> graph _uconv (tm_red_state,t,u) ok).

Let PNeEq (t u : term) :=
  forall Γ, well_typed Γ t × well_typed Γ u ->
  graph _uconv (ne_state,t,u) ok.

Ltac split_tm :=
  split ;
  [ intros * [Hz%type_isType Hz'%type_isType] ;
    [solve [inversion Hz ; inv_whne | inversion Hz' ; inv_whne] | ..] ; now constructor
  |..].

Lemma uconv_complete :
  UAlgoConvInductionConcl PEq PRedEq PNeEq.
Proof.
  subst PEq PRedEq PNeEq.
  unfold UAlgoConvInductionConcl.
  apply UAlgoConvInduction.

  - intros * Ht Hu []%algo_uconv_wh [Hty Htm].
    split.
    all: intros * [Hconcl []]%dup.
    all: unfold graph.
    all: simp _uconv uconv_tm ; cbn.
    all: repeat (match goal with |- orec_graph _ _ _ => patch_rec_ret ; econstructor end) ; cbn.
    1-2: now eapply wh_red_complete_whnf_ty ; eauto.
    2-3: now eapply wh_red_complete_whnf_tm ; eauto.
    * eapply typeConvRed_prem2 in Hconcl ; eauto.
      now eapply Hty.
    * assert [Γ |-[de] A] as [[? ? wh]%type_normalisation]%dup by boundary. 
      eapply termConvRed_prem3 in Hconcl ; eauto.
      1: eapply Htm ; tea.
      eapply type_isType ; tea.
      now eapply subject_reduction_raw_ty.

  - split.
    all: intros.
    all: unfold graph.
    all: simp _uconv uconv_tm_red ; cbn.
    all: econstructor.

  - intros * ? [IHA_ty IHA_tm] ? [IHB_ty IHB_tm].
    split.

    + intros ? [Hconcl]%dup.
      unfold graph.
      simp _uconv uconv_tm_red ; cbn.

      eapply typePiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
      econstructor ; [now eapply IHA_ty|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound in IHA_ty as [Hpost0%algo_conv_sound _]; tea.
      eapply typePiCongAlg_prem1 in Hpost0 ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHB_ty|..].
      now constructor.

  + intros * ? [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red ; cbn.
    eapply termGen' in Hty as (?&[->]& ->%red_ty_compl_univ_l').
    2: gen_typing.

    eapply termPiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    econstructor ; [now eapply IHA_tm|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHA_tm as [_ Hpost0%algo_conv_sound]; tea.
    eapply termPiCongAlg_prem1 in Hpost0 ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHB_tm|..].
    now constructor.

  - split.
    all: intros.
    all: unfold graph.
    all: simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    all: now constructor.

  - split.
    all: intros.
    all: unfold graph.
    all: simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    all: now constructor.

  - intros * ? [_ IH_tm].
    split_tm.
    
    intros ? T ? [[Hty] Hpre0]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    eapply termGen' in Hty as (?&[->]&->%red_ty_compl_nat_l') ; tea.
    2: gen_typing.
    eapply termSuccCongAlg_prem0 in Hpre0.
    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - split.
    all: intros.
    all: unfold graph.
    all: simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    all: now constructor.

  - intros * ? [_ IH_tm].
    split_tm.

    intros * ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    eapply LamCongUAlg_prem0 in Hconcl as (?&?&[->]); tea.
    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - intros * ? ? [_ IH_tm].
    split_tm.

    intros * ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply LamNeUAlg_prem0 in Hconcl as (?&?&[->]); tea.
    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - intros * ? ? [_ IH_tm].
    split_tm.

    intros * ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply NeLamUAlg_prem0 in Hconcl as (?&?&[->]); tea.
    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - intros * ? [IHA_ty IHA_tm] ? [IHB_ty IHB_tm].
    split.

    + intros ? [Hconcl]%dup.
      unfold graph.
      simp _uconv uconv_tm_red ; cbn.

      eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
      econstructor ; [now eapply IHA_ty|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound in IHA_ty as [Hpost0%algo_conv_sound _]; tea.
      eapply typeSigCongAlg_prem1 in Hpost0 ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHB_ty|..].
      now constructor.

  + intros * ? [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red ; cbn.
    eapply termGen' in Hty as (?&[->]&->%red_ty_compl_univ_l') ; tea.
    2: gen_typing.

    eapply termSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    econstructor ; [now eapply IHA_tm|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHA_tm as [_ Hpost0%algo_conv_sound]; tea.
    eapply termSigCongAlg_prem1 in Hpost0 ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHB_tm|..].
    now constructor.

  - intros * ? [_ IHp] ? [_ IHq].
    split_tm.
    intros * ? [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    eapply PairCongUAlg_prem0 in Hconcl as (?&?&[-> [Hpre0 []]%dup]) ; tea.
    econstructor ; [now eapply IHp|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHp as [_ Hpost0%algo_conv_sound]; tea.
    eapply PairCongUAlg_prem1 in Hpost0 ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHq|..].
    now constructor.

  - intros * ? ? [_ IHp] ? [_ IHq].
    split_tm.
    intros * ? [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply PairNeUAlg_prem0 in Hconcl as (?&?&[-> [Hpre0 []]%dup]) ; tea.
    econstructor ; [now eapply IHp|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHp as [_ Hpost0%algo_conv_sound]; tea.
    eapply PairNeUAlg_prem1 in Hpost0 ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHq|..].
    now constructor.

  - intros * ? ? [_ IHp] ? [_ IHq].
    split_tm.
    intros * ? [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply NePairUAlg_prem0 in Hconcl as (?&?&[-> [Hpre0 []]%dup]) ; tea.
    econstructor ; [now eapply IHp|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHp as [_ Hpost0%algo_conv_sound]; tea.
    eapply NePairUAlg_prem1 in Hpost0 ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHq|..].
    now constructor.

  - intros * ? [IHA_ty IHA_tm] ? [_ IHx] ? [_ IHy].
    split.
    
    + intros ? [Hconcl]%dup.
      unfold graph.
      simp _uconv uconv_tm_red build_nf_view2 ; cbn.
      eapply typeIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
      econstructor ; [now eapply IHA_ty|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound in IHA_ty as [[Hpost0]%algo_conv_sound%dup _]; tea.
      eapply typeIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
      econstructor ; [now eapply IHx|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound in IHx as [_ Hpost1%algo_conv_sound]; tea.
      eapply typeIdCongAlg_prem2 in Hpost1 as [Hpre2 []]%dup ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHy|..] ; cbn.
      now econstructor.
      
    + intros ? ?? [Hconcl [[Hty]%dup]]%dup.
      unfold graph.
      simp _uconv uconv_tm_red build_nf_view2 ; cbn.
      eapply termGen' in Hty as (?&[->]&->%red_ty_compl_univ_l') ; tea.
      2: gen_typing.
      eapply termIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
      econstructor ; [now eapply IHA_tm|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound in IHA_tm as [_ [Hpost0]%algo_conv_sound%dup]; tea.
      eapply termIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
      econstructor ; [now eapply IHx|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound in IHx as [_ Hpost1%algo_conv_sound]; tea.
      eapply termIdCongAlg_prem2 in Hpost1 as [Hpre2 []]%dup ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHy|..] ; cbn.
      now econstructor.

  - intros *.
    split_tm.
    intros.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    econstructor.
  
  - intros * []%algo_uconv_wh IH.
    split.

    + intros ? Hconcl.
      unfold graph.
      simp _uconv uconv_tm_red build_nf_view2.
      repeat (unshelve erewrite ! whne_nf_view1 ; tea ; cbn).
      eapply typeNeuConvAlg_prem2 in Hconcl ; tea.
      patch_rec_ret ; econstructor ; [now eapply IH|..] ; cbn.
      now econstructor.

    + intros ? ?? Hconcl.
      unfold graph.
      simp _uconv uconv_tm_red build_nf_view2.
      repeat (unshelve erewrite ! whne_nf_view1 ; tea ; cbn).
      eapply termNeuConvAlg_prem0 in Hconcl ; tea.
      patch_rec_ret ; econstructor ; [now eapply IH|..] ; cbn.
      now econstructor.

  - intros.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    rewrite Nat.eqb_refl ; cbn.
    now econstructor.

  - intros * ? IHm ? [_ IHt] ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    econstructor ; [now eapply IHm|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHm as [? Hpost0] ; tea.
    eapply AppCongUAlg_bridge in Hpost0 as (?&?&[? [Hpre1 []]%dup]); eauto.
    eapply neuAppCongAlg_prem1 in Hpre1 as [Hpre1 []]%dup ; eauto. 
    patch_rec_ret ; econstructor ; [now eapply IHt|..] ; cbn.
    now constructor.

  - intros * ? IH ? [IHP] ? [_ IHz] ? [_ IHs] ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    econstructor ; [now eapply IH|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IH as [? Hpost0] ; tea.
    eapply NatElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
    eapply neuNatElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
    econstructor ; [now eapply IHP|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHP as [Hpos1 _] ; tea.
    eapply algo_conv_sound in Hpos1 as [Hpos1]%dup ; eauto.
    eapply neuNatElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
    econstructor ; [now eapply IHz|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHz as [_ Hpos2] ; tea.
    eapply algo_conv_sound in Hpos2 as [Hpos2]%dup ; eauto.
    eapply neuNatElimCong_prem3 in Hpos2 as [Hpre3 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHs|..] ; cbn.
    now constructor.
    
  - intros * ? IH ? [IHP] ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    econstructor ; [now eapply IH|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IH as [? Hpost0] ; tea.
    eapply EmptyElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
    eapply neuEmptyElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHP|..] ; cbn.
    now constructor.

  - intros * ? IH ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne to_neutral_diag ; cbn.
    eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IH|..] ; cbn.
    now constructor.

  - intros * ? IH ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne to_neutral_diag ; cbn.
    eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IH|..] ; cbn.
    now constructor.

  - intros * ? IH ? [IHP] ? [_ IHe] ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne to_neutral_diag ; cbn.
    eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    econstructor ; [now eapply IH|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IH as [? Hpost0] ; tea.
    eapply IdElimCongUAlg_bridge in Hpost0 as (?&?&?&[? [Hpost0]%dup]); eauto.
    eapply neuIdElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
    econstructor ; [now eapply IHP|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound in IHP as [Hpos1 _] ; tea.
    eapply algo_conv_sound in Hpos1 as [Hpos1]%dup ; eauto.
    eapply neuIdElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHe|..] ; cbn.
    now constructor.

Qed.

End ConversionComplete.