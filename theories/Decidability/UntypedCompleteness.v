(** * LogRel.Decidability.UntypedCompleteness: the inductive predicates imply the implementation answer positively. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel Require Import Utils Syntax.All DeclarativeTyping GenericTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences TypeConstructorsInj NeutralConvProperties.
From LogRel.Algorithmic Require Import BundledAlgorithmicTyping AlgorithmicConvProperties AlgorithmicTypingProperties UntypedAlgorithmicConversion.
From LogRel.Decidability Require Import Functions UntypedFunctions Soundness UntypedSoundness Completeness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.

Import DeclarativeTypingProperties AlgorithmicTypedConvData.

Section ConversionComplete.
  Context
    `{!TypingSubst de}
    `{!TypeConstructorsInj de}.

Let PEq (t u : term) :=
  (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> graph _uconv (tm_state,t,u) ok) ×
  (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> graph _uconv (tm_state,t,u) ok).

Let PRedEq (t u : term) :=
  (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> graph _uconv (tm_red_state,t,u) ok) ×
  (forall Γ A,
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
    * eapply termConvRed_prem3 in Hconcl ; eauto.
      2: reflexivity.
      now eapply Htm.

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
      eapply implem_uconv_graph, uconv_sound_decl in IHA_ty as [Hpost0 _]; tea.
      eapply typePiCongAlg_prem1 in Hpost0 ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHB_ty|..].
      now constructor.

  + intros * [(?&[->]& _)%termGen' (?&[->]& _)%termGen'].
    unfold graph.
    simp _uconv uconv_tm_red ; cbn.

    assert ([Γ |-[ de ] tProd A B : U] × [Γ |-[ de ] tProd A' B' : U]) as
      [[Hpre0 []]%termPiCongAlg_prem0%dup]%dup.
    {
      split ; now econstructor.
    }

    econstructor ; [now eapply IHA_tm|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IHA_tm as [_ Hpost0]; tea.
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
    
    intros * [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.

    assert ([Γ |-[ de ] tSucc t : tNat] × [Γ |-[ de ] tSucc t' : tNat]) as ?%termSuccCongAlg_prem0.
    {
      split ; now econstructor.
    }

    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - split.
    all: intros.
    all: unfold graph.
    all: simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    all: now constructor.

  - intros * ? [_ IH_tm].
    split_tm.

    intros * Hconcl.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.

    eapply LamCongUAlg_prem0 in Hconcl as (?&[]); tea.
    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - intros * ? ? [_ IH_tm].
    split_tm.

    intros * [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply LamNeUAlg_prem0 in Hconcl as (?&[]); tea.
    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - intros * ? ? [_ IH_tm].
    split_tm.

    intros * [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply NeLamUAlg_prem0 in Hconcl as (?&[]); tea.
    patch_rec_ret ; econstructor ; [now eapply IH_tm|..].
    now constructor.

  - intros * ? [IHA_ty IHA_tm] ? [IHB_ty IHB_tm].
    split.

    + intros ? [Hconcl]%dup.
      unfold graph.
      simp _uconv uconv_tm_red ; cbn.

      eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
      econstructor ; [now eapply IHA_ty|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound_decl in IHA_ty as [Hpost0 _]; tea.
      eapply typeSigCongAlg_prem1 in Hpost0 ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHB_ty|..].
      now constructor.

    
    + intros * [(?&[->]& _)%termGen' (?&[->]& _)%termGen'].
      unfold graph.
      simp _uconv uconv_tm_red ; cbn.

      assert ([Γ |-[ de ] tSig A B : U] × [Γ |-[ de ] tSig A' B' : U]) as
        [[Hpre0 []]%termSigCongAlg_prem0%dup]%dup.
      {
        split ; now econstructor.
      }

      econstructor ; [now eapply IHA_tm|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound_decl in IHA_tm as [_ Hpost0]; tea.
      eapply termSigCongAlg_prem1 in Hpost0 ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHB_tm|..].
      now constructor.

  - intros * ? [_ IHp] ? [_ IHq].
    split_tm.
    intros * [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.

    eapply PairCongUAlg_prem0 in Hconcl as [Hpre0 []]%dup ; tea.
    econstructor ; [now eapply IHp|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IHp as [_ Hpost0]; tea.
    eapply PairCongUAlg_prem1 in Hpost0 ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHq|..].
    now constructor.

  - intros * ? ? [_ IHp] ? [_ IHq].
    split_tm.
    intros * [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply PairNeUAlg_prem0 in Hconcl as [Hpre0 []]%dup ; tea.
    econstructor ; [now eapply IHp|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IHp as [_ Hpost0]; tea.
    eapply PairNeUAlg_prem1 in Hpost0 ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHq|..].
    now constructor.

  - intros * ? ? [_ IHp] ? [_ IHq].
    split_tm.
    intros * [Hconcl [[Hty]%dup]]%dup.
    unfold graph.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    eapply NePairUAlg_prem0 in Hconcl as [Hpre0 []]%dup ; tea.
    econstructor ; [now eapply IHp|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IHp as [_ Hpost0]; tea.
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
      eapply implem_uconv_graph, uconv_sound_decl in IHA_ty as [[Hpost0]%dup _]; tea.
      eapply typeIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
      econstructor ; [now eapply IHx|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound_decl in IHx as [_ Hpost1]; tea.
      eapply typeIdCongAlg_prem2 in Hpost1 as [Hpre2 []]%dup ; eauto.
      patch_rec_ret ; econstructor ; [now eapply IHy|..] ; cbn.
      now econstructor.
      
    + intros * [(?&[->]& _)%termGen' (?&[->]& _)%termGen'].
      unfold graph.
      simp _uconv uconv_tm_red ; cbn.

      assert ([Γ |-[ de ] tId A x y : U] × [Γ |-[ de ] tId A' x' y' : U]) as
        [[Hpre0 []]%termIdCongAlg_prem0%dup]%dup.
      {
        split ; now econstructor.
      }

      econstructor ; [now eapply IHA_tm|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound_decl in IHA_tm as [_ [Hpost0]%dup]; tea.
      eapply termIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
      econstructor ; [now eapply IHx|..] ; cbn.
      eapply implem_uconv_graph, uconv_sound_decl in IHx as [_ Hpost1]; tea.
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

    + intros ? ? Hconcl.
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
    eapply implem_uconv_graph, uconv_sound_decl in IHm as [? Hpost0] ; tea.
    eapply AppCongUAlg_bridge in Hpost0 as (?&?&[? [Hpre1 []]%dup]); eauto.
    eapply neuAppCongAlg_prem1 in Hpre1 as [Hpre1 []]%dup ; eauto. 
    patch_rec_ret ; econstructor ; [now eapply IHt|..] ; cbn.
    now constructor.

  - intros * ? IH ? [IHP] ? [_ IHz] ? [_ IHs] ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    econstructor ; [now eapply IH|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IH as [? Hpost0] ; tea.
    eapply NatElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
    eapply neuNatElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
    econstructor ; [now eapply IHP|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IHP as [[Hpos1]%dup _].
    2: eassumption.
    eapply neuNatElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
    econstructor ; [now eapply IHz|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IHz as [_ Hpos2] ; tea.
    eapply neuNatElimCong_prem3 in Hpos2 as [Hpre3 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHs|..] ; cbn.
    now constructor.
    
  - intros * ? IH ? [IHP] ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    econstructor ; [now eapply IH|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IH as [? Hpost0] ; tea.
    eapply EmptyElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
    eapply neuEmptyElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHP|..] ; cbn.
    now constructor.

  - intros * ? IH ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IH|..] ; cbn.
    now constructor.

  - intros * ? IH ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IH|..] ; cbn.
    now constructor.

  - intros * ? IH ? [IHP] ? [_ IHe] ? [Hconcl]%dup.
    unfold graph.
    simp _uconv uconv_ne ; cbn.
    eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    econstructor ; [now eapply IH|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IH as [? Hpost0] ; tea.
    eapply IdElimCongUAlg_bridge in Hpost0 as (?&?&?&[? [Hpost0]%dup]); eauto.
    eapply neuIdElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
    econstructor ; [now eapply IHP|..] ; cbn.
    eapply implem_uconv_graph, uconv_sound_decl in IHP as [[Hpos1]%dup _] ; tea.
    eapply neuIdElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
    patch_rec_ret ; econstructor ; [now eapply IHe|..] ; cbn.
    now constructor.

Qed.

End ConversionComplete.