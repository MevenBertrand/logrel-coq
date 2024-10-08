(** * LogRel.BundledAlgorithmicTyping: algorithmic typing bundled with its pre-conditions, and a tailored induction principle. *)

From LogRel Require Import PremisePreserve.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Template Require Import Loader.

Open Scope bs.
Open Scope bool_scope.

From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences TypeConstructorsInj NeutralConvProperties.

Import DeclarativeTypingProperties AlgorithmicTypingData.


Section Invariants.
  Context `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.


  Unset MetaCoq Strict Unquote Universe Mode.

  MetaCoq Quote Definition conv_ty_precond :=
  (fun Γ A B => [Γ |-[de] A] × [Γ |-[de] B]).

  MetaCoq Quote Definition conv_neu_precond :=
  (fun Γ (A : term) t u =>
    [× well_typed (ta := de) Γ t & well_typed (ta := de) Γ u]).

  MetaCoq Quote Definition conv_tm_precond :=
  (fun Γ A t u => ([Γ |-[de] t : A]) × ([Γ |-[de] u : A])).

  #[local] Definition pre_cond (hyp : Ast.term) : Ast.term :=
  match hyp with
    | Ast.tApp c l =>
        if ((c ?= <% ConvTypeAlg %>) || (c ?= <% ConvTypeRedAlg %>))
          then Ast.tApp conv_ty_precond l
        else if ((c ?= <% ConvNeuAlg %>) || (c ?= <% ConvNeuRedAlg %>))
          then Ast.tApp conv_neu_precond l
        else if ((c ?= <% ConvTermAlg %>) || (c ?= <% ConvTermRedAlg %>))
          then Ast.tApp conv_tm_precond l
        else hyp
    | _ => hyp
  end.

  MetaCoq Quote Definition conv_ty_postcond :=
  (fun Γ A B => [Γ |-[de] A ≅ B]).

  MetaCoq Quote Definition conv_neu_postcond :=
  (fun Γ A m n => 
    [× ([Γ |-[de] m ≅ n : A]),
    (forall (T : term), [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
    (forall (T : term), [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]).
    
    
  MetaCoq Quote Definition conv_tm_postcond :=
  (fun Γ A t u => [Γ |-[de] t ≅ u : A]).

  #[local] Definition post_cond (hyp : Ast.term) : Ast.term :=
  match hyp with
    | Ast.tApp c l =>
        if ((c ?= <% ConvTypeAlg %>) || (c ?= <% ConvTypeRedAlg %>))
          then Ast.tApp conv_ty_postcond l
        else if ((c ?= <% ConvNeuAlg %>) || (c ?= <% ConvNeuRedAlg %>))
          then Ast.tApp conv_neu_postcond l
        else if ((c ?= <% ConvTermAlg %>) || (c ?= <% ConvTermRedAlg %>))
          then Ast.tApp conv_tm_postcond l
        else hyp
    | _ => hyp
  end.

  Lemma typeConvRed_prem2 : $run (constructor_premise_preserve pre_cond post_cond 2 "typeConvRed").
  Proof.
    intros * HA HB [].
    eapply subject_reduction_type, reddecl_conv in HA, HB ; tea.
    split ; boundary.
  Qed.

  Lemma typeConvRed_concl : $run (constructor_concl_preserve pre_cond post_cond "typeConvRed").
  Proof.
    intros * HA HB IHA' [? ?].
    eapply subject_reduction_type, reddecl_conv in HA, HB ; tea.
    do 2 etransitivity ; tea.
    all: now econstructor.
  Qed.

  Lemma typePiCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "typePiCongAlg").
  Proof.
    now intros * [[]%prod_ty_inv []%prod_ty_inv].
  Qed.

  Lemma typePiCongAlg_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "typePiCongAlg").
  Proof.
    intros * ? [[]%prod_ty_inv []%prod_ty_inv].
    split ; [gen_typing|..].
    now eapply stability1.
  Qed.
  
  Lemma typePiCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "typePiCongAlg").
  Proof.
    intros * ?? _.
    econstructor ; tea.
    boundary.
  Qed.

  Lemma typeSigCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "typeSigCongAlg").
  Proof.
    now intros * [[]%sig_ty_inv []%sig_ty_inv].
  Qed.

  Lemma typeSigCongAlg_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "typeSigCongAlg").
  Proof.
    intros * ? [[]%sig_ty_inv []%sig_ty_inv].
    split ; [gen_typing|..].
    now eapply stability1.
  Qed.
  
  Lemma typeSigCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "typeSigCongAlg").
  Proof.
    intros * ?? _.
    econstructor ; tea.
    boundary.
  Qed.

  Lemma typeIdCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "typeIdCongAlg").
  Proof.
    now intros * [[]%id_ty_inv []%id_ty_inv].
  Qed.
  
  Lemma typeIdCongAlg_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "typeIdCongAlg").
  Proof.
    intros * ? [[]%id_ty_inv []%id_ty_inv].
    split ; [assumption|now econstructor].
  Qed.

  Lemma typeIdCongAlg_prem2 : $run (constructor_premise_preserve pre_cond post_cond 2 "typeIdCongAlg").
  Proof.
    intros * ?? [[]%id_ty_inv []%id_ty_inv].
    split ; [assumption|now econstructor].
  Qed.

  Lemma typeIdCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "typeIdCongAlg").
  Proof.
    intros * ??? [[]%id_ty_inv []%id_ty_inv].
    now econstructor.
  Qed.


  Lemma typeNeuConvAlg_prem2 : $run (constructor_premise_preserve pre_cond post_cond 2 "typeNeuConvAlg").
  Proof.
    intros * _ ?? [?%neutral_ty_inv ?%neutral_ty_inv] ; tea.
    now split ; eexists.
  Qed.

  Lemma typeNeuConvAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "typeNeuConvAlg").
  Proof.
    intros * ?? [? HM] [?%neutral_ty_inv] ; tea.
    do 2 econstructor ; tea.
    now eapply HM.
  Qed.

  Lemma neuVarConvAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "neuVarConvAlg").
  Proof.
    intros * Hin [_ []].
    split.
    - do 2 constructor ; gen_typing.
    - intros T Hty.
      eapply termGen' in Hty as [? [[? [->]] ?]].
      eapply in_ctx_inj in Hin ; tea ; subst.
      eassumption.
    - intros T Hty.
      eapply termGen' in Hty as [? [[? [->]] ?]].
      eapply in_ctx_inj in Hin ; tea ; subst.
      eassumption.
  Qed.

  Lemma neuAppCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "neuAppCongAlg").
  Proof.
    intros * _ _ [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuAppCongAlg_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "neuAppCongAlg").
  Proof.
    intros * [? Hm Hn] [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    eapply prod_ty_inj in Hm as [] ; tea.
    eapply prod_ty_inj in Hn as [] ; tea.
    split ; now econstructor.
  Qed.

  Lemma neuAppCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "neuAppCongAlg").
  Proof.
    intros * [? Hm Hn] ? [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split.
    + econstructor ; gen_typing.
    + intros ? Happ.
      eapply termGen' in Happ as [? [(?&?&[-> Htym']) ?]].
      eapply prod_ty_inj in Hm as [] ; tea.
      etransitivity ; [..|eassumption].
      eapply typing_subst1 ; tea.
      now econstructor.
    + intros ? Happ.
      eapply termGen' in Happ as [? [(?&?&[-> Htym']) ?]].
      eapply prod_ty_inj in Hn as [] ; tea.
      etransitivity ; [..|eassumption].
      eapply typing_subst1.
      2: eassumption.
      econstructor ; tea.
      now symmetry.
  Qed.

  Lemma neuNatElimCong_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "neuNatElimCong").
  Proof.
    intros * [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuNatElimCong_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "neuNatElimCong").
  Proof.
    intros * [? Hn Hn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    now split.
  Qed.

  Lemma neuNatElimCong_prem2 : $run (constructor_premise_preserve pre_cond post_cond 2 "neuNatElimCong").
  Proof.
    intros * [? Hn Hn'] HP [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    1: eassumption.
    econstructor ; tea.
    symmetry.
    eapply typing_subst1 ; tea.
    gen_typing.
  Qed.

  Lemma neuNatElimCong_prem3 : $run (constructor_premise_preserve pre_cond post_cond 3 "neuNatElimCong").
  Proof.
    intros * [? Hn Hn'] HP _ [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    1: eassumption.
    econstructor ; tea.
    symmetry.
    eapply elimSuccHypTy_conv.
    all: gen_typing.
  Qed.

  Lemma neuNatElimCong_concl : $run (constructor_concl_preserve pre_cond post_cond "neuNatElimCong").
  Proof.
    intros * [? Hn Hn'] HP ? ? [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    + now econstructor.
    + now intros ?[? [[->]]]%termGen'.
    + intros ?[? [[->]]]%termGen'.
      etransitivity.
      1: eapply typing_subst1.
      all: eassumption.
  Qed.

  Lemma neuEmptyElimCong_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "neuEmptyElimCong").
  Proof.
    intros * [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuEmptyElimCong_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "neuEmptyElimCong").
  Proof.
    intros * [? Hn Hn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    now split.
  Qed.

  Lemma neuEmptyElimCong_concl : $run (constructor_concl_preserve pre_cond post_cond "neuEmptyElimCong").
  Proof.
    intros * [? Hn Hn'] HP [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    + now econstructor.
    + now intros ?[? [[->]]]%termGen'.
    + intros ?[? [[->]]]%termGen'.
      etransitivity.
      1: eapply typing_subst1.
      all: eassumption.
  Qed.

  Lemma neuFstCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "neuFstCongAlg").
  Proof.
    intros * _ _ [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuFstCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "neuFstCongAlg").
  Proof.
    intros * [? Hm Hn] [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split.
    + now econstructor.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hm as [].
      2: eassumption.
      now etransitivity.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hn as [].
      2: eassumption.
      now etransitivity.
  Qed.

  Lemma neuSndCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "neuSndCongAlg").
  Proof.
    intros * _ _ [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuSndCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "neuSndCongAlg").
  Proof.
    intros * [? Hm Hn] [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split.
    + now econstructor.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hm as [].
      2: eassumption.
      etransitivity; tea.
      eapply typing_subst1; tea ; do 2 econstructor.
      boundary.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hn as [].
      2: eassumption.
      etransitivity; tea.
      eapply typing_subst1; tea.
      now econstructor.
  Qed.

  Lemma neuIdElimCong_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "neuIdElimCong").
  Proof.
    intros * _ * _ * _ * [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuIdElimCong_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "neuIdElimCong").
  Proof.
    intros * [? Hn Hn'] [[Hwn Hwn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']]]%dup.
    split.
    1: eassumption.
    epose proof (idElimConv Hwn Hwn') as (?&?&?&[]) ; tea.
    1: eapply TypeRefl ; refold ; boundary.
    1: constructor.
    eapply stability; tea.
    eapply idElimMotiveCtxConv; tea.
    1: eapply ctx_refl ; boundary.
    2: econstructor ; tea.
    all: now symmetry.
  Qed.

  Lemma neuIdElimCong_prem2 : $run (constructor_premise_preserve pre_cond post_cond 2 "neuIdElimCong").
  Proof.
    intros * [? Hn Hn'] HP [[Hwn Hwn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']]]%dup.
    split.
    1: eassumption.
    epose proof (idElimConv Hwn Hwn') as (?&?&?&[]) ; tea.
    1: eapply TypeRefl ; refold ; boundary.
    1: constructor.
    econstructor ; tea.
    symmetry.
    eapply typing_subst2 ; tea.
    1: boundary.
    cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq; now econstructor.
  Qed.

  Lemma neuIdElimCong_concl : $run (constructor_concl_preserve pre_cond post_cond "neuIdElimCong").
  Proof.
    intros * [? Hn Hn'] HP Hr [[Hwn Hwn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']]]%dup.
    epose proof (idElimConv Hwn Hwn') as (?&?&?&[He]) ; tea.
    1: eapply TypeRefl ; refold ; boundary.
    1: constructor.
    inversion_clear He.
    split.
    + econstructor ; tea.
      econstructor ; tea.
      symmetry.
      now econstructor.
    + now intros ?[? [[->]]]%termGen'.
    + intros ?[? [[->]]]%termGen'.
      etransitivity.
      2: eassumption.
      eapply typing_subst2 ; tea.
      1: boundary.
      econstructor ; tea.
      symmetry.
      cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
      now constructor.
  Qed.

  Lemma neuConvRed_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "neuConvRed").
  Proof.
    easy.
  Qed.

  Lemma neuConvRed_concl : $run (constructor_concl_preserve pre_cond post_cond "neuConvRed").
  Proof.
    eintros * [] ?%subject_reduction_type%reddecl_conv ? [].
    2: boundary.
    split.
    - now econstructor.
    - intros.
      etransitivity.
      2: eauto.
      now symmetry.
    - intros.
      etransitivity.
      2: eauto.
      now symmetry.
  Qed.

  Lemma termConvRed_prem3 : $run (constructor_premise_preserve pre_cond post_cond 3 "termConvRed").
  Proof.
    eintros * HA Ht Hu [].
    eapply subject_reduction_type, reddecl_conv in HA.
    2: boundary.
    eapply subject_reduction in Ht ; tea.
    eapply subject_reduction in Hu ; tea.
    split.
    all: econstructor ; tea.
    all: boundary.
  Qed.

  Lemma termConvRed_concl : $run (constructor_concl_preserve pre_cond post_cond "termConvRed").
  Proof.
    eintros * HA Ht Hu ? [].
    eapply subject_reduction_type, reddecl_conv in HA.
    2: boundary.
    eapply subject_reduction, RedConvTeC in Ht ; tea.
    eapply subject_reduction, RedConvTeC in Hu ; tea.
    etransitivity ; tea.
    etransitivity.
    1: now econstructor.
    now symmetry.
  Qed.

  Lemma termPiCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "termPiCongAlg").
  Proof.
    intros * [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    now split.
  Qed.

  Lemma termPiCongAlg_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "termPiCongAlg").
  Proof.
    intros * ? [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    split.
    1: eassumption.
    eapply stability1 ; tea.
    now constructor.
  Qed.

  Lemma termPiCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "termPiCongAlg").
  Proof.
    intros.
    constructor ; tea.
    boundary.
  Qed.

  Lemma termSuccCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "termSuccCongAlg").
  Proof.
    now intros * [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
  Qed.
  
  Lemma termSuccCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "termSuccCongAlg").
  Proof.
    now constructor.
  Qed.

  Lemma termFunConvAlg_prem2: $run (constructor_premise_preserve pre_cond post_cond 2 "termFunConvAlg").
  Proof.
    intros * ?? [?%typing_eta' ?%typing_eta'].
    now split.
  Qed.

  Lemma termFunConvAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "termFunConvAlg").
  Proof.
    intros * ?? ? [].
    etransitivity; [|now eapply TermFunEta].
    etransitivity; [symmetry; now eapply TermFunEta|].
    econstructor ; tea.
    2-3: constructor.
    all: boundary.
  Qed.

  Lemma termSigCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "termSigCongAlg").
  Proof.
    intros * [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    now split.
  Qed.

  Lemma termSigCongAlg_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "termSigCongAlg").
  Proof.
    intros * ? [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    split.
    1: eassumption.
    eapply stability1 ; tea.
    now constructor.
  Qed.

  Lemma termSigCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "termSigCongAlg").
  Proof.
    intros.
    constructor ; tea.
    boundary.
  Qed.

  Lemma termPairConvAlg_prem2 : $run (constructor_premise_preserve pre_cond post_cond 2 "termPairConvAlg").
  Proof.
    intros * ?? [].
    split.
    all: now econstructor.
  Qed.

  Lemma termPairConvAlg_prem3 : $run (constructor_premise_preserve pre_cond post_cond 3 "termPairConvAlg").
  Proof.
    intros * ?? ? [Hp ].
    split.
    1: now econstructor.
    econstructor.
    1: now econstructor.
    eapply typing_subst1.
    1: now symmetry.
    constructor.
    now eapply boundary, sig_ty_inv in Hp as [].
  Qed.

  Lemma termPairConvAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "termPairConvAlg").
  Proof.
    intros * ?? ? ? [Hp].
    etransitivity; [|now eapply TermPairEta].
    etransitivity; [symmetry; now eapply TermPairEta|].
    eapply boundary, sig_ty_inv in Hp as [].
    econstructor ; tea.
    all: constructor ; boundary.
  Qed.

  Lemma termIdCongAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "termIdCongAlg").
  Proof.
    now intros * [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
  Qed.
  
  Lemma termIdCongAlg_prem1 : $run (constructor_premise_preserve pre_cond post_cond 1 "termIdCongAlg").
  Proof.
    intros * ? [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
    split.
    1: assumption.
    econstructor ; tea.
    now constructor. 
  Qed.

  Lemma termIdCongAlg_prem2 : $run (constructor_premise_preserve pre_cond post_cond 2 "termIdCongAlg").
  Proof.
    intros * ?? [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
    split.
    1: assumption.
    econstructor ; tea.
    now constructor. 
  Qed.

  Lemma termIdCongAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "termIdCongAlg").
  Proof.
    intros * ??? [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
    now econstructor.
  Qed.

  Lemma termIdReflCong_concl : $run (constructor_concl_preserve pre_cond post_cond "termIdReflCong").
  Proof.
    intros * [[?[[-> ??] []%id_ty_inj]]%termGen' [?[[-> ??] []%id_ty_inj]]%termGen'].
    assert [Γ |-[de] A ≅ A'] by
        (etransitivity ; tea ; now symmetry).
    econstructor.
    1: econstructor.
    3: econstructor.
    + eassumption. 
    + etransitivity ; tea.
      symmetry.
      now econstructor.
    + now symmetry.
    + eassumption.
    + eassumption.
  Qed.

  Lemma termNeuConvAlg_prem0 : $run (constructor_premise_preserve pre_cond post_cond 0 "termNeuConvAlg").
  Proof.
    intros * _ ? [].
    split ; now eexists.
  Qed.

  Lemma termNeuConvAlg_concl : $run (constructor_concl_preserve pre_cond post_cond "termNeuConvAlg").
  Proof.
    intros * [] ? [].
    now econstructor.
  Qed.

End Invariants.


(** ** Definition of bundled algorithmic typing *)

Definition bn : tag.
Proof.
constructor.
Qed.

Definition bni : tag.
Proof.
constructor.
Qed.

(** The idea of these definitions is to put together an algorithmic derivation with the
pre-conditions that ensure it is sensible. Indeed, for instance [Γ |-[al] A] does not
re-check that Γ is well-typed: in the algorithm, this information is instead maintained as
an invariant. But this means that algorithmic variants, do not unconditionally
imply its declarative counterpart, they only do so if their pre-conditions are fulfilled,
eg if the context or type are well-formed. *)

(** Also note that in the case of judgements that “output” a type, ie type inference and
neutral conversion, we allow for an arbitrary conversion to “rectify” the output type.
This makes it easier to handle these in the logical relation, because it means the interface
is stable by arbitrary conversion. *)

(** In the case of a context, there is no judgement, only a pre-condition, as algorithmic
typing never re-checks a context. *)
Record WfContextBun Γ :=
{
  bn_wf_ctx : [|-[de] Γ] ;
}.

Record WfTypeBun Γ A :=
{
  bun_wf_ty_ctx : [|-[de] Γ] ;
  bun_wf_ty : [Γ |-[al] A] ;
}.

Record InferBun Γ A t :=
{
  bun_inf_ctx : [|-[de] Γ] ;
  bun_inf : [Γ |-[al] t ▹ A]
}.

Record InferConvBun Γ A t :=
{
  bun_inf_conv_ctx : [|-[de] Γ] ;
  bun_inf_conv_ty : term ;
  bun_inf_conv_inf : [Γ |-[al] t ▹ bun_inf_conv_ty] ;
  (** Allows to change the type to any convertible one. *)
  bun_inf_conv_conv : [Γ |-[de] bun_inf_conv_ty ≅ A]
}.

Record InferRedBun Γ A t :=
{
  bun_inf_red_ctx : [|-[de] Γ] ;
  bun_inf_red : [Γ |-[al] t ▹h A]
}.

Record CheckBun Γ A t :=
{
  bun_chk_ctx : [|-[de] Γ] ;
  bun_chk_ty : [Γ |-[de] A] ;
  bun_chk : [Γ |-[al] t ◃ A]
}.

Record ConvTypeBun Γ A B :=
{
  bun_conv_ty_ctx : [|-[de] Γ] ;
  bun_conv_ty_l : [Γ |-[de] A] ;
  bun_conv_ty_r : [Γ |-[de] B] ;
  bun_conv_ty : [Γ |-[al] A ≅ B]
}.

Record ConvTypeRedBun Γ A B :=
{
  bun_conv_ty_red_ctx : [|-[de] Γ] ;
  bun_conv_ty_red_l : [Γ |-[de] A] ;
  bun_conv_ty_red_wh_l : isType A ;
  bun_conv_ty_red_r : [Γ |-[de] B] ;
  bun_conv_ty_red_wh_r : isType B ;
  bun_conv_ty_red : [Γ |-[al] A ≅h B]
}.

Record ConvTermBun Γ A t u :=
{
  bun_conv_tm_ctx : [|-[de] Γ] ;
  bun_conv_tm_ty : [Γ |-[de] A] ;
  bun_conv_tm_l : [Γ |-[de] t : A] ;
  bun_conv_tm_r : [Γ |-[de] u : A] ;
  bun_conv_tm : [Γ |-[al] t ≅ u : A]
}.

Record ConvTermRedBun Γ A t u :=
{
  bun_conv_tm_red_ctx : [|-[de] Γ] ;
  bun_conv_tm_red_ty : [Γ |-[de] A] ;
  bun_conv_tm_red_wh_ty : isType A ;
  bun_conv_tm_red_l : [Γ |-[de] t : A] ;
  bun_conv_tm_red_wh_l : whnf t ;
  bun_conv_tm_red_r : [Γ |-[de] u : A] ;
  bun_conv_tm_red_wh_r : whnf u ;
  bun_conv_tm_red : [Γ |-[al] t ≅h u : A]
}.

Record ConvNeuBun Γ A m n :=
{
  bun_conv_ne_ctx : [|-[de] Γ] ;
  bun_conv_ne_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_wh_l : whne m ;
  bun_conv_ne_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_wh_r : whne n ;
  bun_conv_ne : [Γ |-[al] m ~ n ▹ A]
}.

Record ConvNeuRedBun Γ A m n :=
{
  bun_conv_ne_red_ctx : [|-[de] Γ] ;
  bun_conv_ne_red_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_red_wh_l : whne m ;
  bun_conv_ne_red_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_red_wh_r : whne n ;
  bun_conv_ne_red : [Γ |-[al] m ~h n ▹ A]
}.

Record ConvNeuConvBun Γ A m n :=
{
  bun_conv_ne_conv_ctx : [|-[de] Γ] ;
  bun_conv_ne_conv_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_conv_wh_l : whne m ;
  bun_conv_ne_conv_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_conv_wh_r : whne n ;
  bun_conv_ne_conv_ty : term ;
  bun_conv_ne_conv : [Γ |-[al] m ~ n ▹ bun_conv_ne_conv_ty] ;
  bun_conv_ne_conv_conv : [Γ |-[de] bun_conv_ne_conv_ty ≅ A]
}.

Record RedTypeBun Γ A B :=
{
  bun_red_ty_ctx : [|-[de] Γ] ;
  bun_red_ty_ty : [Γ |-[al] A] ;
  bun_red_ty : [A ⤳* B] ;
}.

Record OneStepRedTermBun Γ A t u :=
{
  bun_osred_tm_ctx : [|-[de] Γ] ;
  (** We do not have the instance yet, so we have to specify it by hand,
  but this really is [Γ |-[bn] t : A]. *)
  bun_osred_tm_tm : typing (ta := bn) (Typing := InferConvBun) Γ A t ;
  bun_osred_tm : [t ⤳ u]
}.

Record RedTermBun Γ A t u :=
{
  bun_red_tm_ctx : [|-[de] Γ] ;
  bun_red_tm_tm : typing (ta := bn) (Typing := InferConvBun) Γ A t ;
  bun_red_tm : [t ⤳* u] ;
}.

Record RedTypeBunI Γ A B :=
{
  buni_red_ty_ctx : [|-[de] Γ] ;
  buni_red_ty_ty : [Γ |-[de] A] ;
  buni_red_ty : [A ⤳* B] ;
}.

Record OneStepRedTermBunI Γ A t u :=
{
  buni_osred_tm_ctx : [|-[de] Γ] ;
  buni_osred_tm_tm : [Γ |-[de] t : A] ;
  buni_osred_tm : [t ⤳ u]
}.

Record RedTermBunI Γ A t u :=
{
  buni_red_tm_ctx : [|-[de] Γ] ;
  buni_red_tm_tm : [Γ |-[de] t : A] ;
  buni_red_tm : [t ⤳* u] ;
}.

(** ** Instances *)

(** We actually define two instances, one fully-algorithmic and one where only conversion
is algorithmic, but typing is not. This is needed because we cannot show right away that
(bundled) algorithmic typing has all the properties to be an instance of the generic interface.
The issue is that the logical relation does not give enough properties of neutrals, in particular
we cannot derive that neutral application is injective, ie if [tApp n u] and [tApp n' u'] are
convertible then [n] and [n'] are and so are [u] and [u']. Thus, we use the mixed instance, which
we can readily show, to gather more properties of conversion, enough to show the fully 
algorithmic one. *)

Module BundledTypingData.

  #[export] Instance WfContext_Bundle : WfContext bn := WfContextBun.
  #[export] Instance WfType_Bundle : WfType bn := WfTypeBun.
  #[export] Instance Inferring_Bundle : Inferring bn := InferBun. 
  #[export] Instance InferringRed_Bundle : InferringRed bn := InferRedBun.
  #[export] Instance Typing_Bundle : Typing bn := InferConvBun.
  #[export] Instance Checking_Bundle : Checking bn := CheckBun.
  #[export] Instance ConvType_Bundle : ConvType bn := ConvTypeBun.
  #[export] Instance ConvTypeRed_Bundle : ConvTypeRed bn :=  ConvTypeRedBun.
  #[export] Instance ConvTerm_Bundle : ConvTerm bn := ConvTermBun.
  #[export] Instance ConvTermRed_Bundle : ConvTermRed bn := ConvTermRedBun.
  #[export] Instance ConvNeu_Bundle : ConvNeu bn := ConvNeuBun.
  #[export] Instance ConvNeuRed_Bundle : ConvNeuRed bn := ConvNeuRedBun.
  #[export] Instance ConvNeuConv_Bundle : ConvNeuConv bn := ConvNeuConvBun.
  #[export] Instance RedType_Bundle : RedType bn := RedTypeBun.
  #[export] Instance OneStepRedTerm_Bundle : OneStepRedTerm bn := OneStepRedTermBun.
  #[export] Instance RedTerm_Bundle : RedTerm bn := RedTermBun.

  Ltac fold_bun :=
    change WfContextBun with (wf_context (ta := bn)) in *;
    change WfTypeBun with (wf_type (ta := bn)) in *;
    change InferBun with (inferring (ta := bn)) in * ;
    change InferRedBun with (infer_red (ta := bn)) in * ;
    change InferConvBun with (typing (ta := bn)) in * ;
    change CheckBun with (check (ta := bn)) in * ;
    change ConvTypeBun with (conv_type (ta := bn)) in * ;
    change ConvTermBun with (conv_term (ta := bn)) in * ;
    change ConvNeuBun with (conv_neu (ta := bn)) in * ;
    change ConvTypeRedBun with (conv_type_red (ta := bn)) in * ;
    change ConvTermRedBun with (conv_term_red (ta := bn)) in * ;
    change ConvNeuRedBun with (conv_neu_red (ta := bn)) in *;
    change ConvNeuConvBun with (conv_neu_conv (ta := bn)) in *;
    change RedTypeBun with (red_ty (ta := bn)) in * ;
    change OneStepRedTermBun with (osred_tm (ta := bn)) in * ;
    change RedTermBun with (red_tm (ta := bn)) in *.

End BundledTypingData.

Import BundledTypingData.

Module BundledIntermediateData.

  #[export] Instance WfContext_BundleInt : WfContext bni := WfContextDecl.
  #[export] Instance WfType_BundleInt : WfType bni := WfTypeDecl.
  #[export] Instance Typing_BundleInt : Typing bni := TypingDecl.
  #[export] Instance ConvType_BundleInt : ConvType bni := ConvTypeBun.
  #[export] Instance ConvTerm_BundleInt : ConvTerm bni := ConvTermBun.
  #[export] Instance ConvNeuConv_BundleInt : ConvNeuConv bni := ConvNeuConvBun.
  #[export] Instance RedType_BundleInt : RedType bni := RedTypeBunI.
  #[export] Instance OneStepRedTerm_BundleInt : OneStepRedTerm bni := OneStepRedTermBunI.
  #[export] Instance RedTerm_BundleInt : RedTerm bni := RedTermBunI.

  Ltac unfold_bni :=
    change (wf_context (ta := bni)) with (wf_context (ta := de)) in *;
    change (wf_type (ta := bni)) with (wf_type (ta := de)) in *;
    change (typing (ta := bni)) with (typing (ta := de)) in * ;
    change (conv_type (ta := bni)) with (conv_type (ta := bn)) in * ;
    change (conv_term (ta := bni)) with (conv_term (ta := bn)) in * ;
    change (conv_neu_conv (ta := bni)) with (conv_neu_conv (ta := bn)) in *.

End BundledIntermediateData.

Set Universe Polymorphism.

(** ** Induction principle for bundled algorithmic conversion *)

(** We show an induction principle tailored for the bundled predicates: it threads the invariants
of the algorithm through the derivation, giving us stronger hypothesis in the minor premises,
corresponding to both the pre-conditions being true, and the post-conditions of the induction
hypotheses holding. *)

Section BundledConv.
  Universe u.

  Context `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.


  Context (PTyEq PTyRedEq : context -> term -> term -> Type@{u})
  (PNeEq PNeRedEq PTmEq PTmRedEq : context -> term -> term -> term -> Type@{u}).

  (** Rather than writing by hand the various large statements of the induction principles,
  we use Ltac to derive them generically. Hopefully, there is no need to touch any part of
  this code when extending modifying the language with more features. *)
  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTyEq ?Γ ?A ?B] =>
        constr:([Γ |-[de] A] × [Γ |-[de] B] -> Hyp)
    | context [PTyRedEq ?Γ ?A ?B] =>
        constr:([Γ |-[de] A] × [Γ |-[de] B] -> Hyp)
    | context [PNeEq ?Γ ?A ?t ?u] =>
        constr:((well_typed (ta := de) Γ t) × (well_typed (ta := de) Γ u) -> Hyp)
    | context [PNeRedEq ?Γ ?A ?t ?u] =>
        constr:((well_typed (ta := de) Γ t) × (well_typed (ta := de) Γ u) -> Hyp)
    | context [PTmEq ?Γ ?A ?t ?u] =>
        constr:(([Γ |-[de] t : A]) × ([Γ |-[de] u : A]) -> Hyp)
    | context [PTmRedEq ?Γ ?A ?t ?u] =>
        constr:(([Γ |-[de] t : A]) × ([Γ |-[de] u : A]) -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTyEq ?Γ ?A ?B] =>
        context C [PTyEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PTyRedEq ?Γ ?A ?B] =>
        context C [PTyRedEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PNeEq ?Γ ?A ?m ?n] =>
        context C [PNeEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PNeRedEq ?Γ ?A ?m ?n] =>
        context C [PNeRedEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PTmEq ?Γ ?A ?t ?u] =>
        context C [PTmEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | context C [PTmRedEq ?Γ ?A ?t ?u] =>
        context C [PTmRedEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A ≅ ?B] => constr:([Γ |-[bn] A ≅ B])
      | [?Γ |-[al] ?A ≅h ?B] => constr:([Γ |-[bn] A ≅h B])
      | [?Γ |-[al] ?t ≅ ?u : ?A] => constr:([Γ |-[bn] t ≅ u : A])
      | [?Γ |-[al] ?t ≅h ?u : ?A] => constr:([Γ |-[bn] t ≅h u : A])
      | [?Γ |-[al] ?m ~ ?n ▹ ?A] => constr:([Γ |-[bn] m ~ n ▹ A])
      | [?Γ |-[al] ?m ~h ?n ▹ ?A] => constr:([Γ |-[bn] m ~h n ▹ A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  #[local] Definition algo_conv_discipline_stmt := 
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq)) in
      let ind := strong_statement t in
      exact ind).

  (** The main theorem *)
  Theorem algo_conv_discipline : algo_conv_discipline_stmt.
  Proof.
    unfold algo_conv_discipline_stmt; intros.
    apply AlgoConvInduction.
    - intros * ?? ? IHA [? Hconcl]%dup.
      eapply typeConvRed_prem2, IHA in Hconcl as [? [? Hpre2]%dup] ; eauto.
      eapply typeConvRed_concl in Hpre2 ; eauto.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply typePiCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply typePiCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply typePiCongAlg_concl in Hpre1 ; eauto.
    - intros * [].
      split ; [now eauto|..].
      now constructor.
    - intros * [].
      split ; [now eauto|..].
      now constructor.
    - intros * [].
      split ; [now eauto|..].
      now constructor.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply typeSigCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply typeSigCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply typeSigCongAlg_concl in Hpre1 ; eauto.
    - intros * ? IHA ? IHx ? IHy [? Hconcl]%dup.
      eapply typeIdCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply typeIdCongAlg_prem1, IHx in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply typeIdCongAlg_prem2, IHy in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply typeIdCongAlg_concl in Hpre2 ; eauto 20.
    - intros * ?? Hconv IH [? Hconcl]%dup.
      eapply typeNeuConvAlg_prem2, IH in Hconcl as [? [? Hpre2]%dup] ; eauto.
      eapply typeNeuConvAlg_concl in Hpre2 ; eauto.
    - intros * ? [? Hconcl]%dup.
      eapply neuVarConvAlg_concl in Hconcl ; eauto.
    - intros * ? IHm ? IHt [? Hconcl]%dup.
      eapply neuAppCongAlg_prem0, IHm in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuAppCongAlg_prem1, IHt in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuAppCongAlg_concl in Hpre1 ; eauto.
    - intros * ? IHn ? IHP ? IHz ? IHs [? Hconcl]%dup.
      eapply neuNatElimCong_prem0, IHn in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuNatElimCong_prem1, IHP in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuNatElimCong_prem2, IHz in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply neuNatElimCong_prem3, IHs in Hpre2 as [? [? Hpre3]%dup] ; eauto.
      eapply neuNatElimCong_concl in Hpre3 ; eauto 20.
    - intros * ? IHe ? IHP [? Hconcl]%dup.
      eapply neuEmptyElimCong_prem0, IHe in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuEmptyElimCong_prem1, IHP in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuEmptyElimCong_concl in Hpre1 ; eauto.
    - intros * ? IH [? Hconcl]%dup.
      eapply neuFstCongAlg_prem0, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuFstCongAlg_concl in Hpre0 ; eauto.
    - intros * ? IH [? Hconcl]%dup.
      eapply neuSndCongAlg_prem0, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuSndCongAlg_concl in Hpre0 ; eauto.
    - intros * ? IHn ? IHP ? IHe [? Hconcl]%dup.
      eapply neuIdElimCong_prem0, IHn in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuIdElimCong_prem1, IHP in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuIdElimCong_prem2, IHe in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply neuIdElimCong_concl in Hpre2 ; eauto 20.
    - intros * ? IHm ?? [? Hconcl]%dup.
      eapply IHm in Hconcl as [? [? Hpre0]]%dup.
      eapply neuConvRed_concl in Hpre0 as [? Hconcl]%dup ; eauto.
    - intros * ??? ? IH [? Hconcl]%dup.
      eapply termConvRed_prem3, IH in Hconcl as [? [? Hpre3]%dup] ; eauto.
      eapply termConvRed_concl in Hpre3 ; eauto.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply termPiCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termPiCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply termPiCongAlg_concl in Hpre1 ; eauto.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHt [? Hconcl]%dup.
      eapply termSuccCongAlg_prem0, IHt in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termSuccCongAlg_concl in Hpre0 ; eauto.
    - intros.
      split ; [eauto|..].
      now econstructor. 
    - intros * ??? IH [? Hconcl]%dup.
      eapply termFunConvAlg_prem2, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termFunConvAlg_concl in Hpre0 ; eauto.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply termSigCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termSigCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply termSigCongAlg_concl in Hpre1 ; eauto.
    - intros * ??? IHf ? IHs [? Hconcl]%dup.
      eapply termPairConvAlg_prem2, IHf in Hconcl as [? [? Hpre2]%dup] ; eauto.
      eapply termPairConvAlg_prem3, IHs in Hpre2 as [? [? Hpre3]%dup] ; eauto.
      eapply termPairConvAlg_concl in Hpre3 ; eauto.
    - intros * ? IHA ? IHx ? IHy [? Hconcl]%dup.
      eapply termIdCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termIdCongAlg_prem1, IHx in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply termIdCongAlg_prem2, IHy in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply termIdCongAlg_concl in Hpre2 ; eauto 20.
    - intros * [? Hconcl]%dup.
      eapply termIdReflCong_concl in Hconcl ; eauto.
    - intros * ? IH ? [? Hconcl]%dup.
      eapply termNeuConvAlg_prem0, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termNeuConvAlg_concl in Hpre0 ; eauto.
Qed.

  Definition BundledConvInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) in
      let t' := weak_statement t in exact t').

  (** As a corollary, we get the desired induction principle. The difference with the above one
  is that we do not get the post-condition of the algorithm in the conclusion, but this is
  in general not necessary. *)
  Corollary BundledConvInduction :
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat split.
    all: intros * [].
    all: now apply algo_conv_discipline.
  Qed.

End BundledConv.

(** ** Soundness of algorithmic conversion *)

(** Contrarily to the induction principle above, if we instantiate the main principle with
only constant true predicates, we get only the post-conditions, ie a soundness theorem: bundled algorithmic conversion judgments imply their declarative counterparts. *)

Section ConvSoundness.

  Context `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.


  Let PTyEq (Γ : context) (A B : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] B] ->
    [Γ |-[de] A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) :=
    [Γ |-[de] t : A] -> [Γ |-[de] u : A] ->
    [Γ |-[de] t ≅ u : A].
  Let PNeEq (Γ : context) (A : term) (m n : term) :=
    (well_typed (ta := de) Γ m) ->
    (well_typed (ta := de) Γ n) ->
    [× [Γ |-[de] m ≅ n : A],
      (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
      (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])].

  Theorem algo_conv_sound : AlgoConvInductionConcl PTyEq PTyEq PNeEq PNeEq PTmEq PTmEq.
  Proof.
    subst PTyEq PTmEq PNeEq.
    red.
    pose proof (algo_conv_discipline 
      (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)) as [H' H] ;
    cycle -1.
    1:{
      repeat (split ; [intros ; apply H' ; eauto |..] ; clear H' ; try destruct H as [H' H]).
      intros ; apply H ; eauto. 
    }
    all: now constructor.
  Qed.

End ConvSoundness.

Theorem bn_conv_sound
  `{!TypingSubst (ta := de)}
  `{!TypeReductionComplete (ta := de)}
  `{!TypeConstructorsInj (ta := de)} :

  BundledConvInductionConcl
    (fun Γ A B => [Γ |-[de] A ≅ B])
    (fun Γ A B => [Γ |-[de] A ≅ B])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A]).
Proof.
  red.
  prod_splitter.
  all: intros * [].
  all: match goal with H : context [al] |- _ => eapply algo_conv_sound in H end.
  all: prod_hyp_splitter.
  all: try eassumption.
  all: now eexists.
Qed.

(** ** Induction principle for bundled algorithmic typing *)

(** This is repeating the same ideas as before, but for typing. *)

Section BundledTyping.

  Context `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.

  Context (PTy : context -> term -> Type)
    (PInf PInfRed PCheck : context -> term -> term -> Type).

  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTy ?Γ ?A] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInf ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInfRed ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PCheck ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTy ?Γ ?A] =>
        context C [PTy Γ A × [Γ |-[de] A]]
    | context C [PInf ?Γ ?A ?t] =>
        context C [PInf Γ A t × [Γ |-[de] t : A]]
    | context C [PInfRed ?Γ ?A ?t] =>
        context C [PInfRed Γ A t × [Γ |-[de] t : A]]
    | context C [PCheck ?Γ ?A ?t] =>
        context C [PCheck Γ A t × [Γ |-[de] t : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A] => constr:([Γ |-[bn] A])
      | [?Γ |-[al] ?t ▹ ?A] => constr:([Γ |-[bn] t ▹ A])
      | [?Γ |-[al] ?t ▹h ?A] => constr:([Γ |-[bn] t ▹h A])
      | [?Γ |-[al] ?t ◃ ?A] => constr:([Γ |-[bn] t ◃ A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  Let PTy' (c : context) (t : term) :=
        [ |-[ de ] c] -> PTy c t × [c |-[ de ] t].
  Let PInf' (c : context) (t t1 : term) :=
     [ |-[ de ] c] -> PInf c t t1 × [c |-[ de ] t1 : t].
  Let PInfRed' (c : context) (t t1 : term) :=
       [ |-[ de ] c] -> PInfRed c t t1 × [c |-[ de ] t1 : t].
  Let PCheck' (c : context) (t t1 : term) :=
         [ |-[ de ] c] ->
         [c |-[ de ] t] -> PCheck c t t1 × [c |-[ de ] t1 : t].

  (** The main theorem *)
  Theorem algo_typing_discipline : ltac:(
    let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
    let ind := strong_statement t in
    exact ind).
  Proof.
    intros.
    subst PTy' PInf' PInfRed' PCheck'.
    apply AlgoTypingInduction.
    1-10: solve [intros ;
      repeat unshelve (
        match reverse goal with
          | IH : context [prod] |- _ => destruct IH ; [..|shelve] ; gen_typing
        end) ;
      now split ; [|econstructor] ; eauto].
    - intros * ? IHI ? IHC ?.
      destruct IHI as [? IHt].
      1: gen_typing.
      destruct IHC ; tea.
      1: now eapply boundary, prod_ty_inv in IHt as [].
      split ; [|econstructor] ; eauto.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHn ? IHP ? IHz ? IHs ?.
      assert [|-[de] Γ,, tNat]
        by (econstructor ; tea ; now econstructor).
      assert [Γ |-[ de ] P[tZero..]].
      {
        eapply typing_subst1.
        1: now econstructor.
        now eapply IHP.
      }
      assert [Γ |-[de] elimSuccHypTy P]
        by now eapply elimSuccHypTy_ty.
      split ; [eauto 10 |..].
      econstructor.
      + now eapply IHP.
      + now eapply IHz.
      + now eapply IHs.
      + now eapply IHn.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHe ? IHP ?.
      assert [|-[de] Γ,, tEmpty]
        by (econstructor ; tea ; now econstructor).
      split ; [eauto|..].
      econstructor.
      + now eapply IHP.
      + now eapply IHe.
    - intros * ? ihA ? ihB ?.
      edestruct ihA as []; tea.
      edestruct ihB as [].
      1: gen_typing.
      split; [eauto|now econstructor].
    - intros * ? ihA ? ihB ? iha ? ihb ?.
      edestruct ihA as []; tea.
      edestruct ihB as [].
      1: gen_typing.
      edestruct iha as []; tea.
      edestruct ihb as []; tea.
      1: now eapply typing_subst1.
      split;[eauto|now econstructor].
      (* why is that not found by eauto ? *)
      eapply X17; tea; now split.
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ihA ? ihx ? ihy ?.
      edestruct ihA as []; tea.
      assert [Γ |-[de] A] by now econstructor.
      split; [eauto|].
      econstructor; tea; [now eapply ihx | now eapply ihy].
    - intros * ? ihA ? ihx ?.
      assert [Γ |-[de] A] by now eapply ihA.
      split; [eauto|]. 
      econstructor; tea; now eapply ihx.
    - intros * ? ihA ? ihx ? ihP ? ihhr ? ihy ? ihe ?.
      assert [Γ |-[de] A] by now eapply ihA.
      assert [Γ |-[de] x : A] by now eapply ihx.
      assert [ |-[ de ] (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)] by now eapply idElimMotiveCtx.
      assert [Γ |-[de] P[tRefl A x .: x..]].
      1:{
          eapply typing_subst2; tea;[| now eapply ihP].
          cbn;rewrite 2!wk1_ren_on, 2!shift_one_eq; now econstructor.
      }
      assert [Γ |-[de] tId A x y] by now econstructor.
      split. 1:eapply X22; eauto. (* ??? *)
      econstructor; tea; [eapply ihP| eapply ihhr| eapply ihy | eapply ihe]; eauto.
    - intros * ? IH HA ?.
      destruct IH as [? IH] ; tea.
      split ; [eauto|..].
      econstructor ; tea.
      eapply subject_reduction_type, reddecl_conv in HA.
      1: eassumption.
      now boundary.
    - intros * ? IHt HA ?.
      destruct IHt as [? IHt] ; eauto.
      split ; [eauto|].
      econstructor ; tea.
      eapply algo_conv_sound in HA ; tea.
      now boundary.
  Qed.

  Definition BundledTypingInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoTypingInductionConcl PTy PInf PInfRed PCheck) in
      let t' := weak_statement t in exact t').

  Corollary BundledTypingInduction :
    ltac:(
      let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat match goal with |- prod _ _ => split end.
    all: intros * [].
    all: apply algo_typing_discipline ; assumption.
  Qed.

End BundledTyping.

Section TypingSoundness.
  Context `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}.

  Let PTy (Γ : context) (A : term) :=
    [|-[de] Γ] -> [Γ |-[de] A].
  Let PInf (Γ : context) (A t : term) :=
    [|-[de] Γ] ->
    [Γ |-[de] t : A].
  Let PCheck (Γ : context) (A t : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] t : A].

  Theorem algo_typing_sound : AlgoTypingInductionConcl PTy PInf PInf PCheck.
  Proof.
    subst PTy PInf PCheck.
    red.
    pose proof (algo_typing_discipline 
      (fun _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)) as [H' H] 
      ;
    cycle -1.
    1: repeat (split ; [
      intros ; apply H' ; tea ; match goal with H : sigT _ |- _ => destruct H | _ => idtac end ; gen_typing 
      | ..] ; clear H' ; try destruct H as [H' H]).
    1: now intros ; apply H ; gen_typing.
    all: now constructor.
  Qed.

End TypingSoundness.

Theorem bn_alg_typing_sound
  `{!TypingSubst (ta := de)}
  `{!TypeReductionComplete (ta := de)}
  `{!TypeConstructorsInj (ta := de)} :

  BundledTypingInductionConcl
    (fun Γ A => [Γ |-[de] A])
    (fun Γ A t => [Γ |-[de] t : A])
    (fun Γ A t => [Γ |-[de] t : A])
    (fun Γ A t => [Γ |-[de] t : A]).
Proof.
  red.
  prod_splitter.
  all: intros * [].
  all: match goal with H : context [al] |- _ => eapply algo_typing_sound in H end.
  all: prod_hyp_splitter.
  all: now eassumption.
Qed.

Lemma bn_typing_sound 
  `{!TypingSubst (ta := de)}
  `{!TypeReductionComplete (ta := de)}
  `{!TypeConstructorsInj (ta := de)}
  Γ t A :
  [Γ |-[bn] t : A] -> [Γ |-[de] t : A].
Proof.
  intros [???Hty?].
  econstructor ; tea.
  now eapply algo_typing_sound in Hty.
Qed.

Corollary inf_conv_decl
  `{!TypingSubst (ta := de)}
  `{!TypeReductionComplete (ta := de)}
  `{!TypeConstructorsInj (ta := de)}
  Γ t A A' :
  [Γ |-[al] t ▹ A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ |-[de] t : A'].
Proof.
  intros Ht Hconv.
  apply algo_typing_sound in Ht.
  2: boundary.
  now econstructor.
Qed.