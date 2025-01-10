(** * LogRel.AlgorithmicTypingProperties: properties of algorithmic typing. *)
From LogRel Require Import Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeConstructorsInj NeutralConvProperties.
From LogRel.Algorithmic Require Import BundledAlgorithmicTyping AlgorithmicConvProperties.

From LogRel Require Import Utils.

Import DeclarativeTypingProperties AlgorithmicTypingData BundledTypingData.

(** ** Small types are large types *)

(** In the generic instance we allow to turn any small type into a type,
while in the definition of algorithmic typing we only allow it when A is a non-canonical
type (in which case it has to be small).
So we need to show admissibility of the more general rule. *)

Lemma algo_typing_small_large
  `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)}
  Γ A :
  [Γ |-[bn] A : U] ->
  [Γ |-[bn] A].
Proof.
  enough (BundledTypingInductionConcl
    (fun _ _ => True)
    (fun Γ A t => [Γ |-[de] A ≅ U] -> [Γ |-[al] t])
    (fun Γ A t => A = U -> [Γ |-[al] t])
    (fun _ _ _ => True)) as (?&?&H&?).
  {
    intros [].
    split ; tea.
    eapply H.
    2: reflexivity.
    do 2 (econstructor ; tea).
    now eapply redty_red, red_compl_univ_r.
  }
  eapply BundledTypingInduction.
  all: try solve [
    econstructor |
    intros; econstructor; [intros Hcan; inversion Hcan| econstructor;[now econstructor|now eapply redty_red, red_compl_univ_r]]|
    intros; match goal with H : [_ |- _ ≅ _] |- _ => unshelve eapply ty_conv_inj in H; try now econstructor; now cbn in H end ].
  
  - intros * ? [IH] **; subst.
    eapply IH.
    eapply subject_reduction_type ; tea.
    boundary.
Qed.

Import BundledIntermediateData IntermediateTypingProperties.

(** ** Instance *)
(** Equipped with the equivalence of declarative and algorithmic conversion,
we easily derive our third instance. *)

Module AlgorithmicTypingProperties.
  Export BundledTypingData AlgorithmicConvProperties.

  #[local] Ltac intros_bn :=
    intros ;
    repeat match goal with | H : context [bn] |- _ => destruct H end ;
    econstructor ; try assumption.

  #[export, refine] Instance WfCtxAlgProperties
    `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)} :
    WfContextProperties (ta := bn) := {}.
  Proof.
    1-8: intros_bn.
    - now do 2 constructor.
    - constructor ; tea.
      now apply algo_typing_sound.
  Qed.

  #[export, refine] Instance WfTypeAlgProperties
    `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)} :
    WfTypeProperties (ta := bn) := {}.
  Proof.
    all: cycle -1.
    1: intros; now eapply algo_typing_small_large.
    1: intros_bn; now eapply algo_typing_wk.
    1-3: intros_bn; now econstructor.
    intros_bn; econstructor; tea; econstructor; tea; now eapply algo_conv_complete.
  Qed.

  #[export, refine] Instance TypingAlgProperties
    `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)} :
    TypingProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      + now eapply algo_typing_wk.
      + gen_typing.
    - intros_bn.
      + now econstructor.
      + constructor.
        now eapply in_ctx_wf.
    - intros_bn.
      + do 2 econstructor ; tea.
        all: now eapply (redty_red (ta := de)), red_compl_univ_r.
      + now do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea.
        2: econstructor.
        all: boundary.
    - intros * [? ? ? (?&?&[])%red_compl_prod_r] [].
      esplit ; tea.
      + do 2 econstructor ; tea.
        1: now eapply (redty_red (ta := de)).
        eapply algo_conv_complete.
        now etransitivity.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply inf_conv_decl.
    - intros_bn.
      1: now econstructor.
      now do 2 econstructor.
    - intros_bn.
      1: now econstructor.
      now do 2 econstructor.
    - intros_bn.
      + do 2 econstructor ; tea.
        now eapply (redty_red (ta := de)), red_compl_nat_r.
      + now do 2 econstructor.
    - intros_bn.
      1: econstructor ; tea.
      + econstructor ; tea.
        now eapply (redty_red (ta := de)), red_compl_nat_r.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor.
        eapply typing_subst1.
        1: eauto using inf_conv_decl.
        now eapply algo_typing_sound.
    - intros_bn.
      1: econstructor.
      gen_typing.
    - intros_bn.
      1: econstructor ; tea.
      + econstructor ; tea.
        now eapply (redty_red (ta := de)), red_compl_empty_r.
      + econstructor.
        eapply typing_subst1.
        1: eauto using inf_conv_decl.
        now eapply algo_typing_sound.
    - intros_bn.
      1: do 2 econstructor; tea.
      1,2: now eapply (redty_red (ta:=de)), red_compl_univ_r.
      gen_typing.
    - intros_bn.
      1: do 2 (econstructor; tea); now eapply algo_conv_complete.
      econstructor.
      2,3: eapply TypeRefl; refold.
      1,2: boundary.
      now eapply algo_typing_sound.
    - intros * [].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r .
      econstructor; tea.
      do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
    - intros * [].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r .
      econstructor; tea.
      1: do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
      eapply typing_subst1; tea.
      eapply TermConv; refold ; [|now symmetry].
      econstructor. eapply TermRefl.
      now eapply inf_conv_decl.
    - intros_bn.
      + econstructor; tea.
        2,3: econstructor ; tea; now eapply algo_conv_complete.
        econstructor; tea; now eapply red_compl_univ_r.
      + now do 2 econstructor.
    - intros * tyA tyx.
      pose proof tyA as ?%bn_alg_typing_sound.
      pose proof tyx as ?%bn_typing_sound.
      destruct tyA, tyx.
      do 3 (econstructor; tea); now eapply algo_conv_complete.
    - intros * tyA tyx tyP tyhr tyy tye.
      pose proof tyA as ?%bn_alg_typing_sound.
      pose proof tyx as ?%bn_typing_sound.
      pose proof tyP as ?%bn_alg_typing_sound.
      pose proof tyhr as ?%bn_typing_sound.
      pose proof tyy as ?%bn_typing_sound.
      pose proof tye as ?%bn_typing_sound.
      destruct tyA, tyx, tyP, tyhr, tyy, tye.
      econstructor; tea.
      + econstructor; tea; econstructor; tea.
        all: now eapply algo_conv_complete.
      + econstructor; eapply typing_subst2; tea.
        cbn; now rewrite 2!wk1_ren_on, 2!shift_one_eq.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      symmetry.
      eapply RedConvTyC, subject_reduction_type ; tea.
      now eapply algo_typing_sound.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
  Qed.

  #[export, refine] Instance RedTermAlgProperties
    `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)} :
    RedTermProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      2: now apply credalg_wk.
      econstructor ; tea.
      1: now eapply algo_typing_wk.
      now eapply typing_wk.
    - intros * [? []]; assumption.
    - now intros * [].
    - intros_bn.
      2: apply redalg_one_step; now constructor.
      econstructor ; tea.
      + econstructor.
        1: now do 2 econstructor.
        econstructor ; tea.
        now eapply algo_conv_complete.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply inf_conv_decl.
    - intros * HP Hz Hs.
      assert [|-[de] Γ] by (destruct Hz ; boundary).
      split ; tea.
      + eapply ty_natElim ; tea.
        econstructor ; tea.
        1: econstructor.
        now do 2 econstructor.
      + apply redalg_one_step ; now constructor.
    - intros * HP Hz Hs [].
      assert [|-[de] Γ] by (destruct Hz ; boundary).
      split ; tea.
      + eapply ty_natElim ; tea.
        econstructor.
        * eassumption.
        * do 2 econstructor ; tea.
          now eapply (redty_red (ta := de)), red_compl_nat_r.
        * now do 2 econstructor.
      + apply redalg_one_step; now constructor.
    - intros_bn.
      + eapply red_compl_prod_r in bun_inf_conv_conv0 as (?&?&[]).
        econstructor ; tea.
        1: econstructor.
        * econstructor ; tea.
          now eapply (redty_red (ta := de)).
        * econstructor ; tea.
          eapply algo_conv_complete.
          now etransitivity.
        * eapply typing_subst1 ; tea.
          econstructor.
          now eapply inf_conv_decl.  
      + now apply redalg_app.
    - intros * [] [] [] [? []].
      assert [Γ |-[al] n ▹h tNat].
      {
        econstructor ; tea.
        now eapply (redty_red (ta := de)), red_compl_nat_r.
      }
      split ; tea.
      1: econstructor ; tea.
      1: econstructor ; tea.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor.
        eapply typing_subst1.
        all: eapply algo_typing_sound ; tea.
        2: now econstructor.
        econstructor ; tea.
        now eapply algo_conv_complete.
      + now apply redalg_natElim.
    - intros * [] [?[]].
      assert [Γ |-[al] n ▹h tEmpty].
      {
        econstructor ; tea.
        now eapply (redty_red (ta := de)), red_compl_empty_r.
      }
      split ; tea.
      1: econstructor ; tea.
      1: econstructor ; tea.
      + econstructor.
        eapply typing_subst1.
        all: eapply algo_typing_sound ; tea.
        2: now econstructor.
        econstructor ; tea.
        now eapply algo_conv_complete.
      + now apply redalg_natEmpty.
    - intros_bn.
      2: econstructor; [|reflexivity]; now constructor.
      econstructor.
      1: tea.
      2: eapply TypeRefl; refold; now boundary.
      do 2 econstructor.
      1: do 2 (econstructor; tea); now eapply algo_conv_complete.
      reflexivity.
    - intros * [? []].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r.
      econstructor; tea.
      2: now apply redalg_fst.
      econstructor; tea.
      do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
    - intros_bn.
      2: econstructor; [|reflexivity]; now constructor.
      econstructor.
      1: tea.
      + do 2 econstructor.
        2: reflexivity.
        do 2 (econstructor; tea); now eapply algo_conv_complete.
      + eapply TypeRefl; eapply typing_subst1.
        2: now eapply algo_typing_sound.
        do 2 econstructor.
        * boundary.
        * now eapply algo_typing_sound.
        * now eapply inf_conv_decl.
        * now eapply inf_conv_decl.
    - intros * [? []].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r.
      econstructor; tea.
      2: now apply redalg_snd.
      econstructor; tea.
      do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
      eapply typing_subst1 ; tea.
      eapply TermRefl; eapply wfTermConv; refold; [|now symmetry].
      econstructor; now eapply inf_conv_decl.
    - intros * tyA tyx tyP tyhr tyy tyA' tyz convA convxy convxz.
      pose proof tyA as ?%bn_alg_typing_sound.
      pose proof tyx as ?%bn_typing_sound.
      pose proof tyP as ?%bn_alg_typing_sound.
      pose proof tyhr as ?%bn_typing_sound.
      pose proof tyy as ?%bn_typing_sound.
      pose proof convA as ?%bn_conv_sound.
      pose proof convxy as ?%bn_conv_sound.
      pose proof convxz as ?%bn_conv_sound.
      destruct tyA, tyx, tyP, tyhr, tyy, tyA', tyz, convA, convxy, convxz.
      econstructor; tea.
      2: eapply redalg_one_step; constructor.
      assert [Γ |-[ de ] tId A' z z ≅ tId A x y].
      1:{
        econstructor; symmetry; tea.
        1,2: econstructor; tea.
        etransitivity; tea; now symmetry.
      }
      econstructor; tea.
      + econstructor; tea; econstructor; tea.
        4: econstructor; tea; econstructor; tea.
        all: eapply algo_conv_complete; tea.
        now etransitivity.
      + econstructor; eapply typing_subst2; tea.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
        econstructor; [econstructor; tea|tea].
        now econstructor.
    - intros * tyA tyx tyP tyhr tyy [? tye].
      pose proof tyP as ?%bn_alg_typing_sound.
      pose proof tyy as ?%bn_typing_sound.
      pose proof tye as ?%bn_typing_sound.
      revert tyA tyx tyP tyhr tyy tye; intros_bn.
      2: now eapply redalg_idElim.
      econstructor; tea.
      + econstructor; tea; econstructor; tea.
        all: now eapply algo_conv_complete.
      + econstructor; eapply typing_subst2; tea.
        cbn; now rewrite 2!wk1_ren_on, 2!shift_one_eq.
    - intros_bn.
      eapply algo_conv_sound in bun_conv_ty ; tea.
      econstructor ; tea.
      now etransitivity.
    - intros_bn.
      all: now econstructor.
    - red. intros_bn.
      2: now etransitivity.
      now econstructor.
  Qed.

  #[export, refine] Instance RedTypeAlgProperties
    `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)} :
    RedTypeProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      1: now apply algo_typing_wk.
      now apply credalg_wk.
    - intros * []; assumption.
    - now intros_bn.
    - intros * [?[]%algo_typing_small_large].
      now econstructor.
    - intros_bn.
      now econstructor. 
    - red. intros_bn.
      now etransitivity.
  Qed.

  #[export] Instance AlgorithmicTypingProperties
    `{!TypingSubst (ta := de)} `{!TypeReductionComplete (ta := de)} `{!TypeConstructorsInj (ta := de)} :
    GenericTypingProperties bn _ _ _ _ _ _ _ _ _ _ := {}.

End AlgorithmicTypingProperties.

(** ** Consequences *)

Import AlgorithmicTypingProperties.

(** *** Completeness of algorithmic typing *)

Import BundledTypingData AlgorithmicTypingProperties.

From LogRel.TypingProperties Require Import LogRelConsequences.
#[local] Existing Instances TypingSubstLogRel RedCompleteLogRel TypeConstructorsInjLogRel TypingCompleteLogRel.

#[deprecated(note="use the TypingComplete class instead")]Corollary algo_typing_complete Γ A t :
  [Γ |-[de] t : A] ->
  [Γ |-[bn] t : A].
Proof.
  now eintros ?%(tm_compl (ta' := bn)).
Qed.

(** *** Uniqueness of types *)

Lemma type_uniqueness Γ A A' t :
  [Γ |-[de] t : A] ->
  [Γ |-[de] t : A'] ->
  [Γ |-[de] A ≅ A'].
Proof.
  intros [?? Hinf]%algo_typing_complete [?? Hinf']%algo_typing_complete.
  eapply algo_typing_det in Hinf.
  2: eassumption.
  subst.
  etransitivity ; tea.
  now symmetry.
Qed.