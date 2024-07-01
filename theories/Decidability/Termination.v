(** * LogRel.Decidability.Termination: the implementation always terminates on well-typed inputs. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import BasicAst Context Notations UntypedReduction Weakening DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel.Decidability Require Import Functions Soundness Completeness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.

Import DeclarativeTypingProperties.

Section ConversionTerminates.

Let PTyEq (Γ : context) (A B : term) :=
  forall v B',
  [Γ |-[de] A] × [Γ |-[de] B'] ->
  domain _conv (ty_state;Γ;v;A;B').
Let PTyRedEq (Γ : context) (A B : term) :=
  forall v B',
  isType B' ->
  [Γ |-[de] A] × [Γ |-[de] B'] ->
  domain _conv (ty_red_state;Γ;v;A;B').
Let PNeEq (Γ : context) (A t u : term) :=
  forall v u',
  whne u' ->
  well_typed (ta := de) Γ t × well_typed (ta := de) Γ u' ->
  domain _conv (ne_state;Γ;v;t;u').
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall v u',
  whne u' ->
  well_typed (ta := de) Γ t × well_typed (ta := de) Γ u' ->
  domain _conv (ne_red_state;Γ;v;t;u').
Let PTmEq (Γ : context) (A t u : term) :=
  forall u',
  [Γ |-[de] t : A] × [Γ |-[de] u' : A] ->
  domain _conv (tm_state;Γ;A;t;u').
Let PTmRedEq (Γ : context) (A t u : term) :=
  forall u',
  whnf u' ->
  [Γ |-[de] t : A] × [Γ |-[de] u' : A] ->
  domain _conv (tm_red_state;Γ;A;t;u').

Theorem _conv_terminates :
  AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  apply AlgoConvInduction.

  - intros * ?? HA IHA * [? Hconcl]%dup.
    apply compute_domain.
    simp _conv conv_ty.
    cbn.
    split.
    1: eapply wh_red_complete ; now exists istype.
    intros A'' []%red_sound.
    split.
    1: eapply wh_red_complete ; now exists istype.
    intros B'' []%red_sound.
    replace A'' with A'
      by (eapply whred_det ; tea ; eapply algo_conv_wh in HA as [] ; gen_typing).

    eapply typeConvRed_prem2, IHA in Hconcl as [] ; eauto.
    2: now eapply type_isType.
    split ; [now eexists|..].
    now intros [] ; cbn.
    
  - intros * ???? * wB' [Hconcl]%dup.
    apply compute_domain.
    simp _conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    2: now unshelve erewrite (whne_ty_view1 _) ; cbn ; cbn.
    
    eapply typePiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros Hpost0%implem_conv_graph%algo_conv_sound ; eauto.
    eapply typePiCongAlg_prem1 in Hpost0 ; eauto.

  - intros * wB' ?.
    apply compute_domain.
    simp _conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    now unshelve erewrite (whne_ty_view1 _) ; cbn ; cbn.

  - intros * wB' ?.
    apply compute_domain.
    simp _conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    now unshelve erewrite (whne_ty_view1 _) ; cbn.
  
  - intros * wB' ?.
    apply compute_domain.
    simp _conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    now unshelve erewrite (whne_ty_view1 _) ; cbn.

  - intros * ? ? ? ? * wB' [Hconcl]%dup.
    apply compute_domain.
    simp _conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    2: now unshelve erewrite (whne_ty_view1 _) ; cbn.
    
    eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros Hpost0%implem_conv_graph%algo_conv_sound ; eauto.
    eapply typeSigCongAlg_prem1 in Hpost0 ; eauto.

  - intros * ? ? ? ? ? ? * wB' [Hconcl]%dup.
    apply compute_domain.
    simp _conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    2: now unshelve erewrite (whne_ty_view1 _) ; cbn.

    eapply typeIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost0]%implem_conv_graph%algo_conv_sound%dup ; eauto.
    eapply typeIdCongAlg_prem1 in Hpost0 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros Hpost1%implem_conv_graph%algo_conv_sound ; eauto.
    eapply typeIdCongAlg_prem2 in Hpost1 ; eauto.
    
  - intros * ?? ?? * wB' [Hconcl]%dup.
    apply compute_domain.
    simp _conv conv_ty_red build_nf_ty_view2.
    destruct wB' ; cbn.
    1-6: now unshelve erewrite whne_ty_view1 ; cbn.
    do 2 (unshelve erewrite whne_ty_view1 ; tea) ; cbn.

    eapply typeNeuConvAlg_prem2 in Hconcl as [Hpre0 []]%dup ; eauto.
    now split ; [..| intros []] ; cbn.

  - intros ? n ? ? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu' as [n'| | | | | |].
    all: simp _conv conv_ne to_neutral_diag ; cbn ; try easy.
    destruct (Nat.eqb_spec n n') ; cbn.
    2: easy.
    erewrite ctx_access_complete ; tea.
    now econstructor.

  - intros * Hm ? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _conv conv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost1]%implem_conv_graph ; eauto.
    1: now eapply algo_conv_wh in Hm as [].
    eapply algo_conv_det in Hm ; tea ; subst.
    eapply algo_conv_sound, neuAppCongAlg_prem1 in Hpost1 as [[]]%dup ; eauto.
    now split ; [eauto | intros [] ; cbn].

  - intros * Hn ? ?? ?? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _conv conv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost1]%implem_conv_graph ; eauto.
    1: now eapply algo_conv_wh in Hn as [].
    eapply algo_conv_det in Hn ; tea ; subst.
    eapply algo_conv_sound in Hpost1 as [[] [Hpost1]%dup]%dup ; eauto.
    eapply neuNatElimCong_prem1 in Hpost1 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost2]%implem_conv_graph%algo_conv_sound%dup ; eauto.
    eapply neuNatElimCong_prem2 in Hpost2 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost3]%implem_conv_graph%algo_conv_sound%dup ; eauto.
    eapply neuNatElimCong_prem3 in Hpost3 ; eauto.
    now split ; [eauto | intros [] ; cbn].

  - intros * Hn ? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _conv conv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost1]%implem_conv_graph ; eauto.
    1: now eapply algo_conv_wh in Hn as [].
    eapply algo_conv_det in Hn ; tea ; subst.
    eapply algo_conv_sound in Hpost1 as [[] [Hpost1]%dup]%dup ; eauto.
    eapply neuEmptyElimCong_prem1 in Hpost1 ; eauto.
    now split ; [eauto | intros [] ; cbn].

  - intros * Hn ? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _conv conv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost1]%implem_conv_graph ; eauto.
    1: now eapply algo_conv_wh in Hn as [].
    eapply algo_conv_det in Hn ; tea ; subst.
    now cbn.
    
  - intros * Hn ? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _conv conv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost1]%implem_conv_graph ; eauto.
    1: now eapply algo_conv_wh in Hn as [].
    eapply algo_conv_det in Hn ; tea ; subst.
    now cbn.

  - intros * _ * _ * _ * Hn ? ?? ?? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _conv conv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost1]%implem_conv_graph ; eauto.
    1: now eapply algo_conv_wh in Hn as [].
    eapply algo_conv_det in Hn ; tea ; subst.
    eapply algo_conv_sound in Hpost1 as [[] [Hpost1]%dup]%dup ; eauto.
    eapply neuIdElimCong_prem1 in Hpost1 as [[]]%dup ; eauto.
    repeat erewrite <- wk1_ren_on.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost2]%implem_conv_graph%algo_conv_sound%dup ; eauto.
    eapply neuIdElimCong_prem2 in Hpost2 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros ?%implem_conv_graph%algo_conv_sound ; eauto.

  - intros * Hm ? ? ? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_ne_red ; cbn.

    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost0 []]%implem_conv_graph%algo_conv_sound%dup ; eauto.
    2: now eapply algo_conv_wh in Hm as [].
    split ; [..|easy].
    eapply wh_red_complete ; exists istype ; boundary.

  - intros * ??? []%algo_conv_wh IH * [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm ; cbn.

    split.
    1: eapply wh_red_complete ; exists istype ; boundary.
    intros A'' []%red_sound.
    split.
    1: eapply wh_red_complete ; now eexists (isterm _).
    intros t'' []%red_sound.
    split.
    1: eapply wh_red_complete ; now eexists (isterm _).
    intros u'' []%red_sound.

    replace A'' with A' in * by (now eapply whred_det ; gen_typing).
    replace t'' with t' in * by (eapply whred_det ; eassumption).

    eapply termConvRed_prem3 in Hconcl ; eauto.
    now split ; [..| intros [] ; cbn].

  - intros * ?? ?? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite (whne_ty_view1 _) ; cbn.

    eapply termPiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros Hpost0%implem_conv_graph%algo_conv_sound ; eauto.
    eapply termPiCongAlg_prem1 in Hpost0 ; eauto.

  - intros * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    now unshelve erewrite (whne_ty_view1 _) ; cbn.

  - intros * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply nat_isNat in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    now unshelve erewrite (whne_nf_view1 _) ; cbn.

  - intros * ?? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply nat_isNat in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite (whne_nf_view1 _) ; cbn.

    eapply termSuccCongAlg_prem0 in Hconcl ; eauto.

  - intros * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    now unshelve erewrite (whne_ty_view1 _) ; cbn.

  - intros * ?? ?? ? wu' [Hconcl]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 ; cbn.

    now eapply termFunConvAlg_prem2 in Hconcl.

  - intros * ?? ?? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite (whne_ty_view1 _) ; cbn.

    eapply termSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros Hpost0%implem_conv_graph%algo_conv_sound ; eauto.
    eapply termSigCongAlg_prem1 in Hpost0 ; eauto.

  - intros * ?? ?? ?? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3.

    eapply termPairConvAlg_prem2 in Hconcl as [Hpre2 []]%dup ; tea.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost2]%implem_conv_graph%algo_conv_sound%dup ; eauto.
    eapply termPairConvAlg_prem3 in Hpost2 ; eauto.

  - intros * ?? ?? ?? ? wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite (whne_ty_view1 _) ; cbn.

    eapply termIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost0]%implem_conv_graph%algo_conv_sound%dup ; eauto.
    eapply termIdCongAlg_prem1 in Hpost0 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros Hpost1%implem_conv_graph%algo_conv_sound ; eauto.
    eapply termIdCongAlg_prem2 in Hpost1 ; eauto.

  - intros * _ * _ * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply id_isId in wu' ; tea.
    destruct wu' as [|(?&?&->)] ; cbn ; try exact I.
    now unshelve erewrite (whne_nf_view1 _) ; cbn.

  - intros * Hm IH Hpos ? wu' [Hconcl []]%dup. 
    apply compute_domain.
    simp _conv conv_tm_red build_nf_view3.
    eapply algo_conv_wh in Hm as [].
    destruct Hpos as [[]| | | |].
    + eapply Uterm_isType in wu' ; tea.
      cbn ; simp build_nf_ty_view2.
      unshelve erewrite whne_ty_view1 ; tea.
      destruct wu' ; try solve [cbn ; easy].
      unshelve erewrite whne_ty_view1 ; tea.
      cbn.
      split ; [..|now intros [] ; cbn].
      eapply IH ; tea.
      split ; now eexists.
    + eapply nat_isNat in wu' ; tea.
      cbn ; simp build_nf_view3.
      unshelve erewrite whne_nf_view1 ; tea.
      destruct wu' ; try solve [cbn ; easy].
      unshelve erewrite whne_nf_view1 ; tea.
      cbn.
      split ; [..|now intros [] ; cbn].
      eapply IH ; tea.
      split ; now eexists.
    + eapply empty_isEmpty in wu' ; tea.
      cbn ; simp build_nf_view3.
      unshelve erewrite whne_nf_view1 ; tea.
      unshelve erewrite whne_nf_view1 ; tea.
      cbn.
      split ; [..|now intros [] ; cbn].
      eapply IH ; tea.
      split ; now eexists.
    + eapply id_isId in wu' ; tea.
      cbn ; simp build_nf_view3.
      unshelve erewrite whne_nf_view1 ; tea.
      destruct wu' as [|(?&?&->)]; try solve [cbn ; easy].
      unshelve erewrite whne_nf_view1 ; tea.
      cbn.
      split ; [..|now intros [] ; cbn].
      eapply IH ; tea.
      split ; now eexists.
    + eapply neutral_isNeutral in wu' ; tea.
      unshelve erewrite whne_ty_view1 ; tea.
      cbn ; simp build_nf_view3.
      do 2 (unshelve erewrite whne_nf_view1 ; tea) ; cbn.
      split ; [..|now intros [] ; cbn].
      eapply IH ; tea.
      split ; now eexists.
  Qed.
  
  Corollary tconv_terminates Γ A A' :
    [Γ |-[de] A] ->
    [Γ |-[de] A'] ->
    domain tconv (Γ,A,A').
  Proof.
    intros.
    assert (domain _conv (ty_state; Γ; tt; A; A')) as [].
    {
      eapply _conv_terminates ; eauto.
      eapply algo_conv_complete.
      econstructor.
      boundary.
    }
    eexists.
    unfold graph.
    simp tconv.
    econstructor ; cbn in * ; tea.
    now constructor.
  Qed.

End ConversionTerminates.

Section TypingTerminates.

  Import AlgorithmicTypingData.

  Variable conv : (context × term × term) ⇀ exn errors unit.

  Hypothesis conv_sound : forall Γ T V,
    graph conv (Γ,T,V) ok ->
    [Γ |-[al] T ≅ V].

  Hypothesis conv_terminates : forall Γ A A',
    [Γ |-[de] A] ->
    [Γ |-[de] A'] ->
    domain conv (Γ,A,A').

  Definition lt_state (s s' : typing_state) :=
    match s, s' with
    | inf_state, inf_state => False
    | inf_state, _ => True
    | inf_red_state, wf_ty_state => True
    | _, _ => False
    end.

  Lemma well_founded_lt_state : well_founded lt_state.
  Proof.
    all: repeat (constructor ; intros [] ; cbn ; try auto).
  Qed.

  #[local]Definition R_aux := lexprod term typing_state term_subterm lt_state.

  #[local]Definition R (x y : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term) :=
    R_aux
      (Datatypes.pair (x.π2.π2.π2) x.π1)
      (Datatypes.pair (y.π2.π2.π2) y.π1).
  
  #[local]Lemma R_acc : well_founded R.
  Proof.
    intros x.
    unfold R, R_aux.
    constructor.
    intros y h.
    eapply acc_A_B_lexprod in h.
  - remember (Datatypes.pair ((y.π2).π2).π2 y.π1) as y' eqn:e.
    induction h as [y'' h ih] in y, e |- *. subst.
    constructor. intros [v ρ] hr.
    eapply ih. 2: reflexivity.
    assumption.
  - eapply well_founded_term_subterm.
  - apply well_founded_lt_state.
  - apply well_founded_lt_state. 
  Qed.

Definition wf_input (s : typing_state) Γ : tstate_input s -> Type :=
  match s with
  | check_state => fun A => [Γ |-[de] A]
  | _ => fun _ => True
  end.

Theorem typing_terminates (s : typing_state) (Γ : context) (v : tstate_input s) (t : term) :
  [|-[de] Γ] ->
  wf_input s Γ v ->
  domain (typing conv) (s;Γ;v;t).
Proof.
  intros HΓ Hv.
  set (x := (s;Γ;v;t)).
  change s with (x.π1) in Hv.
  change Γ with (x.π2.π1) in HΓ, Hv.
  change v with (x.π2.π2.π1) in Hv.
  pose proof (Hacc := R_acc x).
  clearbody x.
  clear s Γ v t.
  induction Hacc as [x H IH] in HΓ, Hv |- * ; cbn in *.
  apply compute_domain. funelim_typing ; cbn in *; try easy.
  all: match goal with 
      | H : (_;_;_) = (_;_;_) |- _ => injection H; clear H; intros; subst
  end.

  - split.
    + apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    + intros [[]|] ; cbn ; try easy.
      intros ?%implem_typing_sound%algo_typing_sound ; tea.
      split ; cbn.
      2: now intros [[]|] ; cbn.
      apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      econstructor ; tea.
      econstructor.
      now destruct s.
  - split.
    + apply IH ; cbn ; try easy.
     left ; cbn ; now do 2 econstructor.
    + intros [|] ; cbn ; try easy.
      intros ?%implem_typing_sound%algo_typing_sound ; tea.
      split.
      2: intros [] ; now cbn.
      apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      now econstructor.
  - split.
    + apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    + intros [[]|] ; cbn ; try easy.
      intros Hf%implem_typing_sound%algo_typing_sound ; tea.
      split.
      2: intros [] ; now cbn.
      apply IH ; cbn ; tea.
      1: left ; cbn ; now do 2 econstructor.
      eapply prod_ty_inv.
      boundary.
  - split.
    + apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    + intros [[]|] ; now cbn.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [[]|] ; cbn ; try easy.
    intros Hn%implem_typing_sound%algo_typing_sound ; tea.
    set (Γ' := _ ,, tNat).
    assert ([|-[de] Γ']) by (now econstructor ; [|econstructor]). 
    split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [|] ; cbn ; [|easy].
    intros ?%implem_typing_sound%algo_typing_sound ; tea.
    split.
    2: intros [|] ; cbn ; intros _ ; split; [|intros []] ; try (cbn ; easy).
    + apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      eapply typing_subst1 ; tea.
      now econstructor.
    + apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      now eapply elimSuccHypTy_ty.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [[]|] ; cbn ; try easy.
    intros Hn%implem_typing_sound%algo_typing_sound ; tea.
    set (Γ' := _ ,, tEmpty).
    assert ([|-[de] Γ']) by (now econstructor ; [|econstructor]). 
    split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [|] ; now cbn.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros Hn%implem_typing_sound%algo_typing_sound ; tea; split.
    set (Γ' := _ ,, _); assert [|-[de] Γ'] by (econstructor; tea; destruct s; now econstructor).
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros HA%implem_typing_sound%algo_typing_sound ; tea.
    set (Γ' := _ ,, _); assert [|-[de] Γ'] by (econstructor; tea; destruct s; now econstructor).
    split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros HB%implem_typing_sound%algo_typing_sound ; tea; split.
    1: apply IH ; cbn ; tea; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros Ha%implem_typing_sound%algo_typing_sound ; tea; split.
    match goal with
    | _ : [ ?Γ |-[de] _ : _] |- _ => assert [Γ|-[de] B[a..]] by now eapply typing_subst1
    end.
    1: apply IH ; cbn ; tea; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split; cycle -1.
    1: intros [t|]; cbn; [|easy]; intros hA%implem_typing_sound%algo_typing_sound; tea.
    1: destruct t; cbn; try easy.
    1: assert [Γ0 |-[de] A] by (destruct s; now econstructor).
    1: split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hx%implem_typing_sound%algo_typing_sound; tea.
    1: split; cycle -1.
    1: intros [|]; cbn; easy.
    all: eapply IH; cbn; tea; try easy.
    all: left; cbn; do 2 constructor.
  - split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hA%implem_typing_sound%algo_typing_sound; tea.
    1: split; cycle -1.
    1: intros [|]; cbn; easy.
    all: eapply IH; cbn; tea; try easy.
    all: left; cbn; do 2 constructor.
  - split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hA%implem_typing_sound%algo_typing_sound; tea.
    1: split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hx%implem_typing_sound%algo_typing_sound; tea.
    1: rewrite <- !(Weakening.wk1_ren_on Γ0 A).
    1: assert [ |-[ de ] (Γ0,, A),, tId A⟨@Weakening.wk1 Γ0 A⟩ x⟨@Weakening.wk1 Γ0 A⟩ (tRel 0)]
      by now eapply idElimMotiveCtx.
    1: split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hP%implem_typing_sound%algo_typing_sound; tea.
    1: assert [Γ0 |-[ de ] P[tRefl A x .: x..]].
    1:{ 
      eapply typing_subst2; tea; cbn.
      rewrite 2!Weakening.wk1_ren_on, 2!shift_subst_eq.
      now econstructor.
    }
    1: split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hhr%implem_typing_sound%algo_typing_sound; tea.
    1: split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hy%implem_typing_sound%algo_typing_sound; tea.
    1: assert [Γ0 |-[ de ] tId A x y] by now econstructor.
    1: split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros he%implem_typing_sound%algo_typing_sound; tea.
    1: split; cycle -1.
    all: eapply IH; cbn; tea; try easy; left; cbn; do 2 constructor.
  - split.
    + apply IH ; cbn ; try easy.
      1: now right ; cbn.
    + intros [|] ; cbn ; [|easy].
      intros ?%implem_typing_sound%algo_typing_sound ; cbn in * ; tea.
      split.
      2: easy.
      eapply conv_terminates ; tea.
      boundary.
  - split.
    + apply IH ; cbn ; try easy.
      right; now cbn.
    + intros [|] ; cbn ; [|easy].
      intros ?%implem_typing_sound%algo_typing_sound ; cbn in * ; tea.
      split.
      2: easy.
      eapply wh_red_complete.
      exists istype.
      now boundary.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [|] ; cbn ; try easy.
    intros ?%implem_typing_sound%algo_typing_sound ; tea.
    split.
    2: intros []; now cbn.
    apply IH ; cbn ; try easy.
    1: left ; cbn ; now do 2 econstructor.
    now econstructor.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [|] ; cbn ; try easy.
    intros ?%implem_typing_sound%algo_typing_sound ; tea.
    split.
    2: intros []; now cbn.
    apply IH ; cbn ; try easy.
    1: left ; cbn ; now do 2 econstructor.
    now econstructor.
  - split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hA%implem_typing_sound%algo_typing_sound; tea.
    1: split; cycle -1.
    1: intros [|]; cbn; [|easy]; intros hx%implem_typing_sound%algo_typing_sound; tea.
    1: split; [|easy].
    all: eapply IH; cbn; tea; try easy.
    all: left; do 2 constructor.
  - split; cycle -1.
    1: intros [t|]; cbn; [|easy]; intros hA%implem_typing_sound%algo_typing_sound; tea.
    1: destruct t; cbn; try easy.
    eapply IH; cbn; tea; try easy; right; now cbn.
Qed.

End TypingTerminates.