(** * LogRel.Decidability.UntypedTermination: the implementation always terminates on well-typed inputs. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import BasicAst Context Notations UntypedReduction Weakening DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel Require Import UntypedAlgorithmicConversion.
From LogRel Require Import Utils. (* at the end, to get the right easy tactic… *)
From LogRel.Decidability Require Import Functions UntypedFunctions Soundness UntypedSoundness Completeness UntypedCompleteness.
From PartialFun Require Import Monad PartialFun MonadExn.

Import DeclarativeTypingProperties AlgorithmicTypingData.

Set Universe Polymorphism.


Lemma uconv_sound_decl :
  UAlgoConvInductionConcl
    (fun t u => 
      (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[de] t ≅ u]) ×
      (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[de] t ≅ u : A]))

    (fun t u =>
      (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[de] t ≅ u]) ×
      (forall Γ A, isType A -> [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[de] t ≅ u : A]))

    (fun t u =>
      forall Γ, well_typed Γ t × well_typed Γ u ->
      ∑ A'', [Γ |-[de] t ≅ u : A'']).
Proof.
  split ; [..|split].
  all: intros t u Hconv.
  1-2: split.
  - intros * [].
    eapply uconv_sound in Hconv as [?%algo_conv_sound _]; eauto.
  - intros * [].
    eapply uconv_sound in Hconv as [_ ?%algo_conv_sound]; eauto.
  - intros * [].
    eapply uconv_sound in Hconv as [?%algo_conv_sound _]; eauto. 
  - intros * ? [].
    eapply uconv_sound in Hconv as [_ ?%algo_conv_sound]; eauto.
  - intros * [].
    eapply uconv_sound in Hconv as [? []%algo_conv_sound] ; eauto.
Qed.


#[universes(polymorphic)]Definition uconv_str_type
    (x : uconv_state × term × term)
    (r : exn errors unit) : Type :=
  match x,r with
  | (s,t,u), success _ =>
      forall (Γ Δ : context) (ρ : Δ ≤ Γ) t' u',
      t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ -> graph _uconv (s,t',u') ok
  | (s,t,u), exception e => 
    forall (Γ Δ : context) (ρ : Δ ≤ Γ) t' u',
    t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ -> ∑ e', graph _uconv (s,t',u') (exception e')
  end.

Lemma wh_red_str (Γ Δ : context) (ρ : Δ ≤ Γ) t v :
  graph wh_red t⟨ρ⟩ v ->
  ∑ v', v = v'⟨ρ⟩ × graph wh_red t v'.
Proof.
Admitted.

Lemma _uconv_str :
  funrect _uconv (fun _ => True) uconv_str_type.
Proof.
Admitted.

Lemma uconv_expand_ne_eta n n' :
  whne n ->
  whne n' ->
  domain _uconv (tm_state, eta_expand n, eta_expand n') ->
  domain _uconv (ne_state, n, n').
Proof.
  intros w w' [v g].
  unfold graph in g.
  simp _uconv uconv_tm in g ; cbn in g.
  apply (orec_graph_call_inv _uconv) in g as [? [red g]] ; cbn in *.
  eapply red_sound in red as [<-%red_whne _].
  2: now constructor ; apply whne_ren.
  apply (orec_graph_call_inv _uconv) in g as [? [red g]] ; cbn in *.
  eapply red_sound in red as [<-%red_whne _].
  2: now constructor ; apply whne_ren.
  apply (orec_graph_rec_inv _uconv) in g as [? [g _]] ; cbn in *.
  simp _uconv uconv_tm_red in g.
  apply (orec_graph_rec_inv _uconv) in g as [? [g _]] ; cbn in *.
  simp _uconv uconv_ne to_neutral_diag in g ; cbn in *.
  apply (orec_graph_rec_inv _uconv) in g as [r [g _]] ; cbn in *.
  unshelve eapply funrect_graph in g.
  4: apply _uconv_str.
  2: now cbn.
  cbn in g.
  destruct r.
  - eexists.
    eapply g.
    all: unshelve erewrite <- wk1_ren_on ; try reflexivity.
    1: exact ε.
    exact (tRel 0).
  - edestruct g ; cycle -1.
    now eexists.
    all: unshelve erewrite <- wk1_ren_on ; try reflexivity.
    1: exact ε.
    exact (tRel 0).
Qed.

Lemma uconv_expand_ne_fst n n' :
    whne n ->
    whne n' ->
    domain _uconv (tm_state, tFst n, tFst n') ->
    domain _uconv (ne_state, n, n').
  Proof.
    intros w w' [v g].
    unfold graph in g.
    simp _uconv uconv_tm in g ; cbn in g.
    apply (orec_graph_call_inv _uconv) in g as [? [red g]] ; cbn in *.
    eapply red_sound in red as [<-%red_whne _].
    2: now constructor.
    apply (orec_graph_call_inv _uconv) in g as [? [red g]] ; cbn in *.
    eapply red_sound in red as [<-%red_whne _].
    2: now constructor.
    apply (orec_graph_rec_inv _uconv) in g as [? [g _]] ; cbn in *.
    simp _uconv uconv_tm_red in g.
    apply (orec_graph_rec_inv _uconv) in g as [? [g _]] ; cbn in *.
    simp _uconv uconv_ne to_neutral_diag in g ; cbn in *.
    apply (orec_graph_rec_inv _uconv) in g as [r [g _]] ; cbn in *.
    now eexists.
Qed.

Lemma uconv_expand Γ A t t' B u u':
    [Γ |- t : A] ->
    [t ⤳* t'] ->
    [Γ |- u : B] ->
    [u ⤳* u'] ->
    domain _uconv (tm_state, t, u) ->
    domain _uconv (tm_state, t', u').
  Proof.
    intros ? [red ?]%dup ? [red' ?]%dup [v g] ; refold.
    unfold graph in g.
    simp _uconv uconv_tm in g ; cbn in g.
    apply (orec_graph_call_inv _uconv) in g as [? [[? w]%red_sound g]] ; cbn in *.
    apply (orec_graph_call_inv _uconv) in g as [? [[? w']%red_sound g]] ; cbn in *.
    apply (orec_graph_rec_inv _uconv) in g as [? [g _]] ; cbn in *.
    eapply whred_red_det in red, red' ; cycle -1 ; tea.
    apply compute_domain.
    simp _uconv uconv_tm ; cbn.
    split.
    1:{
      eexists ; cbn.
      eapply wh_red_complete_whnf_tm ; tea.
      now eapply subject_reduction_raw.
    }
    intros ? [ ]%red_sound.
    eapply whred_det in red ; tea ; subst.
    split.
    1:{
      eexists ; cbn.
      eapply wh_red_complete_whnf_tm ; tea.
      now eapply subject_reduction_raw.
    }
    intros ? [ ]%red_sound.
    eapply whred_det in red' ; tea ; subst.
    split.
    2: easy.
    now eexists.
Qed.

Import DeclarativeTypingProperties.

Section ConversionTerminates.


Let PTyEq (Γ : context) (A B : term) :=
  forall B',
  [Γ |-[de] A] × [Γ |-[de] B'] ->
  domain _uconv (tm_state,A,B').
Let PTyRedEq (Γ : context) (A B : term) :=
  forall B',
  isType B' ->
  [Γ |-[de] A] × [Γ |-[de] B'] ->
  domain _uconv (tm_red_state,A,B').
Let PNeEq (Γ : context) (A t u : term) :=
  forall u',
  whne u' ->
  well_typed (ta := de) Γ t × well_typed (ta := de) Γ u' ->
  domain _uconv (ne_state,t,u').
Let PTmEq (Γ : context) (A t u : term) :=
  forall u',
  [Γ |-[de] t : A] × [Γ |-[de] u' : A] ->
  domain _uconv (tm_state,t,u').
Let PTmRedEq (Γ : context) (A t u : term) :=
  forall u',
  whnf u' ->
  [Γ |-[de] t : A] × [Γ |-[de] u' : A] ->
  domain _uconv (tm_red_state,t,u').

Ltac split_tm :=
  split ;
  [ intros * ? [Hz%type_isType Hz'%type_isType] ;
    [solve [inversion Hz ; inv_whne | inversion Hz' ; inv_whne] | ..] ; solve [ now constructor | now apply isType_whnf]
  |..].

Theorem _uconv_terminates :
  AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PTmEq PTmRedEq.
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
    simp _uconv uconv_tm_red.
    destruct wB'.
    all: simp build_nf_view2 ; cbn ; try easy.
    2: now unshelve erewrite whne_nf_view1 ; cbn.
    
    eapply typePiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost0 _]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply typePiCongAlg_prem1 in Hpost0 ; eauto.

  - intros * wB' ?.
    apply compute_domain.
    simp _uconv uconv_tm_red.
    destruct wB'.
    all: simp build_nf_view2 ; cbn ; try easy.
    now unshelve erewrite whne_nf_view1 ; cbn.

  - intros * wB' ?.
    apply compute_domain.
    simp _uconv uconv_tm_red.
    destruct wB'.
    all: simp build_nf_view2 ; cbn ; try easy.
    now unshelve erewrite whne_nf_view1 ; cbn.
  
  - intros * wB' ?.
    apply compute_domain.
    simp _uconv uconv_tm_red.
    destruct wB'.
    all: simp build_nf_view2 ; cbn ; try easy.
    now unshelve erewrite whne_nf_view1 ; cbn.

  - intros * ? ? ? ? * wB' [Hconcl]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red.
    destruct wB'.
    all: simp build_nf_view2 ; cbn ; try easy.
    2: now unshelve erewrite whne_nf_view1 ; cbn.
    
    eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [Hpost0 _]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply typeSigCongAlg_prem1 in Hpost0 ; eauto.

  - intros * ? ? ? ? ? ? * wB' [Hconcl]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red.
    destruct wB'.
    all: simp build_nf_view2 ; cbn ; try easy.
    2: now unshelve erewrite whne_nf_view1 ; cbn.

    eapply typeIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [[Hpost0]%dup _]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply typeIdCongAlg_prem1 in Hpost0 as [[] Hpre1]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [_ Hpost1]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply typeIdCongAlg_prem2 in Hpost1 ; eauto.
    
  - intros * ?? ?? * wB' [Hconcl]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    destruct wB' ; cbn.
    1-6: now unshelve erewrite whne_nf_view1 ; cbn.
    do 2 (unshelve erewrite whne_nf_view1 ; tea ; cbn).

    eapply typeNeuConvAlg_prem2 in Hconcl as [Hpre0 []]%dup ; eauto.

  - intros ? n ? ? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu' as [n'| | | | | |].
    all: simp _uconv uconv_ne to_neutral_diag ; cbn ; try easy.
    now destruct (Nat.eqb_spec n n') ; cbn.

  - intros * Hm ? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _uconv uconv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    inversion Hm as [????? Hm'] ; refold ; subst.
    eintros [? Hpost1]%implem_uconv_graph%uconv_sound ; eauto.
    eapply algo_conv_det in Hm' ; tea ; subst.
    eapply neuConvRed in Hpost1 ; refold ; tea. 
    eapply algo_conv_sound, neuAppCongAlg_prem1 in Hpost1 ; eauto.

  - intros * Hn ? ?? ?? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _uconv uconv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    inversion Hn as [????? Hm'] ; refold ; subst.
    eintros [? Hpost1]%implem_uconv_graph%uconv_sound ; eauto.
    eapply algo_conv_det in Hm' ; tea ; subst.
    eapply neuConvRed in Hpost1 ; refold ; tea. 
    eapply algo_conv_sound in Hpost1 as [[] [Hpost1]%dup]%dup ; eauto.
    eapply neuNatElimCong_prem1 in Hpost1 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [[Hpost2]%dup _]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply neuNatElimCong_prem2 in Hpost2 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [_ [Hpost3]%dup]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply neuNatElimCong_prem3 in Hpost3 ; eauto.

  - intros * Hn ? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _uconv uconv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    inversion Hn as [????? Hm'] ; refold ; subst.
    eintros [? Hpost1]%implem_uconv_graph%uconv_sound ; eauto.
    eapply algo_conv_det in Hm' ; tea ; subst.
    eapply neuConvRed in Hpost1 ; refold ; tea. 
    eapply algo_conv_sound in Hpost1 as [[] [Hpost1]%dup]%dup ; eauto.
    eapply neuEmptyElimCong_prem1 in Hpost1 ; eauto.

  - intros * Hn ? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _uconv uconv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuFstCongAlg_prem0 in Hconcl ; eauto.
    
  - intros * Hn ? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _uconv uconv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuSndCongAlg_prem0 in Hconcl ; eauto.

  - intros * _ * _ * _ * He ?? ?? ?? * wu' [Hconcl]%dup.
    apply compute_domain.
    destruct wu'.
    all: simp _uconv uconv_ne to_neutral_diag ; cbn; try exact I.

    eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    inversion He as [????? He'] ; refold ; subst.
    eintros [? Hpost1]%implem_uconv_graph%uconv_sound ; eauto.
    eapply algo_conv_det in He' ; tea ; subst.
    eapply neuConvRed in Hpost1 ; refold ; tea. 
    eapply algo_conv_sound in Hpost1 as [[] [Hpost1]%dup]%dup ; eauto.
    eapply neuIdElimCong_prem1 in Hpost1 as [[]]%dup ; eauto.
    repeat erewrite <- wk1_ren_on.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [[Hpost2]%dup _]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply neuIdElimCong_prem2 in Hpost2 ; eauto.

  - eauto.

  - intros * ??? []%algo_conv_wh IH * [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm ; cbn.

    split.
    1: eapply wh_red_complete ; now eexists (isterm _).
    intros t'' []%red_sound.
    split.
    1: eapply wh_red_complete ; now eexists (isterm _).
    intros u'' []%red_sound.

    replace t'' with t' in * by (eapply whred_det ; eassumption).

    eapply termConvRed_prem3 in Hconcl ; eauto.

  - intros * ?? ?? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite whne_nf_view1 ; cbn.

    eapply termPiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [_ Hpost0]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply termPiCongAlg_prem1 in Hpost0 ; eauto.

  - intros * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    now unshelve erewrite whne_nf_view1 ; cbn.

  - intros * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply nat_isNat in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    now unshelve erewrite whne_nf_view1 ; cbn.

  - intros * ?? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply nat_isNat in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite whne_nf_view1 ; cbn.

    eapply termSuccCongAlg_prem0 in Hconcl ; eauto.

  - intros * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    now unshelve erewrite whne_nf_view1 ; cbn.

  - intros * w _ ? IH ? w' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    eapply fun_isFun in w, w' ; eauto.
    destruct w, w'.

    + eapply LamCongUAlg_prem0 in Hconcl as (?&?&[[=<-<-]]).
      2: now constructor.
      cbn ; split ; [..|easy].
      eapply uconv_expand ; [..|eapply IH ; split] ; eauto.
      all: try solve [now eapply typing_eta'].
      2: reflexivity.
      now eapply redalg_one_step, eta_expand_beta.

    + eapply LamNeUAlg_prem0 in Hconcl as (?&?&[[=<-<-]]).
      2: now constructor.
      cbn.
      unshelve (erewrite whne_nf_view1) ; tea ; cbn.
      split ; [..|easy].
      eapply uconv_expand ; [..|eapply IH ; split] ; eauto.
      all: try solve [now eapply typing_eta'].
      * eapply redalg_one_step, eta_expand_beta.
      * reflexivity.

    + eapply NeLamUAlg_prem0 in Hconcl as (?&?&[[=<-<-]]).
      2: now constructor.
      cbn.
      unshelve (erewrite whne_nf_view1) ; tea ; cbn.
      split ; [..|easy].
      eapply IH ; split ; eauto.

    + unshelve erewrite whne_nf_view1 ; tea ; cbn.
      unshelve erewrite whne_nf_view1 ; tea ; cbn.
      split ; [..|easy].
      apply uconv_expand_ne_eta ; tea.
      eapply IH.
      split.
      all: now eapply typing_eta'.

  - intros * ?? ?? * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite whne_nf_view1 ; cbn.

    eapply termSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [_ Hpost0]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply termSigCongAlg_prem1 in Hpost0 ; eauto.

  - intros ? t u A'' B'' w _ ? IHf ? IHs * w' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2 ; cbn.
    eapply sig_isPair in w, w' ; tea.
    destruct w, w'.

    + cbn.
      eapply PairCongUAlg_prem0 in Hconcl as (?&?&[[=<-<-] [[]]%dup]).
      2: now constructor.
      cbn.
      split.
      1:{
        eapply uconv_expand, IHf ; try reflexivity ; [..|split] ; eauto.
        2: eapply redalg_one_step ; econstructor.
        all: now econstructor.
      }

      intros [] ; cbn ; [|easy].
      intros [_ Hpost1]%implem_uconv_graph%uconv_sound_decl ; eauto.
      eapply PairCongUAlg_prem1 in Hpost1 as [] ; eauto.
      split ; [..|easy].
      eapply uconv_expand, IHs ; try reflexivity ; [..|split] ; eauto.
      2: eapply redalg_one_step ; econstructor.
      all: now econstructor.

    + cbn.
      eapply PairNeUAlg_prem0 in Hconcl as (?&?&[[=<-<-] [[]]%dup]).
      2: now constructor.
      unshelve erewrite whne_nf_view1 ; tea ; cbn.
      split.
      1:{
        eapply uconv_expand, IHf ; try reflexivity ; [..|split] ; eauto.
        2: eapply redalg_one_step ; econstructor.
        all: now econstructor.
      }

      intros [] ; cbn ; [|easy].
      intros [_ Hpost1]%implem_uconv_graph%uconv_sound_decl ; eauto.
      eapply PairNeUAlg_prem1 in Hpost1 as [] ; eauto.
      split ; [..|easy].
      eapply uconv_expand, IHs ; try reflexivity ; [..|split] ; eauto.
      2: eapply redalg_one_step ; econstructor.
      all: now econstructor.

    + cbn.
      eapply NePairUAlg_prem0 in Hconcl as (?&?&[[=<-<-] [[]]%dup]).
      2: now constructor.
      unshelve erewrite whne_nf_view1 ; tea ; cbn.
      split.
      1: now eapply uconv_expand, IHf ; try reflexivity ; [..|split].

      intros [] ; cbn ; [|easy].
      intros [_ Hpost1]%implem_uconv_graph%uconv_sound_decl ; eauto.
      eapply NePairUAlg_prem1 in Hpost1 as [] ; eauto.

    + cbn.
      do 2 (unshelve erewrite whne_nf_view1 ; tea ; cbn).
      split ; [..|easy].
      eapply uconv_expand_ne_fst ; tea.
      apply IHf.
      split ; now econstructor.

  - intros * ?? ?? ?? ? wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' ; cbn ; try exact I.
    2: now unshelve erewrite whne_nf_view1 ; cbn.

    eapply termIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [_ [Hpost0]%dup]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply termIdCongAlg_prem1 in Hpost0 as [[]]%dup ; eauto.
    split ; [eauto | intros [] ; cbn ; [|easy]].

    intros [_ Hpost1]%implem_uconv_graph%uconv_sound_decl ; eauto.
    eapply termIdCongAlg_prem2 in Hpost1 ; eauto.

  - intros * _ * _ * wu' [Hconcl []]%dup.
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    eapply id_isId in wu' ; tea.
    destruct wu' as [|(?&?&->)] ; cbn ; try exact I.
    now unshelve erewrite whne_nf_view1 ; cbn.

  - intros * []%algo_conv_wh IH Hpos ? wu' [Hconcl [? Hty]]%dup. 
    apply compute_domain.
    simp _uconv uconv_tm_red build_nf_view2.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    destruct wu' ; cbn ; try easy.
    + eapply termGen' in Hty as (?&[? [->]]&Hconv).
      eapply red_ty_compl_prod_l' in Hconv as (?&?&[->]).
      2: gen_typing.
      inversion Hpos.
      inv_whne.
    + eapply termGen' in Hty as (?&[->]&Hconv).
      eapply red_ty_compl_sig_l' in Hconv as (?&?&[->]).
      2: gen_typing.
      inversion Hpos.
      inv_whne.
    + unshelve erewrite whne_nf_view1 ; tea ; cbn.
      split ; [..|easy].
      eapply IH ; tea.
      split ; now eexists.
 
Qed.