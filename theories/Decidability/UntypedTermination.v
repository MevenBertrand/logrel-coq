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

Section GraphInversion.

  Context {I} `{CT : CallTypes I} `{!CallableProps CT} {A B} (f : ∇ (x : A), I ⇒ B x).

  Definition orec_graph'
    {a} (o : orec I A B (B a)) (b : B a) : Prop :=
    match o with
    | _ret x => x = b
    | _rec x κ => exists v, orec_graph f (f x) v /\ orec_graph f (κ v) b
    | _call i x κ => exists v, cp_graph i x v /\ orec_graph f (κ v) b
    | undefined => False
    end.

  Definition orec_graph_from {a} {o : orec I A B (B a)} {b}
    (e : orec_graph f o b) : orec_graph' o b :=
      match e with
      | ret_graph _ _ => eq_refl 
      | rec_graph _ _ _ v _ h h' =>
          ex_intro _ v (conj h h')
      | call_graph _ _ _ _ v _ h h' =>
          ex_intro _ v (conj h h')
      end.

  Import EqNotations.

  Definition orec_graph_to {a} {o : orec I A B (B a)} {b} :
    orec_graph' o b -> orec_graph f o b :=
      match o with
      | _ret x => fun e => rew e in ret_graph _ _
      | _rec x κ => fun '(ex_intro _ v (conj h h')) =>
          rec_graph _ _ _ v _ h h'
      | _call i x κ => fun '(ex_intro _ v (conj h h')) =>
          call_graph _ _ _ _ v _ h h'
      | undefined => fun f => False_rect _ f
      end.

  Lemma orec_graph_equiv {a} {o : orec I A B (B a)} {b} :
  orec_graph f o b <-> orec_graph' o b.
  Proof.
    split.
    - apply orec_graph_from.
    - apply orec_graph_to.
  Qed.

End GraphInversion.

Section AlgoStr.

  Definition dest_entry_rename (ρ : nat -> nat) (d : dest_entry) : dest_entry :=
    match d with
    | eEmptyElim P => eEmptyElim P⟨upRen_term_term ρ⟩
    | eNatElim P hs hz => eNatElim P⟨upRen_term_term ρ⟩ hs⟨ρ⟩ hz⟨ρ⟩
    | eApp u => eApp u⟨ρ⟩
    | eFst => eFst
    | eSnd => eSnd
    | eIdElim A x P hr y => eIdElim A⟨ρ⟩ x⟨ρ⟩ P⟨upRen_term_term (upRen_term_term ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩
    end.

  Lemma map_eq_cons [A B : Type] (f : A -> B) (l : list A) [l' : list B] [b : B] :
    list_map f l = (b :: l')%list ->
    ∑ (a : A) (tl : list A),
    [× l = (a :: tl)%list , f a = b & list_map f tl = l'].
  Proof.
    intros e.
    destruct l ; cbn in * ; inversion e ; subst ; clear e.
    do 2 eexists ; split ; reflexivity.
  Qed.

  Lemma zip_rename ρ t π : (zip t π)⟨ρ⟩ = zip t⟨ρ⟩ (list_map (dest_entry_rename ρ) π).
  Proof.
    induction π as [|[]] in t |- * ; cbn.
    1: reflexivity.
    all: now erewrite IHπ.
  Qed.

  Lemma red_stack_str :
    funrect wh_red_stack (fun _ => True)
      (fun '(t,π) u => forall (ρ : nat -> nat) t' π',
        t = t'⟨ρ⟩ -> π = List.map (dest_entry_rename ρ) π' -> ∑ u', graph wh_red_stack (t',π') u' × u = u'⟨ρ⟩).
  Proof.
    intros ? _ ; cbn.
    funelim (wh_red_stack _) ; cbn ; try easy.
    - destruct t1 ; cbn.
      all: intros ? [] ? [=] ->%eq_sym%List.map_eq_nil ; subst.
      all: eexists ; split ; [unfold graph ; simp wh_red_stack ; now econstructor|..].
      all: now bsimpl.

    - intros ? [] ? [=] ->%eq_sym%List.map_eq_nil ; subst.
      eexists ; split.
      1: unfold graph ; simp wh_red_stack ; econstructor.
      reflexivity.

    - split ; [easy|..].
      intros * IH ? [] ? [=] ([]&?&[? [=]])%eq_sym%map_eq_cons ; subst.
      edestruct IH as [? []].
      2: reflexivity.
      2:{
        subst.
        eexists ; split ; [..|reflexivity].
        unfold graph ; simp wh_red_stack.
        patch_rec_ret ; econstructor.
        2: now constructor.
        eassumption.
      }
      now bsimpl.

    - intros ? [] ? [=] ? ; subst.
      eexists ; split.
      1: unfold graph ; simp wh_red_stack ; econstructor.
      now rewrite zip_rename.

    - destruct n0 ; cbn.
      all: intros ? [] ? [=] ->%eq_sym%List.map_eq_nil ; subst.
      all: eexists ; split ; [unfold graph ; simp wh_red_stack ; now econstructor|..].
      all: now bsimpl.

    - split ; [easy|..].
      intros * IH ? [] ? [=] ([]&?&[? [=]])%eq_sym%map_eq_cons ; subst.
      edestruct IH as [? []].
      2: reflexivity.
      2:{
        subst.
        eexists ; split ; [..|reflexivity].
        unfold graph ; simp wh_red_stack.
        patch_rec_ret ; econstructor.
        2: now constructor.
        eassumption.
      }
      now bsimpl.

    - split ; [easy|..].
      intros * IH ? [] ? [=] ([]&?&[? [=]])%eq_sym%map_eq_cons ; subst.
      edestruct IH as [? []].
      1: reflexivity.
      2:{
        subst.
        eexists ; split ; [..|reflexivity].
        unfold graph ; simp wh_red_stack.
        patch_rec_ret ; econstructor.
        2: now constructor.
        eassumption.
      }
      now bsimpl.
      
    - intros ? [] ? [=] ->%eq_sym%List.map_eq_nil ; subst.
      eexists ; split ; [unfold graph ; simp wh_red_stack ; now econstructor|..].
      now bsimpl.

    - split ; [easy|..].
      intros * IH ? [] ? [=] ([]&?&[? [=]])%eq_sym%map_eq_cons ; subst.
      edestruct IH as [? []].
      1: reflexivity.
      2:{
        subst.
        eexists ; split ; [..|reflexivity].
        unfold graph ; simp wh_red_stack.
        patch_rec_ret ; econstructor.
        2: now constructor.
        eassumption.
      }
      now bsimpl.

    - split ; [easy|..].
      intros * IH ? [] ? [=] ([]&?&[? [=]])%eq_sym%map_eq_cons ; subst.
      edestruct IH as [? []].
      1: reflexivity.
      2:{
        subst.
        eexists ; split ; [..|reflexivity].
        unfold graph ; simp wh_red_stack.
        patch_rec_ret ; econstructor.
        2: now constructor.
        eassumption.
      }
      now bsimpl.

    - intros ? [] ? [=] ->%eq_sym%List.map_eq_nil ; subst.
      eexists ; split ; [unfold graph ; simp wh_red_stack ; now econstructor|..].
      now bsimpl.
 
    - split ; [easy|..].
      intros * IH ? [] ? [=] ([]&?&[? [=]])%eq_sym%map_eq_cons ; subst.
      edestruct IH as [? []].
      1: reflexivity.
      2:{
        subst.
        eexists ; split ; [..|reflexivity].
        unfold graph ; simp wh_red_stack.
        patch_rec_ret ; econstructor.
        2: now constructor.
        eassumption.
      }
      now bsimpl.

    - split ; [easy|..].
      destruct s.
      all: intros * IH ? [] ? [=] ? ; subst.
      all: edestruct IH as [? []] ; [reflexivity|..] ; [shelve|..].
      all: subst.
      all: eexists ; split ; [..|reflexivity].
      all: unfold graph ; simp wh_red_stack ; cbn.
      all: patch_rec_ret ; econstructor ; [..|now constructor].
      all: eassumption.
      Unshelve.
      all: reflexivity.
  Qed.

  Corollary _wh_red_str :
    funrect wh_red (fun _ => True) (fun t u => forall (ρ : nat -> nat) t',
      t = t'⟨ρ⟩ -> ∑ u', graph wh_red t' u' × u = u'⟨ρ⟩).
  Proof.
    intros ? _.
    cbn ; intros ? H ρ t' ->.
    eapply funrect_graph in H.
    2: apply red_stack_str.
    2: easy.
    edestruct (H ρ t' nil) as [? []].
    1-2: reflexivity.
    eexists ; split ; tea.
    unfold graph.
    econstructor ; cbn ; tea.
    now constructor.
  Qed.
  
  Lemma wh_red_str (ρ : nat -> nat) t v :
    graph wh_red t⟨ρ⟩ v ->
    ∑ v', v = v'⟨ρ⟩ × graph wh_red t v'.
  Proof.
    intros g.
    eapply funrect_graph in g.
    2: apply _wh_red_str.
    2: easy.
    cbn in g.
    edestruct g as [? []].
    1: reflexivity.
    now easy.
  Qed.

  Lemma up_inj ρ : ssrfun.injective ρ -> ssrfun.injective (upRen_term_term ρ).
  Proof.
    intros H x y e.
    destruct x,y ; cbn in * ; try congruence.
    easy.
  Qed.

  Definition ncan_ne_view1 {N} (w : ~ isCanonical N) : ne_view1 N.
  Proof.
    destruct N.
    all: try solve [destruct w ; econstructor].
    - now constructor.
    - eapply (ne_view1_dest _ (eApp _)).
    - eapply (ne_view1_dest _ (eNatElim _ _ _)).
    - eapply (ne_view1_dest _ (eEmptyElim _)).
    - eapply (ne_view1_dest _ eFst).
    - eapply (ne_view1_dest _ eSnd).
    - eapply (ne_view1_dest _ (eIdElim _ _ _ _ _)).
  Defined.

  Lemma ncan_nf_view1 {N} (w : ~ isCanonical N) : build_nf_view1 N = nf_view1_ne (ncan_ne_view1 w).
  Proof.
    destruct N ; cbn ; try reflexivity.
    all: destruct w ; econstructor.
  Qed.

  Lemma nf_view2_neutral_can t t' :
    build_nf_view2 t t' = neutrals t t' ->
    ~ isCanonical t /\ ~ isCanonical t'.
  Proof.
    intros Heq.
    simp build_nf_view2 in Heq.
    destruct (build_nf_view1 t) as [? [] | | ? [] | | | ] eqn:Heqt ; cbn in Heq.
    all: destruct (build_nf_view1 t') as [? [] | | ? [] | | | ] eqn:Heqt' ; cbn in Heq.
    all: try solve [congruence].
    split.
    all: now eapply tm_view1_neutral_can.
  Qed.

  Definition nf_view2_rename (ρ : nat -> nat) {t t' : term} (v : nf_view2 t t') : nf_view2 t⟨ρ⟩ t'⟨ρ⟩ :=
    match v in nf_view2 x x' return nf_view2 x⟨ρ⟩ x'⟨ρ⟩ with
    | sorts s s' => sorts s s'
    | prods A A' B B' => prods A⟨ρ⟩ A'⟨ρ⟩ B⟨upRen_term_term ρ⟩ B'⟨upRen_term_term ρ⟩
    | nats => nats
    | emptys => emptys
    | sigs A A' B B' => sigs A⟨ρ⟩ A'⟨ρ⟩ B⟨upRen_term_term ρ⟩ B'⟨upRen_term_term ρ⟩
    | ids A A' x x' y y' => ids A⟨ρ⟩ A'⟨ρ⟩ x⟨ρ⟩ x'⟨ρ⟩ y⟨ρ⟩ y'⟨ρ⟩
    | lams A A' t t' => lams A⟨ρ⟩ A'⟨ρ⟩ t⟨upRen_term_term ρ⟩ t'⟨upRen_term_term ρ⟩
    | lam_ne A t n' => lam_ne A⟨ρ⟩ t⟨upRen_term_term ρ⟩ n'⟨ρ⟩
    | ne_lam n A' t' => ne_lam n⟨ρ⟩ A'⟨ρ⟩ t'⟨upRen_term_term ρ⟩
    | zeros => zeros
    | succs t t' => succs t⟨ρ⟩ t'⟨ρ⟩
    | pairs A A' B B' t t' u u' => pairs A⟨ρ⟩ A'⟨ρ⟩ B⟨upRen_term_term ρ⟩ B'⟨upRen_term_term ρ⟩ t⟨ρ⟩ t'⟨ρ⟩ u⟨ρ⟩ u'⟨ρ⟩
    | pair_ne A B t u n' => pair_ne A⟨ρ⟩ B⟨upRen_term_term ρ⟩ t⟨ρ⟩ u⟨ρ⟩ n'⟨ρ⟩
    | ne_pair n A' B' t' u' => ne_pair n⟨ρ⟩ A'⟨ρ⟩ B'⟨upRen_term_term ρ⟩ t'⟨ρ⟩ u'⟨ρ⟩
    | refls A A' x x' => refls A⟨ρ⟩ A'⟨ρ⟩ x⟨ρ⟩ x'⟨ρ⟩
    | neutrals n n' => neutrals n⟨ρ⟩ n'⟨ρ⟩
    | mismatch t u => mismatch t⟨ρ⟩ u⟨ρ⟩
    | anomaly t u => anomaly t⟨ρ⟩ u⟨ρ⟩
    end.

  Lemma build_nf_view2_rename ρ t t' : build_nf_view2 t⟨ρ⟩ t'⟨ρ⟩ = nf_view2_rename ρ (build_nf_view2 t t').
  Proof.
    destruct t, t' ; reflexivity.
  Qed.

  Definition ne_view2_rename (ρ : nat -> nat) {t t' : term} (v : ne_view2 t t') : ne_view2 t⟨ρ⟩ t'⟨ρ⟩ :=
    match v in ne_view2 x x' return ne_view2 x⟨ρ⟩ x'⟨ρ⟩ with
    | ne_rels n n' => ne_rels (ρ n) (ρ n')
    | ne_apps f u f' u' => ne_apps f⟨ρ⟩ u⟨ρ⟩ f'⟨ρ⟩ u'⟨ρ⟩
    | ne_nats n P hz hs n' P' hz' hs' => ne_nats
        n⟨ρ⟩ P⟨upRen_term_term ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩
        n'⟨ρ⟩ P'⟨upRen_term_term ρ⟩ hz'⟨ρ⟩ hs'⟨ρ⟩
    | ne_emptys n P n' P' => ne_emptys n⟨ρ⟩ P⟨upRen_term_term ρ⟩ n'⟨ρ⟩ P'⟨upRen_term_term ρ⟩
    | ne_fsts p p' => ne_fsts p⟨ρ⟩ p'⟨ρ⟩
    | ne_snds p p' => ne_snds p⟨ρ⟩ p'⟨ρ⟩
    | ne_ids A x P hr y e A' x' P' hr' y' e' => ne_ids
      A⟨ρ⟩ x⟨ρ⟩ P⟨upRen_term_term (upRen_term_term ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩ e⟨ρ⟩
      A'⟨ρ⟩ x'⟨ρ⟩ P'⟨upRen_term_term (upRen_term_term ρ)⟩ hr'⟨ρ⟩ y'⟨ρ⟩ e'⟨ρ⟩
    | ne_mismatch t u => ne_mismatch t⟨ρ⟩ u⟨ρ⟩
    | ne_anomaly t u => ne_anomaly t⟨ρ⟩ u⟨ρ⟩
    end.

  Lemma build_ne_view2_rename ρ t t' : build_ne_view2 t⟨ρ⟩ t'⟨ρ⟩ = ne_view2_rename ρ (build_ne_view2 t t').
  Proof.
    destruct t, t' ; reflexivity.
  Qed.

  #[local] Ltac crush :=
    repeat match goal with
      | |- context [build_nf_view1 _] => erewrite ncan_nf_view1 ; cbn
      | |- forall (_ : exn _ _), _ => intros [] ; cbn
      | |- ?t = ?t'⟨_⟩ -> _ =>
            intros _eq ; subst t +
              (destruct t' ; cbn in _eq ; try solve [congruence] ; inversion _eq ; subst ; clear _eq)
      | |- forall _ : _, _ => intros ?
      | |- True => trivial
      | |- True * _ => split ; [trivial|..]
      | |- graph _uconv (_, _, _) _ => unfold graph ; simp _uconv uconv_tm_red uconv_ne build_nf_view2 ; cbn
      | H : _ |- orec_graph ?f (?f ?t) ?r => simple eapply H ; [..|reflexivity|reflexivity]
      | |- orec_graph _ _ _ => cbn ; patch_rec_ret ; econstructor
      | |- ssrfun.injective (upRen_term_term _) => apply up_inj
      | |- ssrfun.injective _ => assumption
    end.

  Lemma _uconv_str :
    funrect _uconv (fun _ => True)
      (fun '(s,t,u) r => forall (ρ : nat -> nat) t' u', ssrfun.injective ρ ->
        t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ -> graph _uconv (s,t',u') r).
  Proof.
    intros ? _ ; cbn.
    funelim (_uconv _) ; cbn.

    - funelim (uconv_tm _) ; cbn.
      intros ? red ? red'.
      split ; [easy|..].
      intros ? IH ** ; subst.
      unfold graph ; simp _uconv uconv_tm ; cbn.
      eapply wh_red_str in red as [? [->]], red' as [? [->]].
      econstructor.
      1: eassumption.
      econstructor.
      1: eassumption.
      patch_rec_ret.
      econstructor ; [..|econstructor].
      now eapply IH.

    - funelim (uconv_tm_red _) ; cbn.
      all: match goal with | _ : _ = _ |- _ => shelve | _ => idtac end.
      all: solve [crush].
      Unshelve.

      + crush.
        all: eapply H ; [now eapply up_inj | reflexivity|..].
        all: now asimpl.

      + crush.
        all: eapply H ; [now eapply up_inj |idtac|reflexivity].
        all: now asimpl.

      + crush.
      
      + crush.

      + crush.

      + intros.
        subst.
        rewrite build_nf_view2_rename in Heq.
        unfold graph ; simp _uconv uconv_tm_red.
        destruct (build_nf_view2 _ _) ; cbn in * ; try solve [congruence].
        now constructor.
      
      + easy.

    - funelim (uconv_ne _) ; cbn.
      1-6,8: solve [crush].

      + intros.
        subst.
        rewrite build_ne_view2_rename in Heq.
        unfold graph ; simp _uconv uconv_ne.
        destruct (build_ne_view2 _ _) ; cbn in * ; try solve [congruence].
        now constructor.

      + crush.
        eapply Nat.eqb_eq in Heq ; subst.
        match goal with | H : ssrfun.injective _ |- _ => apply H in Heq end.
        subst.
        rewrite Nat.eqb_refl ; cbn.
        now constructor.
      + crush.
        eapply Nat.eqb_neq in Heq.
        rewrite (proj2 (Nat.eqb_neq _ _)) ; cbn ; auto.
        now constructor.

  Unshelve.
  all: try solve [apply nf_view2_neutral_can in Heq as [] ; now eintros ?%isCanonical_ren].
  all: match goal with
    | |- ~ isCanonical ?t => remember t⟨ρ⟩ as t' in * ; eintros ?%isCanonical_ren
    end.
  all: solve [simp build_nf_view2 in Heq ;
    destruct (build_nf_view1 t') as [? [] | | ? [] | | | ] eqn:Heq' ; subst ; cbn in * ;
      congruence + (now eapply tm_view1_neutral_can)].

  Qed.

End AlgoStr.

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
  eapply uconv_wk in g.
  - now eexists.
  - intros ??.
    auto.
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
      eapply red_compl_prod_l' in Hconv as (?&?&[->]).
      2: gen_typing.
      inversion Hpos.
      inv_whne.
    + eapply termGen' in Hty as (?&[->]&Hconv).
      eapply conv_sig_l in Hconv as (?&?&[->]).
      2: gen_typing.
      inversion Hpos.
      inv_whne.
    + unshelve erewrite whne_nf_view1 ; tea ; cbn.
      split ; [..|easy].
      eapply IH ; tea.
      split ; now eexists.
 
Qed.