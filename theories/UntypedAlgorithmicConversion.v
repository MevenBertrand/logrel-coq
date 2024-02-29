(** * LogRel.UntypedAlgorithmicConversion: alternative definition of algorithmic conversion. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  UntypedReduction GenericTyping DeclarativeTyping DeclarativeInstance
  BundledAlgorithmicTyping AlgorithmicTyping AlgorithmicConvProperties TypeConstructorsInj
  Normalisation DeclarativeSubst Fundamental LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Neutral Escape Reflexivity.
From LogRel.Substitution Require Import Escape Poly.

Import DeclarativeTypingProperties AlgorithmicTypingData.


(** ** Definitions *)

(** **** Conversion of types/terms: there is no distinction here *)
Inductive UConvAlg : term -> term  -> Type :=
  | termConvRed {t t' u u'} :
    [t ⤳* t'] ->
    [u ⤳* u' ] ->
    [t' ≅h u'] ->
    [t ≅ u]
(** **** Conversion of types/terms reduced to a weak-head normal form *)
with UConvRedAlg : term -> term -> Type :=
  | PiCongUAlg {A B A' B'} :
    [A ≅ A'] ->
    [B ≅ B'] ->
    [tProd A B ≅h tProd A' B']
  | NatReflUAlg :
    [tNat ≅h tNat]
  | ZeroReflUAlg :
    [tZero ≅h tZero]
  | SuccCongUAlg {t t'} :
    [t ≅ t'] ->
    [tSucc t ≅h tSucc t']
  | EmptyReflUAlg :
    [tEmpty ≅h tEmpty]
  | LamCongUAlg {A t A' t'} :
    [t ≅ t'] ->
    [tLambda A t ≅h tLambda A' t']
  | LambNeUAlg {A t n'} :
    whne n' ->
    [t ≅ eta_expand n'] -> 
    [tLambda A t ≅h n']
  | NeLamUAlg {n A' t'} :
    whne n ->
    [eta_expand n ≅ t'] -> 
    [n ≅h tLambda A' t']
  | SigCongUAlg {A B A' B'} :
    [A ≅ A'] ->
    [ B ≅ B'] ->
    [tSig A B ≅h tSig A' B']
  | PairCongUAlg {A B p q A' B' p' q'} :
    [p ≅ p'] ->
    [q ≅ q'] ->
    [tPair A B p q ≅h tPair A' B' p' q']
  | PairNeUAlg {A B p q n'} :
    whne n' ->
    [p ≅ tFst n'] ->
    [q ≅ tSnd n'] ->
    [tPair A B p q ≅h n']
  | NePairUAlg {n A' B' p' q'} :
    whne n ->
    [tFst n ≅ p'] ->
    [tSnd n ≅ q'] ->
    [n ≅h tPair A' B' p' q']
  | IdCongUAlg {A A' x x' y y'} :
    [A ≅ A'] ->
    [x ≅ x'] ->
    [y ≅ y'] ->
    [tId A x y ≅h tId A' x' y']
  | termIdReflCong {A x A' x'} :
    [tRefl A x ≅h tRefl A' x']
  | NeuConvUAlg {m n} :
    [m ~ n] ->
    [m ≅h n]

(** **** Conversion of neutral terms *)
with UConvNeuAlg : term  -> term -> Type :=
  | VarConvUAlg {n} :
    [tRel n ~ tRel n]
  | AppCongUAlg {m n t u} :
    [m ~ n] ->
    [t ≅ u] ->
    [tApp m t ~ tApp n u]
  | NatElimCongUAlg {n n' P P' hz hz' hs hs'} :
    [n ~ n'] ->
    [P ≅ P'] ->
    [hz ≅ hz'] ->
    [hs ≅ hs'] ->
    [tNatElim P hz hs n ~ tNatElim P' hz' hs' n']
  | EmptyElimCongUAlg {P P' e e'} :
    [e ~ e'] ->
    [P ≅ P'] ->
    [tEmptyElim P e ~ tEmptyElim P' e']
  | FstCongUAlg {m n} :
    [m ~ n] ->
    [tFst m ~ tFst n]
  | SndCongUAlg {m n} :
    [m ~ n] ->
    [tSnd m ~ tSnd n]
  | IdElimCongUAlg {A A' x x' P P' hr hr' y y' e e'} :
    [e ~ e'] ->
    [P ≅ P'] ->
    [hr ≅ hr'] ->
    [tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e']

where "[ A ≅ B ]" := (UConvAlg A B)
and "[ A ≅h B ]" := (UConvRedAlg A B)
and "[ m ~ n ]" := (UConvNeuAlg m n).

(** ** Induction principles *)

Scheme 
    Minimality for UConvAlg Sort Type with
    Minimality for UConvRedAlg Sort Type with
    Minimality for UConvNeuAlg Sort Type.
    
Combined Scheme UAlgoConvInduction from
    UConvAlg_rect_nodep,
    UConvRedAlg_rect_nodep,
    UConvNeuAlg_rect_nodep.

Arguments UAlgoConvInduction PEq PRedEq PNeEq : rename.


Definition UAlgoConvInductionConcl :=
  ltac:(
    let t := type of UAlgoConvInduction in
    let t' := remove_steps t in
    exact t').

(* 
(** ** Bundles *)

Definition bnu : tag.
Proof.
constructor.
Qed.

Record ConvTypeUBun Γ A B :=
{
  bun_uconv_ty_ctx : [|-[de] Γ] ;
  bun_uconv_ty_l : [Γ |-[de] A] ;
  bun_uconv_ty_r : [Γ |-[de] B] ;
  bun_uconv_ty : [A ≅ B]
}.

Record ConvTypeRedUBun Γ A B :=
{
  bun_uconv_ty_red_ctx : [|-[de] Γ] ;
  bun_uconv_ty_red_l : [Γ |-[de] A] ;
  bun_uconv_ty_red_wh_l : isType A ;
  bun_uconv_ty_red_r : [Γ |-[de] B] ;
  bun_uconv_ty_red_wh_r : isType B ;
  bun_uconv_ty_red : [A ≅h B]
}.

Record ConvTermUBun Γ A t u :=
{
  bun_uconv_tm_ctx : [|-[de] Γ] ;
  bun_uconv_tm_ty : [Γ |-[de] A] ;
  bun_uconv_tm_l : [Γ |-[de] t : A] ;
  bun_uconv_tm_r : [Γ |-[de] u : A] ;
  bun_uconv_tm : [t ≅ u]
}.

Record ConvTermRedUBun Γ A t u :=
{
  bun_uconv_tm_red_ctx : [|-[de] Γ] ;
  bun_uconv_tm_red_ty : [Γ |-[de] A] ;
  bun_uconv_tm_red_wh_ty : isType A ;
  bun_uconv_tm_red_l : [Γ |-[de] t : A] ;
  bun_uconv_tm_red_wh_l : whnf t ;
  bun_uconv_tm_red_r : [Γ |-[de] u : A] ;
  bun_uconv_tm_red_wh_r : whnf u ;
  bun_uconv_tm_red : [t ≅h u]
}.

Record ConvNeuUBun Γ A m n :=
{
  bun_uconv_ne_ctx : [|-[de] Γ] ;
  bun_uconv_ne_l : [Γ |-[de] m : A] ;
  bun_uconv_ne_wh_l : whne m ;
  bun_uconv_ne_r : well_typed (ta := de) Γ n ;
  bun_uconv_ne_wh_r : whne n ;
  bun_uconv_ne : [m ~ n]
}. *)

(** ** Relation to weak-head normal forms *)

Section UAlgoConvWh.

  Let PEq (A B : term) := True.
  Let PNeEq (m n : term) := 
    whne m × whne n.
  Let PRedEq (t u : term) := 
    whnf t × whnf u.

  Theorem algo_uconv_wh :
    UAlgoConvInductionConcl PEq PRedEq PNeEq.
  Proof.
    subst PEq PRedEq PNeEq ; cbn.
    apply UAlgoConvInduction.
    all: intros ; prod_splitter ; prod_hyp_splitter.
    all: now constructor.
  Qed.

End UAlgoConvWh.


Section NeutralConversion.
  Import AlgorithmicTypingData.

  Lemma var0_wk1_id {Γ A t} : t[tRel 0 .: @wk1 Γ A >> tRel] = t.
  Proof. bsimpl. rewrite scons_eta'. now asimpl. Qed.

  Lemma ne_conv_conv (Γ : context) (A m n : term) :
    [Γ |-[de] A] ->
    [Γ |-[de] m : A] ->
    [Γ |-[al] m ~ n ▹ A] ->
    [Γ |-[al] m ≅ n : A].
  Proof.
    intros * Hty.
    pose proof (Hty' := Hty).
    eapply Fundamental in Hty' as [? Hfund%reducibleTy].
    revert m n.
    pattern one, Γ, A, Hfund. apply LR_rect_TyUr; clear Γ A Hty VΓ Hfund.
    - intros.
      econstructor.
      1: eapply redty_red; now destruct h as [??? [??]].
      1-2: reflexivity.
      econstructor. 
      2: now constructor.
      eassumption.
    - intros ? * [] ?.
      econstructor.
      1: gen_typing.
      1-2: reflexivity.
      econstructor.
      1: eassumption.
      econstructor; eapply (convneu_whne eq).
    - intros ? ? ? ΠA IHdom IHcod m n mty Hconv ; cbn in *.
      destruct ΠA  as [?????? []]; cbn in *.
      econstructor.
      1: gen_typing.
      1-2: reflexivity.
      econstructor.
      1-2: econstructor ; now eapply algo_conv_wh in Hconv.
      eapply convtm_meta_conv.
      3: reflexivity.
      1: unshelve eapply IHcod.
      + exact (tRel var_zero).
      + apply wk1.
      + gen_typing.
      + eapply var0; tea ; now bsimpl.
      + econstructor. 1:econstructor.
        * renToWk; erewrite wk_prod; eapply ty_wk.
          1: econstructor; tea; boundary.
          econstructor; tea. gen_typing.
        * rewrite wk1_ren_on; now eapply ty_var0.
        * assert (cod⟨wk_up dom (@wk1 Γ dom)⟩[(tRel 0)..] = cod[tRel 0 .: @wk1 Γ dom >> tRel]) as -> by now bsimpl.
          econstructor. now rewrite var0_wk1_id.
      + eapply convne_meta_conv.
        3: reflexivity.
        1: econstructor.
        * replace (tProd _ _) with ((tProd dom cod)⟨↑⟩) by
            (cbn ; reflexivity).
          eapply algo_conv_shift.
          econstructor ; tea.
          1: now gen_typing.
          econstructor.
        * eapply convtm_meta_conv.
          1: unshelve eapply IHdom.
          -- now eapply wk1.
          -- gen_typing.
          -- rewrite wk1_ren_on; now eapply ty_var0.
          -- eapply convne_meta_conv.
             1: do 2 econstructor.
             2: reflexivity.
             now bsimpl.
          -- now bsimpl.
          -- reflexivity.
        * now bsimpl.
      + bsimpl.
        rewrite scons_eta'.
        now bsimpl.
  - intros _ Δ B NB **; destruct NB.
    econstructor.
    + now eapply redtywf_red.
    + reflexivity.
    + reflexivity.
    + econstructor; [eassumption|constructor].
  - intros _ Δ B NB **; destruct NB.
    econstructor.
    + now eapply redtywf_red.
    + reflexivity.
    + reflexivity.
    + econstructor; [eassumption|constructor].
  - intros ??? ΣA ihdom ihcod m n tym Hconv.
    destruct (polyRedId ΣA); escape.
    assert [|-[de] Γ] by boundary.
    econstructor.
    1: eapply (ParamRedTy.red ΣA).
    1,2: reflexivity.
    assert [Γ |-[de] m : ParamRedTy.outTy ΣA]. 1:{
      econstructor; tea.
      eapply convty_exp. 
      1: eapply (ParamRedTy.red ΣA).
      1: eapply redtywf_refl; eapply (ParamRedTy.red ΣA).
      econstructor; tea;
      eapply LogicalRelation.Escape.escapeEq;
      eapply reflLRTyEq.
    }
    assert [Γ |-[ de ] tFst m : (ParamRedTy.dom ΣA)⟨@wk_id Γ⟩].
    1: rewrite wk_id_ren_on; now econstructor.
    assert [Γ |-[ al ] tFst m ~ tFst n ▹ ParamRedTy.dom ΣA].
    1:{
      do 2 econstructor; tea.
      1: eapply (ParamRedTy.red ΣA).
      constructor.
    }
    econstructor.
    1-2: econstructor ; now eapply algo_conv_wh in Hconv.
    + unshelve epose (r := ihdom _ wk_id _ _ _ _).
      1,4: tea.
      2: rewrite wk_id_ren_on in r; now apply r.
    + unshelve epose (r := ihcod _ (tFst m) wk_id _ _ _ _ _).
      1: tea.
      5: erewrite Sigma.wk_id_shift in r; apply r.
      3: do 2 econstructor; tea.
      3: eapply (ParamRedTy.red ΣA).
      3: constructor.
      * assert (whne m).
        { apply algo_conv_wh in Hconv; now destruct Hconv. }
        eapply neuTerm; tea.
        split; tea; now econstructor.
      * rewrite Sigma.wk_id_shift; now econstructor.
    Unshelve. 2,4: tea.
  - intros ??? [???? red] IH _ m n tym hconv; cbn in *.
    econstructor.
    1: apply red.
    1,2: reflexivity.
    econstructor; tea; constructor.
  Qed.

End NeutralConversion.

Section Soundness.

  Let PEq (t u : term) :=
    (forall Γ, [Γ |-[de] t] -> [Γ |-[de] u] -> [Γ |-[al] t ≅ u]) ×
    (forall Γ A, [Γ |-[de] t : A] -> [Γ |-[de] u : A] -> [Γ |-[al] t ≅ u : A]).

  Let PRedEq (t u : term) :=
    (forall Γ, [Γ |-[de] t] -> [Γ |-[de] u] -> [Γ |-[al] t ≅h u]) ×
    (forall Γ A, isType A -> [Γ |-[de] t : A] -> [Γ |-[de] u : A] -> [Γ |-[al] t ≅h u : A]).

  Let PNeEq (t u : term) :=
    forall Γ A A', [Γ |-[de] t : A] -> [Γ |-[de] u : A'] ->
    ∑ A'', [× [Γ |-[al] t ~ u ▹ A''], [Γ |-[de] A'' ≅ A] & [Γ |-[de] A'' ≅ A']].

  Property subject_reduction_raw Γ t t' A :
    [t ⤳* t'] ->
    [Γ |-[de] t : A] ->
    [Γ |-[de] t' : A].
  Proof.
    eintros Hty ?%subject_reduction ; tea.
    boundary.
  Qed.

  Property subject_reduction_raw_ty Γ A A' :
    [A ⤳* A'] ->
    [Γ |-[de] A] ->
    [Γ |-[de] A'].
  Proof.
    eintros Hty ?%subject_reduction_type ; tea.
    boundary.
  Qed.

  Lemma uconv_sound :
    UAlgoConvInductionConcl PEq PRedEq PNeEq.
  Proof.
    subst PEq PRedEq PNeEq.
    apply UAlgoConvInduction.
    - intros * Ht Hu Ht' [Hty Htm].
      split.
      + intros.
        econstructor ; eauto.
        eapply Hty.
        all: now eapply subject_reduction_raw_ty.
      + intros.
        assert [Γ |-[de] A] as [? red]%type_normalisation by boundary.
        eapply subject_reduction_type in red as [] ; refold.
        2: boundary.
        econstructor ; eauto.
        eapply Htm.
        * eapply type_isType ; tea.
          boundary.
        * eapply subject_reduction_raw ; tea.
          gen_typing.
        * eapply subject_reduction_raw ; tea.
          gen_typing.
    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros * [HtyA HtyB]%prod_ty_inv [HtyA' HtyB']%prod_ty_inv.
        assert [Γ |-[al] A ≅ A'] as Hconv_al by eauto.
        pose proof Hconv_al as Hconv_de.
        eapply algo_conv_sound in Hconv_de ; tea.
        econstructor ; eauto.
        apply IHB_ty ; tea.
        now eapply stability1.
      + intros * ? [? [[-> ] Hred%red_ty_compl_univ_l]]%termGen' [? [[-> ] ]]%termGen'.
        assert [Γ |-[al] A ≅ A' : U] as Hconv_al by eauto.
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        pose proof Hconv_al as Hconv_de.
        eapply algo_conv_sound in Hconv_de ; tea.
        econstructor ; tea.
        eapply IHB_tm ; tea.
        eapply stability1 ; tea.
        all: gen_typing.
    - split.
      1: now econstructor.
      intros * ? _ [? [? Hred]]%termGen'.
      cbn in * ; subst.
      eapply red_ty_compl_univ_l, redty_sound, red_whnf in Hred as ->.
      constructor.
      now gen_typing.
    - split.
      + intros * Hz _.
        inversion Hz ; subst ; refold.
        eapply termGen' in H as [? [? Hconv]].
        cbn in * ; subst.
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      + intros * ? _ [? [? Hred]]%termGen'.
        cbn in * ; subst.
        eapply red_ty_compl_nat_l, redty_sound, red_whnf in Hred as ->.
        constructor.
        now gen_typing.
    - intros * Ht [_ IHt].
      split.
      + intros * Hs _.
        inversion Hs ; subst ; refold.
        eapply termGen' in H as [? [[-> _] Hconv]].
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      + intros * ? [? [[-> ?] Hred]]%termGen' [? [[-> ?] _]]%termGen'.
        eapply red_ty_compl_nat_l, redty_sound, red_whnf in Hred as ->.
        2: now gen_typing.
        now constructor.
    - split.
      1: now econstructor.
      intros * ? _ [? [? Hred]]%termGen'.
      cbn in * ; subst.
      eapply red_ty_compl_univ_l, redty_sound, red_whnf in Hred as ->.
      constructor.
      now gen_typing.
    - intros * Ht [_ IHt].
      split.
      + intros * Hs _.
        inversion Hs ; subst ; refold.
        eapply termGen' in H as [? [[* [->]] Hconv]].
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      + intros ? T ? [? [[B [->]] Hconv]]%termGen' [? [[B' [->]] Hconv']]%termGen'.
        eapply red_ty_compl_prod_l in Hconv as (A''&B''&[Hred]).
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        eapply prod_ty_inj in Hconv' as [].
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; [..|eapply IHt].
        1: reflexivity.
        1-2: eapply redalg_one_step, eta_expand_beta.
        all: econstructor ; [eapply stability1 ; [..| eassumption] | ..] ; tea ; boundary.
    - intros * Hne Ht [_ IHt].
      split.
      + intros * Hs _.
        inversion Hs ; subst ; refold.
        eapply termGen' in H as [? [[* [->]] Hconv]].
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      + intros ? T ? [? [[B [->]] Hconv]]%termGen' Hn.
        eapply red_ty_compl_prod_l in Hconv as (A''&B''&[Hred]).
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; [..|eapply IHt].
        * reflexivity.
        * eapply redalg_one_step, eta_expand_beta.
        * reflexivity.
        * econstructor ; [eapply stability1 ; [..| eassumption] | ..] ; tea ; boundary.
        * now eapply typing_eta'.
    - intros * Hne Ht [_ IHt].
      split.
      + intros * _ Hs.
        inversion Hs ; subst ; refold.
        eapply termGen' in H as [? [[* [->]] Hconv]].
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      + intros ? T ? Hn [? [[B [->]] Hconv]]%termGen'.
        eapply red_ty_compl_prod_l in Hconv as (A''&B''&[Hred]).
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; [..|eapply IHt].
        * reflexivity.
        * reflexivity.
        * eapply redalg_one_step, eta_expand_beta.
        * now eapply typing_eta'.
        * econstructor ; [eapply stability1 ; [..| eassumption] | ..] ; tea ; boundary.
    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros * [HtyA HtyB]%sig_ty_inv [HtyA' HtyB']%sig_ty_inv.
        assert [Γ |-[al] A ≅ A'] as Hconv_al by eauto.
        pose proof Hconv_al as Hconv_de.
        eapply algo_conv_sound in Hconv_de ; tea.
        econstructor ; eauto.
        apply IHB_ty ; tea.
        now eapply stability1.
      + intros * ? [? [[-> ] Hred%red_ty_compl_univ_l]]%termGen' [? [[-> ] ]]%termGen'.
        assert [Γ |-[al] A ≅ A' : U] as Hconv_al by eauto.
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        pose proof Hconv_al as Hconv_de.
        eapply algo_conv_sound in Hconv_de ; tea.
        econstructor ; tea.
        eapply IHB_tm ; tea.
        eapply stability1 ; tea.
        all: gen_typing.
    - intros * Hp [_ IHp] Hq [_ IHq].
      split.
      + intros * Hs _.
        inversion Hs ; subst ; refold.
        eapply termGen' in H as [? [[* ->] Hconv]].
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      + intros ? T ? [? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'.
        eapply red_ty_compl_sig_l in Hconv as (A''&B''&[Hred]).
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        eapply sig_ty_inj in Hconv' as [].
        assert [Γ |-[de] p' : A]
          by (econstructor ; tea ; etransitivity ; tea ; now symmetry).
        assert [Γ |-[al] p ≅ p' : A] as ?%algo_conv_sound by eauto ; tea.
        econstructor.
        1-2: now constructor.
        * eapply algo_conv_tm_expand ; [..|eapply IHp].
          1: reflexivity.
          1-2: eapply redalg_one_step ; constructor.
          all: now econstructor.
        * assert [Γ |-[ de ] p ≅ tFst (tPair A B p q) : A] by
            (econstructor ; symmetry ; now econstructor).
          eapply algo_conv_tm_expand ; [..|eapply IHq].
          1: reflexivity.
          1-2: eapply redalg_one_step ; constructor.
          all: econstructor ; tea.
          all: eapply typing_subst1 ; tea.
          econstructor.
          1: etransitivity ; tea.
          1: now symmetry.
          etransitivity ; tea.
          now symmetry.
    - intros * Hne Hp [_ IHp] Hq [_ IHq].
      split.
      { intros * Hs _.
        inversion Hs ; subst ; refold.
        eapply termGen' in H as [? [[* ->] Hconv]].
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      }
      intros ? T ? [? [[->] Hconv]]%termGen' Hn.
      eapply red_ty_compl_sig_l in Hconv as (A''&B''&[Hred]).
      eapply redty_sound, red_whnf in Hred as ->.
      2: gen_typing.
      assert [Γ |-[de] tFst n' : A] by
        now eapply wfTermConv ; refold ; [econstructor|..].
      assert [Γ |-[al] p ≅ tFst n' : A] as ?%algo_conv_sound by eauto ; tea.
      econstructor.
      1-2: now constructor.
      + eapply algo_conv_tm_expand ; [..|eapply IHp].
        1,3: reflexivity.
        1: eapply redalg_one_step ; constructor.
        all: now econstructor.
      + assert [Γ |-[ de ] p ≅ tFst (tPair A B p q) : A] by
          (econstructor ; symmetry ; now econstructor).
        eapply algo_conv_tm_expand ; [..|eapply IHq].
        * reflexivity.
        * eapply redalg_one_step ; constructor.
        * reflexivity.
        * econstructor ; tea.
          now eapply typing_subst1.
        * econstructor.
          1: now econstructor.
          eapply typing_subst1.
          2: econstructor ; boundary.
          etransitivity ; tea.
          now econstructor ; symmetry.
    - intros * Hne Hp [_ IHp] Hq [_ IHq].
      split.
      { intros * _ Hs.
        inversion Hs ; subst ; refold.
        eapply termGen' in H as [? [[* ->] Hconv]].
        unshelve eapply ty_conv_inj in Hconv.
        1-2: now constructor.
        now cbn in *.
      }
      intros ? T ? Hn [? [[->] Hconv]]%termGen'.
      eapply red_ty_compl_sig_l in Hconv as (A''&B''&[Hred]).
      eapply redty_sound, red_whnf in Hred as ->.
      2: gen_typing.
      assert [Γ |-[de] tFst n : A'] by
        now eapply wfTermConv ; refold ; [econstructor|..].
      assert [Γ |-[al] tFst n ≅ p' : A'] as ?%algo_conv_sound by eauto ; tea.
      econstructor.
      1-2: now constructor.
      + eapply algo_conv_tm_expand ; [..|eapply IHp].
        1,2: reflexivity.
        1: eapply redalg_one_step ; constructor.
        all: now econstructor.
      + (* assert [Γ |-[ de ] p ≅ tFst (tPair A B p q) : A''] by
          (econstructor ; symmetry ; now econstructor). *)
        eapply algo_conv_tm_expand ; [..|eapply IHq].
        * reflexivity.
        * reflexivity.
        * eapply redalg_one_step ; constructor.
        * now econstructor.
        * econstructor ; tea.
          eapply typing_subst1 ; tea.
          now econstructor ; symmetry.
    - intros * HA [IHA_ty IHA_tm] Hx [_ IHx_tm] Hy [_ IHy_tm].
      split.
      + intros * [HtyA [Htyx Htyy]]%id_ty_inv [HtyA' [Htyx' Htyy']]%id_ty_inv.
        assert [Γ |-[al] A ≅ A'] as [Hconv_al Hconv_de]%dup by eauto.
        eapply algo_conv_sound in Hconv_de ; tea.
        econstructor ; eauto.
        * eapply IHx_tm ; tea ; now econstructor.
        * eapply IHy_tm ; tea ; now econstructor.
      + intros * ? [? [[-> ] Hred%red_ty_compl_univ_l]]%termGen' [? [[-> ] ]]%termGen'.
        assert [Γ |-[al] A ≅ A'] as ?%algo_conv_sound by (eapply IHA_ty ; gen_typing).
        2-3: gen_typing.
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        econstructor ; eauto.
        * eapply IHx_tm ; tea ; now econstructor.
        * eapply IHy_tm ; tea ; now econstructor.
    - intros *.
      split.
      { intros * Hs _.
      inversion Hs ; subst ; refold.
      eapply termGen' in H as [? [[* ->] Hconv]].
      unshelve eapply ty_conv_inj in Hconv.
      1-2: now constructor.
      now cbn in *.
      }
      intros ? T ? [? [[->] Hconv]]%termGen' _.
      eapply red_ty_compl_id_l in Hconv as (?&?&?&[Hred]).
      eapply redty_sound, red_whnf in Hred as ->.
      2: gen_typing.
      econstructor.
    - intros * Hconv IH.
      split.
      + intros * Hm Hn.
        edestruct IH as [? []].
        * eapply neutral_ty_inv in Hm.
          2: now eapply algo_uconv_wh in Hconv as [].
          eassumption.
        * eapply neutral_ty_inv in Hn.
          2: now eapply algo_uconv_wh in Hconv as [].
          eassumption.
        * now econstructor.
      + intros * ? Hm Hn.
        edestruct IH as [? [IHconv ]] ; tea.
        epose proof IHconv as []%algo_conv_sound.
        2-3: now eexists.
        eapply ne_conv_conv in IHconv.
        2: boundary.
        2: econstructor ; tea ; now symmetry.
        eapply algo_conv_conv in IHconv ; tea.
        2: eapply ctx_refl ; boundary.
        2-3: now econstructor.
        inversion IHconv as [??????? hA hm hn] ; subst ; refold.
        eapply red_whnf in hA as -> ; [|gen_typing].
        eapply red_whnf in hm as -> ; [|eapply algo_uconv_wh in Hconv as [] ; gen_typing].
        eapply red_whnf in hn as -> ; [|eapply algo_uconv_wh in Hconv as [] ; gen_typing].
        assumption.
    - intros * [? [[decl [-> ? Hdecl]] ]]%termGen' [? [[? [->]] ]]%termGen'.
      eapply in_ctx_inj in Hdecl ; tea ; subst.
      eexists ; split.
      1: econstructor ; tea.
      all: now symmetry.
    - intros * Hm IHm Ht [_ IHt] ? T T' [? [(A&B&[->])]]%termGen' [? [(A'&B'&[->])]]%termGen'.
      edestruct IHm as [T'' [? Hconv Hconv']] ; tea.
      eapply red_ty_compl_prod_r in Hconv as (?&?&[Hred]).
      eapply red_ty_compl_prod_r in Hconv' as (A''&B''&[Hred']).
      eapply redty_sound, whred_det in Hred' ; [..|eapply Hred].
      2-3: now constructor.
      inversion Hred' ; subst ; clear Hred'.
      assert [Γ |-[ al ] t ≅ u : A''] as [? ?%algo_conv_sound]%dup by
        (eapply IHt ; econstructor ; tea).
      2-3: now econstructor.
      eexists ; split.
      + do 2 (econstructor ; tea).
        2: now constructor.
        now eapply redty_sound.
      + etransitivity ; tea.
        eapply typing_subst1 ; tea.
        constructor.
        boundary.
      + etransitivity ; tea.
        eapply typing_subst1.
        2: eassumption.
        econstructor ; tea.
        now symmetry.
    - intros * Hn IHn Hp [IHP _] Hz [_ IHz] HS [_ IHS] ? T T'
        [? [[->]]]%termGen' [? [[->]]]%termGen'.
      edestruct IHn as [T'' [Hconvn Hconv Hconv']] ; tea.
      eapply red_ty_compl_nat_r in Hconv.
      eapply red_ty_compl_nat_r in Hconv'.
      assert [Γ,, tNat |-[al] P ≅ P'] as [? ?%algo_conv_sound]%dup by (now eapply IHP) ; tea.
      eexists ; split.
      1: econstructor ; tea.
      + econstructor ; tea.
        2: now constructor.
        now eapply redty_sound.
      + eapply IHz ; tea.
        econstructor ; tea.
        symmetry.
        eapply typing_subst1 ; tea.
        do 2 constructor.
        boundary.
      + eapply IHS ; tea.
        econstructor ; tea.
        symmetry.
        eapply elimSuccHypTy_conv ; tea.
        boundary.
      + now symmetry.
      + etransitivity.
        2: eassumption.
        eapply typing_subst1 ; tea.
        eapply algo_conv_sound in Hconvn as [].
        2-3: now eexists.
        now econstructor.
    - intros * Hn IHn Hp [IHP _] ? T T'
        [? [[->]]]%termGen' [? [[->]]]%termGen'.
      edestruct IHn as [T'' [Hconvn Hconv Hconv']] ; tea.
      eapply red_ty_compl_empty_r in Hconv.
      eapply red_ty_compl_empty_r in Hconv'.
      assert [Γ,, tEmpty |-[al] P ≅ P'] as [? ?%algo_conv_sound]%dup by (now eapply IHP) ; tea.
      eexists ; split.
      1: econstructor ; tea.
      + econstructor ; tea.
        2: now constructor.
        now eapply redty_sound.
      + now symmetry.
      + etransitivity.
        2: eassumption.
        eapply typing_subst1 ; tea.
        eapply algo_conv_sound in Hconvn as [].
        2-3: now eexists.
        now econstructor.
    - intros * Hm IHm * [? [(A&B&[->])]]%termGen' [? [(A'&B'&[->])]]%termGen'.
      edestruct IHm as [T'' [? Hconv Hconv']] ; tea.
      eapply red_ty_compl_sig_r in Hconv as (?&?&[Hred]).
      eapply red_ty_compl_sig_r in Hconv' as (A''&B''&[Hred']).
      eapply redty_sound, whred_det in Hred' ; [..|eapply Hred].
      2-3: now constructor.
      injection Hred' ; intros ; subst ; clear Hred'.
      eexists ; split.
      + do 2 (econstructor ; tea).
        2: now constructor.
        now eapply redty_sound.
      + now transitivity A.
      + now transitivity A'.
    - intros * Hm IHm * [? [(A&B&[->])]]%termGen' [? [(A'&B'&[->])]]%termGen'.
      edestruct IHm as [T'' [Hconvm Hconv Hconv']] ; tea.
      eapply red_ty_compl_sig_r in Hconv as (?&?&[Hred]).
      eapply red_ty_compl_sig_r in Hconv' as (A''&B''&[Hred']).
      eapply redty_sound, whred_det in Hred' ; [..|eapply Hred].
      2-3: now constructor.
      injection Hred' ; intros ; subst ; clear Hred'.
      eexists ; split.
      + do 2 (econstructor ; tea).
        2: now constructor.
        now eapply redty_sound.
      + etransitivity ; tea.
        eapply typing_subst1 ; tea.
        eapply TermConv ; refold.
        1: now do 2 econstructor.
        now symmetry.
      + etransitivity ; tea.
        eapply typing_subst1 ; tea.
        eapply algo_conv_sound in Hconvm as [].
        2-3: now eexists.
        do 2 econstructor ; tea.
        now eapply RedConvTyC.
    - intros * Hn IHn HP [IHP _] Hr [_ IHr] ? T T' [? [[->]]]%termGen' [? [[->]]]%termGen'.
      edestruct IHn as [T'' [[Hconvn Hconvn']%dup Hconv Hconv']] ; tea.
      eapply red_ty_compl_id_r in Hconv as (?&?&?&[Hred]).
      eapply red_ty_compl_id_r in Hconv' as (A''&x''&y''&[Hred']).
      eapply redty_sound, whred_det in Hred' ; [..|eapply Hred].
      2-3: constructor.
      inversion Hred' ; subst ; clear Hred'.
      eapply algo_conv_sound in Hconvn' as [].
      2-3: now eexists.
      assert [Γ |-[de] A' ≅ A] by
        (etransitivity ; tea ; now symmetry).
      assert [Γ |-[ de ] x' ≅ x : A'].
      {
        etransitivity ; tea.
        1: now symmetry.
        econstructor ; tea.
        now symmetry.
      }
      eassert [(Γ,, A),, tId A⟨wk1 A⟩ x⟨wk1 A⟩ (tRel 0) |-[ al ] P ≅ P'] as [? ?%algo_conv_sound]%dup.
      {
        eapply IHP.
        1: boundary.
        eapply stability ; tea.
        eapply idElimMotiveCtxConv ; tea.
        2-3: now boundary.
        eapply ctx_refl ; boundary.
      }
      eexists ; split.
      1: econstructor ; tea.
      + econstructor ; tea.
        2: now constructor.
        now eapply redty_sound.
      + eapply IHr ; tea.
        econstructor ; tea.
        eapply typing_subst2.
        4: now symmetry.
        * boundary.
        * now econstructor.
        * cbn ; rewrite 2!wk1_ren_on, 2! shift_subst_eq.
          econstructor.
          1: econstructor ; tea.
          econstructor ; tea.
          econstructor.
          boundary.
      + eauto.
      + etransitivity ; [|eauto].
        eapply typing_subst2 ; tea.
        * boundary.
        * etransitivity.
          1: now symmetry.
          now econstructor.
        * cbn ; rewrite 2!wk1_ren_on, 2! shift_subst_eq.
          econstructor ; tea.
          eauto.
      + boundary.
      + eapply stability.
        1: boundary.
        eapply idElimMotiveCtxConv ; tea.
        1: eapply ctx_refl ; boundary.
        1: boundary.
        now eapply idElimMotiveCtx.
  Qed.

End Soundness.