(** * LogRel.Decidability.UntypedNegativeSoundness: implementation failure implies negation of typing for untyped conversion. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeConstructorsInj NeutralConvProperties.
From LogRel.Algorithmic Require Import BundledAlgorithmicTyping AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel Require Import UntypedAlgorithmicConversion.

From LogRel.Decidability Require Import Functions UntypedFunctions Views Soundness
  UntypedSoundness Completeness UntypedCompleteness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.
Set Structural Injection.

Hint Extern 10 =>
  match goal with
    | H : _ × _ |- _ => destruct H
    | H : ~ _ |- False => apply H
    | H : [× _, _ & _] |- _ => destruct H 
    | H : [× _, _, _ & _] |- _ => destruct H 
    | H : [× _, _, _, _ & _] |- _ => destruct H 
    | H : [× _, _, _, _, _ & _] |- _ => destruct H 
    | H : [× _, _, _, _, _, _ & _] |- _ => destruct H 
    | H : [× _, _, _, _, _, _, _ & _] |- _ => destruct H 
    | H : [× _, _, _, _, _, _, _, _ & _] |- _ => destruct H 
    | H : [× _, _, _, _, _, _, _, _, _ & _] |- _ => destruct H
  end : core.

Import DeclarativeTypingProperties.

Section ConvSoundNeg.

  Context `{!TypingSubst de} `{!TypeConstructorsInj de}
    `{!TermConstructorsInj de} `{!ConvNeutralConv de}.

  #[universes(polymorphic)]Definition uconv_sound_neg_pre
    (x : uconv_state × term × term) : Type :=
  match x with
  | (tm_state,t,u) => ∑ Γ A, [Γ |- t ∈ A] × [Γ |- u ∈ A]
  | (tm_red_state,t,u) => ∑ Γ A, [× whnf t, whnf u & ([Γ |- t ∈ A] × [Γ |- u ∈ A])]
  | (ne_state,m,n) => ∑ Γ, [× whne m, whne n & (well_typed Γ m × well_typed Γ n)]
  end.

  #[universes(polymorphic)]Definition uconv_sound_neg_type
    (x : uconv_state × term × term)
    (r : exn errors unit)
    (p : uconv_sound_neg_pre x) : Type :=
  match x, p, r with
  | _, _, (success _) => True
  | (tm_state,t,u), (Γ;(A;_)), (exception _) =>  ~ [Γ |-[de] t ≅ u ∈ A]
  | (tm_red_state,t,u), (Γ;(A;_)), (exception _) => ~ [Γ |-[de] t ≅ u ∈ A]
  | (ne_state,m,n), (Γ;_), (exception _) => ~ ∑ T, [Γ |-[de] m ~ n : T]
  end.

  Definition term_class_ty `{ta : tag} `{WfType ta} `{Typing ta} Γ A t :
    [Γ |-[ta] t : A] -> [Γ |-[ta] t ∈ (isterm A)] :=
    fun H => H.

  Definition type_class_ty `{ta : tag} `{WfType ta} `{Typing ta} Γ A :
    [Γ |-[ta] A] -> [Γ |-[ta] A ∈ istype] :=
    fun H => H.

  Lemma convtm_red' Γ A A' t t' u u' :
    [t ⤳* t'] ->
    [u ⤳* u'] ->
    [A ⤳* A'] ->
    [Γ |-[de] t ≅ u : A] ->
    [Γ |-[de] t' ≅ u' : A'].
  Proof.
    intros.
    econstructor.
    2: eapply subject_reduction_type ; boundary.
    etransitivity.
    2: etransitivity ; [eassumption|..].
    1: symmetry.
    all: eapply subject_reduction ; tea ; boundary.
  Qed.

  Lemma pair_conv_fst Γ A A' B B' t t' u u' T :
    [Γ |-[ de ] tPair A B t u ≅ tPair A' B' t' u' : T] ->
    [Γ |- t ≅ t' : A].
  Proof.
    intros Hty.
    eapply convtm_red'.
    3: reflexivity.
    1-2: eapply redalg_one_step, fstPair.
    econstructor.
    eapply convtm_conv ; tea.
    eapply boundary_tm_conv_l in Hty as (?&[->]&?)%termGen'.
    now symmetry.
  Qed.

  Lemma pair_conv_snd Γ A A' B B' t t' u u' T :
    [Γ |-[ de ] tPair A B t u ≅ tPair A' B' t' u' : T] ->
    [Γ |- u ≅ u' : B[t..]].
  Proof.
    intros Hty.
    eapply convtm_red'.
    3: reflexivity.
    1-2: eapply redalg_one_step, sndPair.
    econstructor.
    1: econstructor.
    1: eapply convtm_conv ; tea.
    all: eapply boundary_tm_conv_l in Hty as (?&[->]&?)%termGen'.
    1:  now symmetry.
    eapply typing_subst1.
    2: constructor ; boundary.
    constructor ; boundary.
  Qed.

  Lemma pair_conv_fst_ne Γ A B t u n' T :
    [Γ |-[ de ] tPair A B t u ≅ n' : T] ->
    [Γ |- t ≅ tFst n' : A].
  Proof.
    intros Hty.
    eapply convtm_red'.
    2,3: reflexivity.
    1: eapply redalg_one_step, fstPair.
    econstructor.
    eapply convtm_conv ; tea.
    eapply boundary_tm_conv_l in Hty as (?&[->]&?)%termGen'.
    now symmetry.
  Qed.

  Lemma pair_conv_snd_ne Γ A B t u n' T :
    [Γ |-[ de ] tPair A B t u ≅ n' : T] ->
    [Γ |- u ≅ tSnd n' : B[t..]].
  Proof.
    intros Hty.
    eapply convtm_red'.
    2,3: reflexivity.
    1: eapply redalg_one_step, sndPair.
    econstructor.
    1: econstructor.
    1: eapply convtm_conv ; tea.
    all: eapply boundary_tm_conv_l in Hty as (?&[->]&?)%termGen'.
    1:  now symmetry.
    eapply typing_subst1.
    2: constructor ; boundary.
    constructor ; boundary.
  Qed.

Lemma pair_conv_ne_fst Γ n A' B' t' u' T :
  [Γ |-[ de ] n ≅ tPair A' B' t' u' : T] ->
  [Γ |- tFst n ≅ t' : A'].
Proof.
  intros Hty.
  eapply convtm_red'.
  1,3: reflexivity.
  1: eapply redalg_one_step, fstPair.
  econstructor.
  eapply convtm_conv ; tea.
  eapply boundary_tm_conv_r in Hty as (?&[->]&?)%termGen'.
  now symmetry.
Qed.

Lemma pair_conv_ne_snd Γ n A' B' t' u' T :
  [Γ |-[ de ] n ≅ tPair A' B' t' u' : T] ->
  [Γ |- tSnd n ≅ u' : B'[t'..]].
Proof.
  intros Hty.
  eapply convtm_red'.
  1,3: reflexivity.
  1: eapply redalg_one_step, sndPair.
  econstructor.
  1: econstructor.
  1: eapply convtm_conv ; tea.
  2: eapply typing_subst1.
  2: now eapply pair_conv_ne_fst.
  all: eapply boundary_tm_conv_r in Hty as (?&[->]&?)%termGen'.
  1: now symmetry.
  constructor ; boundary.
Qed.


Lemma mismatch2_hd_view_ty Γ T V (tT : isType T) (tV : isType V) :
  build_nf_view2 T V = mismatch2 T V ->
  type_hd_view Γ tT tV = False.
Proof.
  destruct tT, tV ; cbn ; try reflexivity.
  all: simp build_nf_view2 ; cbn.
  1-6: congruence.
  do 2 (unshelve erewrite whne_nf_view1 ; tea ; cbn).
  congruence.
Qed.

Lemma mismatch2_hd_view_tm Γ A t u :
  [Γ |-[de] t : A] -> [Γ |-[de] u : A] ->
  whnf t -> whnf u ->
  build_nf_view2 t u = mismatch2 t u ->
  (∑ (nft : isType t) (nfu : isType u), type_hd_view Γ nft nfu = False) +
  ((∑ (nft : isNat t) (nfu : isNat u), nat_hd_view Γ nft nfu = False) +
  (∑ (nft : isId t) (nfu : isId u) , forall Γ A' x y, id_hd_view Γ A' x y nft nfu = False)).
Proof.
  intros Ht Hu wt wu.
  funelim (build_nf_view2 t u).
  all: try solve [
    congruence |
    match goal with
      | H : [_ |-[de] (tSort _) : _] |- _ => eapply termGen' in H as (?&[]&?)
    end |
    left ; unshelve (do 2 eexists) ; try constructor ; cbn ;
    now apply not_can_whne ; [..|eapply tm_view1_neutral_can] |
    right ; left ; unshelve (do 2 eexists) ; try constructor ; cbn ;
    now apply not_can_whne ; [..|eapply tm_view1_neutral_can]].

    1,4: unshelve (right ; right ; unshelve (do 2 eexists) ; econstructor ;
      [now apply not_can_whne ; [..|eapply tm_view1_neutral_can]|..] ;
      do 2 eexists ; reflexivity) ; easy.
    
    - destruct t1 ; try solve [congruence |
      left ; unshelve (do 2 eexists) ; try constructor ; cbn ;
      now apply not_can_whne ; [..|eapply tm_view1_neutral_can]].

    - destruct n ;
      try solve [
      congruence |
      right ; left ; unshelve (do 2 eexists) ; try constructor ; cbn ;
      now apply not_can_whne ; [..|eapply tm_view1_neutral_can]].

Qed.

Lemma mismatch2_hd_view_ne t u :
  whne t -> whne u ->
  ~ build_nf_view2 t u = mismatch2 t u.
Proof.
  intros Ht Hu.
  funelim (build_nf_view2 _ _) ; try solve [congruence|inversion Hu|inversion Ht].
  - destruct t1 ; inversion Hu.
  - destruct n ; inversion Hu.
Qed. 

  Lemma _implem_uconv_neg_sound :
    funrect _uconv uconv_sound_neg_pre uconv_sound_neg_type.
  Proof.
    intros x pre.
    funelim (_uconv x) ; cbn in pre |- *.

    3: simp uconv_ne ; cbn ; destruct (build_ne_view2 _ _) eqn:e ; cbn ; try easy.
    2: simp uconv_tm_red ; cbn ; destruct (build_nf_view2 _ _) eqn:e ; cbn ; try easy.
    1: simp uconv_tm ; cbn.

    all:
      repeat (match goal with | H : ∑ _, _ |- _ => destruct H as [? pre] end) ;
      repeat (match goal with | A : class |- _ => destruct A ; cbn in * end) ; try easy.
    
    - intros T' []%red_sound V' []%red_sound.
      eapply typeConvRed_prem2 in pre ; tea.
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros [|] _ Hnty ; cbn in * ; [easy|..].
      intros Hty.
      eapply Hnty.
      etransitivity.
      2: etransitivity ; tea.
      1: symmetry. 
      all: eapply RedConvTyC, subject_reduction_type ; eauto.
      all: boundary.
    
    - intros ? []%red_sound ? []%red_sound.
      eapply termConvRed_prem3 in pre ; tea.
      2: reflexivity.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] _ Hnty ; cbn in * ; [easy|..].
      intros Hty.
      eapply Hnty.
      eapply TermConv ; refold.
      2: constructor ; boundary.
      etransitivity.
      2: etransitivity ; [eassumption|..].
      1: symmetry.
      all: eapply RedConvTeC, subject_reduction ; [..|eassumption].
      all: boundary.

    - epose proof pre as [? ? [[]%typePiCongAlg_prem0]%dup].
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros [|] Hty ? ; cbn in *.
      2: now intros []%prod_ty_inj.
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [Hty _] ; cbn in Hty.
      edestruct typePiCongAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros [|] _ Hty' ; [easy|..].
      intros []%prod_ty_inj.
      eapply Hty', stability1 ; eauto.

    - epose proof pre as [?? [[(?&[-> _ _]&?)%termGen' _]]%dup].
      assert ([projT1 |-[ de ] tProd A B : U] × [projT1 |-[ de ] tProd A' B' : U]) as pre''.
      {
        split.
        all: eapply ty_conv ; [eauto|..].
        all: now symmetry.
      }
      edestruct termPiCongAlg_prem0 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in *.
      2:{ 
        intros ?.
        eapply Hnty, prod_tm_inj.
        econstructor ; now symmetry.
      }
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [_ ?]; tea.
      edestruct termPiCongAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty' ; cbn in * ; [easy|..].
      intros ?.
      eapply Hnty', stability1.
      1: now econstructor.
      eapply prod_tm_inj.
      now eapply convtm_conv ; [..|symmetry].

    - epose proof pre as [? ? [[]%typeSigCongAlg_prem0]%dup].
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros [|] Hty ? ; cbn in *.
      2: now intros []%sig_ty_inj.
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [Hty _] ; cbn in Hty.
      edestruct typeSigCongAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros [|] _ Hty' ; [easy|..].
      intros []%sig_ty_inj.
      now eapply Hty'.

    - epose proof pre as [?? [pre' [(?&[-> _ _]&?)%termGen' _]]%dup].
      assert ([projT1 |-[ de ] tSig A B : U] × [projT1 |-[ de ] tSig A' B' : U]) as pre''.
      {
        split.
        all: eapply ty_conv ; [eauto|..].
        all: now symmetry.
      }
      edestruct termSigCongAlg_prem0 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in *.
      2:{ 
        intros ?.
        eapply Hnty, sig_tm_inj.
        now econstructor ; [..|symmetry].
      }
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [_ ?]; tea.
      edestruct termSigCongAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty' ; cbn in * ; [easy|..].
      intros ?.
      eapply Hnty', sig_tm_inj.
      now eapply convtm_conv ; [..|symmetry].
    
    - epose proof pre as [_ _ [pre' []%typeIdCongAlg_prem0]%dup].
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros [|] Hty ? ; cbn.
      2: now intros [? _]%id_ty_inj.
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [? _] ; eauto.
      edestruct typeIdCongAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty' ? ; cbn in *.
      2: now intros []%id_ty_inj.
      eapply implem_uconv_graph, uconv_sound_decl in Hty' ; tea.
      edestruct typeIdCongAlg_prem2 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] ? Hty'' ; cbn in * ; [easy|..].
      now intros []%id_ty_inj.
    
    - epose proof pre as [?? [pre' [(?&[-> _ _]&?)%termGen' _]]%dup].
      assert ([projT1 |-[ de ] tId A x y : U] × [projT1 |-[ de ] tId A' x' y' : U]) as pre''.
      {
        split.
        all: eapply ty_conv ; [eauto|..].
        all: now symmetry.
      }
      edestruct termIdCongAlg_prem0 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in *.
      2: now eintros ?%convtm_conv%id_tm_inj ; [..|now symmetry] ; eauto.
      eapply implem_uconv_graph, uconv_sound_decl in Hty ; eauto.
      edestruct termIdCongAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty'%implem_uconv_graph Hnty' ; cbn in *.
      2: now eintros ?%convtm_conv%id_tm_inj ; [..|now symmetry] ; eauto.
      eapply uconv_sound_decl in Hty' ; tea.
      edestruct termIdCongAlg_prem2 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty, type_class_ty.
      intros [|] ? Hty'' ; cbn in * ; [easy|..].
      now eintros ?%convtm_conv%id_tm_inj ; [..|now symmetry] ; eauto.

    - destruct pre as [wt wu [Ht Hu]].
      eapply type_isType in Ht ; tea.
      inversion Ht ; inversion H.

    - edestruct LamCongUAlg_prem0 as (?&[]) ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in * ; [easy|..].
      eintros Hty'%convtm_conv ; [..|now symmetry].
      eapply Hnty.
      eapply convtm_red'.
      3: reflexivity.
      1,2: now eapply redalg_one_step, eta_expand_beta.
      eapply convtm_meta_conv.
      3: reflexivity.
      2: shelve.
      econstructor.
      2: now do 2 econstructor ; [boundary|econstructor].
      erewrite <- !wk1_ren_on.
      erewrite wk_prod.
      eapply typing_wk ; boundary.
      Unshelve.
      now bsimpl.
      
    - destruct pre as [wt wu [Ht Hu]].
      eapply type_isType in Ht ; tea.
      inversion Ht ; inversion H.

    - edestruct LamNeUAlg_prem0 as (?&[]) ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in * ; [easy|..].
      eintros Hty'%convtm_conv ; [..|now symmetry].
      eapply Hnty.
      eapply convtm_red'.
      3: reflexivity.
      1: now eapply redalg_one_step, eta_expand_beta.
      1: reflexivity.
      eapply convtm_meta_conv.
      3: reflexivity.
      2: shelve.
      econstructor.
      2: now do 2 econstructor ; [boundary|econstructor].
      erewrite <- !wk1_ren_on.
      erewrite wk_prod.
      eapply typing_wk ; boundary.
      Unshelve.
      now bsimpl.
    
    - destruct pre as [wt wu [Ht Hu]].
      eapply type_isType in Hu ; tea.
      inversion Hu ; inversion H.

    - edestruct NeLamUAlg_prem0 as (?&[]) ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in * ; [easy|..].
      eintros Hty'%convtm_conv ; [..|now symmetry].
      eapply Hnty.
      eapply convtm_red'.
      3: reflexivity.
      2: now eapply redalg_one_step, eta_expand_beta.
      1: reflexivity.
      eapply convtm_meta_conv.
      3: reflexivity.
      2: shelve.
      econstructor.
      2: now do 2 econstructor ; [boundary|econstructor].
      erewrite <- !wk1_ren_on.
      erewrite wk_prod.
      eapply typing_wk ; boundary.
      Unshelve.
      now bsimpl.

    - destruct pre as [wt wu [Ht Hu]].
      eapply type_isType in Hu ; tea.
      inversion Hu ; inversion H.
        
    - epose proof pre as [?? [pre' [(?&[->]&?)%termGen']]%dup].
      edestruct termSuccCongAlg_prem0.
      1: split ; eapply ty_conv ; eauto ; now symmetry.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] ? Hty ; cbn in * ; [easy|..].
      eintros Hconv%convtm_conv ; [..|now symmetry].
      unshelve eapply nat_conv_inj in Hconv.
      1-2: now constructor.
      now cbn in Hconv.

    - destruct pre as [wt wu [Ht Hu]].
      epose proof Ht as Ht'%type_isType ; tea.
      inversion Ht' ; inversion H.

    - edestruct PairCongUAlg_prem0 as [] ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in *.
      2: now eintros ?%pair_conv_fst.
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [_ ?].
      edestruct PairCongUAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty' ; cbn in * ; [easy|..].
      now eintros ?%pair_conv_snd.

    - destruct pre as [wt wu [Ht Hu]].
      epose proof Ht as Ht'%type_isType ; tea.
      inversion Ht' ; inversion H.

    - edestruct PairNeUAlg_prem0 as [] ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in *.
      2: now eintros ?%pair_conv_fst_ne.
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [_ ?].
      edestruct PairNeUAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty' ; cbn in * ; [easy|..].
      now eintros ?%pair_conv_snd_ne.
      
    - destruct pre as [wt wu [Ht Hu]].
      epose proof Hu as Hu'%type_isType ; tea.
      inversion Hu' ; inversion H.

    - edestruct NePairUAlg_prem0 as [] ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty ; cbn in *.
      2: now eintros ?%pair_conv_ne_fst.
      eapply implem_uconv_graph, uconv_sound_decl in Hty as [_ ?].
      edestruct NePairUAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros [|] Hty Hnty' ; cbn in * ; [easy|..].
      now eintros ?%pair_conv_ne_snd.

    - destruct pre as [? ? ?].
      eapply nf_view2_neutral_can in e as [wt%not_can_whne wu%not_can_whne] ; tea.
      edestruct typeNeuConvAlg_prem2 ; cycle 2 ; tea.
      unshelve eexists.
      1: eexists ; now split.
      intros [|] _ Hnty ; cbn in * ; [easy|..].
      unshelve eintros ?%ty_conv_inj.
      1-2: now constructor.
      cbn in *.
      eauto.
      eapply Hnty.
      eexists.
      now eapply conv_neu_conv.

    - destruct pre as [? ? ?].
      eapply nf_view2_neutral_can in e as [wt%not_can_whne wu%not_can_whne] ; tea.
      unshelve eexists.
      1: now repeat eexists.
      cbn in *.
      intros [|] _ Hnty ; cbn in * ; eauto.
      intros ?.
      eapply Hnty.
      eexists.
      now eapply conv_neu_conv.

    - destruct pre as [wt wu [Ht Hu]].
      eapply type_isType in Ht, Hu ; tea.
      unshelve eintros H_view%ty_conv_inj ; tea.
      eapply mismatch2_hd_view_ty in e.
      now erewrite e in H_view.

    - intros Hty.
      assert (whne t -> whne u -> False) by
       (now intros ; eapply mismatch2_hd_view_ne ; cycle -1).
      eapply mismatch2_hd_view_tm in e as [e|[e|e]] ; eauto.
      + destruct e as (nft&nfu&e).
        enough (type_hd_view _ nft nfu) as Hhd by now rewrite e in Hhd.
        apply ty_conv_inj.
        econstructor.
        econstructor ; tea.
        destruct nft.
        all: try solve [eapply boundary_tm_conv_l in Hty as (?&Hgen&?)%termGen' ;
          cbn in Hgen ; try easy ; prod_hyp_splitter ; subst ; try solve [now symmetry]].
        destruct nfu ; [..|easy].
        all: solve [eapply boundary_tm_conv_r in Hty as (?&Hgen&?)%termGen' ;
          cbn in Hgen ; try easy ; prod_hyp_splitter ; subst ; try solve [now symmetry]].
      + destruct e as (nft&nfu&e).
        enough (nat_hd_view _ nft nfu) as Hhd by now rewrite e in Hhd.
        apply nat_conv_inj.
        econstructor ; tea.
        destruct nft.
        all: try solve [eapply boundary_tm_conv_l in Hty as (?&Hgen&?)%termGen' ;
          cbn in Hgen ; try easy ; prod_hyp_splitter ; subst ; try solve [now symmetry]].
        destruct nfu ; [..|easy].
        all: solve [eapply boundary_tm_conv_r in Hty as (?&Hgen&?)%termGen' ;
          cbn in Hgen ; try easy ; prod_hyp_splitter ; subst ; try solve [now symmetry]].

      + destruct e as (nft&nfu&e).
        enough (∑ Γ A x y, id_hd_view Γ A x y nft nfu) as (?&?&?&?&?Hhd)
          by now rewrite e in Hhd.
        destruct nft.
        * epose proof Hty as (?&Hgen&?)%boundary_tm_conv_l%termGen' ;
          cbn in Hgen ; try easy ; prod_hyp_splitter ; subst.
          do 4 eexists.
          eapply id_conv_inj.
          econstructor ; tea.
          now symmetry.
        * destruct nfu ; [..|easy].
          epose proof Hty as (?&Hgen&?)%boundary_tm_conv_r%termGen' ;
          cbn in Hgen ; try easy ; prod_hyp_splitter ; subst.
          do 4 eexists.
          eapply id_conv_inj.
          econstructor ; tea.
          now symmetry.

    - destruct (Nat.eqb_spec n n') ; cbn ; try easy.
      intros [? (?&[[= ->]])%neuConvGen].
      eauto.

    - edestruct neuAppCongAlg_prem0 ; eauto.
      destruct pre as [wn wn' []].
      inversion wn ; inversion wn' ; subst.
      unshelve eexists.
      1: eexists ; now split.
      intros [|] Hty%implem_uconv_graph Hnty ; cbn in *.
      2: now intros [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
      eapply uconv_sound_decl in Hty as [? Hty] ; eauto.
      eapply AppCongUAlg_bridge in Hty as (?&?&[? Hty]) ; eauto.
      edestruct neuAppCongAlg_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros  [|] _ Hnty' ; [easy|..].
      intros [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
      eapply Hnty'.
      econstructor ; tea.
      eapply prod_ty_inj, Hty.
      boundary.

    - edestruct neuNatElimCong_prem0 ; eauto.
      destruct pre as [wn wn' []].
      inversion wn ; inversion wn' ; subst.
      unshelve eexists.
      1: eexists ; now split.
      intros [|] Hty%implem_uconv_graph Hnty ; cbn in *.
      2: now intros [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
      eapply uconv_sound_decl in Hty as [? Hty] ; eauto.
      eapply NatElimCongUAlg_bridge in Hty as [? Hty] ; eauto.
      edestruct neuNatElimCong_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros  [|] HP%implem_uconv_graph Hnty' ; cbn.
      2: now intros [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
      eapply uconv_sound_decl in HP as [? _].
      edestruct neuNatElimCong_prem2 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros  [|] Hz%implem_uconv_graph ? ; cbn.
      2: now intros [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
      eapply uconv_sound_decl in Hz as [_ ?].
      edestruct neuNatElimCong_prem3 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros  [|] Hs%implem_uconv_graph ? ; cbn ; [easy|..].
      now intros [? (?&?&?&?&[[=]])%neuConvGen] ; subst.

    - edestruct neuEmptyElimCong_prem0 ; eauto.
      destruct pre as [wn wn' []].
      inversion wn ; inversion wn' ; subst.
      unshelve eexists.
      1: eexists ; now split.
      intros [|] Hty%implem_uconv_graph Hnty ; cbn in *.
      2: now intros [? (?&?&[[=]])%neuConvGen] ; subst.
      eapply uconv_sound_decl in Hty as [? Hty] ; eauto.
      eapply EmptyElimCongUAlg_bridge in Hty as [? Hty] ; eauto.
      edestruct neuEmptyElimCong_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros  [|] HP%implem_uconv_graph Hnty' ; cbn ; [easy|..].
      now intros [? (?&?&[[=]])%neuConvGen] ; subst.

    - edestruct neuFstCongAlg_prem0 ; eauto.
      destruct pre as [wn wn' []].
      inversion wn ; inversion wn' ; subst.
      unshelve eexists.
      1: eexists ; now split.
      intros [|] Hty%implem_uconv_graph Hnty ; cbn in * ; [easy|..].
      now intros [? (?&?&?&[[=]])%neuConvGen] ; subst.

    - edestruct neuSndCongAlg_prem0 ; eauto.
      destruct pre as [wn wn' []].
      inversion wn ; inversion wn' ; subst.
      unshelve eexists.
      1: eexists ; now split.
      intros [|] Hty%implem_uconv_graph Hnty ; cbn in * ; [easy|..].
      now intros [? (?&?&?&[[=]])%neuConvGen] ; subst.

    - edestruct neuIdElimCong_prem0 ; eauto.
      destruct pre as [wn wn' []].
      inversion wn ; inversion wn' ; subst.
      unshelve eexists.
      1: eexists ; now split.
      intros [|] Hty%implem_uconv_graph Hnty ; cbn in *.
      2: now intros [? (?&?&?&?&?&?&[[=]])%neuConvGen] ; subst.
      eapply uconv_sound_decl in Hty as [? Hty] ; eauto.
      eapply IdElimCongUAlg_bridge in Hty as (?&?&?&[? Hty]) ; eauto.
      edestruct neuIdElimCong_prem1 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using type_class_ty.
      intros  [|] HP%implem_uconv_graph Hnty' ; cbn.
      2: now intros [? (?&?&?&?&?&?&[[=]])%neuConvGen] ; subst.
      eapply uconv_sound_decl in HP as [? _].
      edestruct neuIdElimCong_prem2 ; eauto.
      unshelve eexists.
      1: repeat eexists ; eauto using term_class_ty.
      intros  [|] Hz%implem_uconv_graph ? ; cbn ; [easy|..].
      now intros [? (?&?&?&?&?&?&[[=]])%neuConvGen] ; subst.

    - intros [? ?%neuConvGen].
      destruct t ; cbn in * ; try solve [easy].
      all: prod_hyp_splitter ; subst.
      all: simp build_ne_view2 in e ; cbn in *.
      all: congruence.
    
  Qed.

  Corollary implem_tconv_sound_neg Γ T V e :
    graph tconv (Γ,T,V) (exception e) ->
    [Γ |-[de] T] -> [Γ |-[de] V] ->
    ~ [Γ |-[de] T ≅ V].
  Proof.
    intros Hgraph **.
    eapply (funrect_graph _
      (fun '(Γ',T',V') => [Γ' |-[de] T'] × [Γ' |-[de] V'])
      (fun '(Γ',T',V') r => match r with | success _ => True | exception _ => ~ [Γ' |-[de] T' ≅ V'] end)) in Hgraph ; try easy.
    
    intros (?&?&?) [].
    funelim (tconv _) ; cbn.
    inversion_clear eqargs.
    intros [] ; cbn ; [easy|].
    eintros ?%funrect_graph.
    2: now apply _implem_conv_neg_sound.
    all: now cbn in *.
  Qed.

End ConvSoundNeg.