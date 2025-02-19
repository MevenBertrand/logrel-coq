(** * LogRel.Decidability.NegativeSoundness: implementation failure implies negation of typing. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeConstructorsInj NeutralConvProperties.
From LogRel.Algorithmic Require Import BundledAlgorithmicTyping AlgorithmicConvProperties AlgorithmicTypingProperties.

From LogRel.Decidability Require Import Functions Soundness Completeness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.
Set Structural Injection.

Import DeclarativeTypingProperties.

Lemma ty_mismatch_hd_view Γ T V (tT : isType T) (tV : isType V) :
  build_nf_ty_view2 T V = ty_mismatch T V ->
  type_hd_view Γ tT tV = False.
Proof.
  destruct tT, tV ; cbn ; try reflexivity.
  all: simp build_nf_ty_view2 ; cbn.
  1-6: congruence.
  do 2 (unshelve erewrite whne_ty_view1 ; tea) ; cbn.
  congruence.
Qed.

Lemma univ_mismatch_hd_view Γ s T V (tT : isType T) (tV : isType V) :
  build_nf_view3 (tSort s) T V = types s (ty_mismatch T V) ->
  univ_hd_view Γ tT tV = False.
Proof.
  destruct tT, tV ; cbn ; try reflexivity.
  all: simp build_nf_view3 build_nf_ty_view2 ; cbn.
  1-5: intros [=].
  do 2 (unshelve erewrite whne_ty_view1 ; tea) ; cbn.
  discriminate.
Qed.

Lemma zip_can t s : ~ isCanonical (zip1 t s).
Proof.
  destruct s ; cbn.
  all: now intros c ; inversion c.
Qed.

Lemma mismatch_hd_view Γ A t u (tA : isType A) :
  whnf t -> whnf u ->
  build_nf_view3 A t u = mismatch A t u ->
  (∑ (nft : isNat t) (nfu : isNat u), A = tNat × nat_hd_view Γ nft nfu = False) +
  (∑ (nft : isId t) (nfu : isId u) A' x y, A = tId A' x y × id_hd_view Γ A' x y nft nfu = False).
Proof.
  intros wt wu.
  destruct tA ; cbn.
  all: simp build_nf_view3 build_nf_ty_view2 ; cbn.
  all: try solve [intros [=]].
  - destruct (build_nf_view1 t), (build_nf_view1 u) ; cbn.
    all: try solve [intros [=]].
    all: destruct n ; cbn ; try solve [intros [=]].
    all: destruct n0 ; cbn ; try solve [intros [=]].
    all: unshelve (intros _ ; left ; do 2 eexists).
    all: try solve [constructor].
    1-8: econstructor ; eapply not_can_whne ; tea ; solve [now apply zip_can | intros c ; inversion c].
    all: now cbn.

  - destruct (build_nf_view1 t), (build_nf_view1 u) ; cbn.
    all: solve [intros [=]].

  - destruct (build_nf_view1 t), (build_nf_view1 u) ; cbn.
    all: try solve [intros [=]]. 
    all: destruct n ; cbn ; try solve [intros [=]].
    all: (intros _ ; right ; do 5 eexists).
    all: split ; [reflexivity|..].
    Unshelve.
    all: try solve [constructor].
    5-8: econstructor ; eapply not_can_whne ; tea ; solve [now apply zip_can | intros c ; inversion c].
    all: now cbn.
    
  - unshelve erewrite whne_ty_view1 ; tea ; cbn.
    destruct (build_nf_view1 t) ; cbn ; try solve [intros [=]].
    destruct (build_nf_view1 u) ; cbn ; solve [intros [=]].

Qed.

Lemma prod_tm_inj `{TermConstructorsInj de} Γ A B A' B' :
  [Γ |-[de] tProd A B ≅ tProd A' B' : U] ->
  [Γ |-[de] A' ≅ A : U] × [Γ,,A' |-[de] B ≅ B' : U].
Proof.
  unshelve eintros ?%univ_conv_inj.
  1-2: now econstructor.
  now cbn in *.
Qed.

Lemma sig_tm_inj `{TermConstructorsInj de} Γ A B A' B' :
  [Γ |-[de] tSig A B ≅ tSig A' B' : U] ->
  [Γ |-[de] A ≅ A' : U] × [Γ,,A |-[de] B ≅ B' : U].
Proof.
  unshelve eintros ?%univ_conv_inj.
  1-2: now econstructor.
  now cbn in *.
Qed.

Lemma id_tm_inj `{TermConstructorsInj de} Γ A x y A' x' y' :
  [Γ |-[de] tId A x y ≅ tId A' x' y' : U] ->
  [× [Γ |-[de] A ≅ A' : U], [Γ |-[de] x ≅ x' : A] & [Γ |-[de] y ≅ y' : A]].
Proof.
  unshelve eintros ?%univ_conv_inj.
  1-2: now econstructor.
  now cbn in *.
Qed.

Section ConvSoundNeg.
  Import AlgorithmicTypedConvData.

  Context `{!TypingSubst de} `{!TypeConstructorsInj de}
    `{!TermConstructorsInj de} `{!ConvNeutralConvPos de}.

  #[universes(polymorphic)]Definition conv_sound_pre
    (x : conv_full_dom) : Type :=
  match x with
  | (ty_state;Γ;_;T;V) => [Γ |-[de] T] × [Γ |-[de] V]
  | (ty_red_state;Γ;_;T;V) => [× whnf T, whnf V & [Γ |-[de] T] × [Γ |-[de] V]]
  | (tm_state;Γ;A;t;u) => [Γ |-[de] t : A] × [Γ |-[de] u : A]
  | (tm_red_state;Γ;A;t;u) => [× whnf A, whnf t, whnf u & [Γ |-[de] t : A] × [Γ |-[de] u : A]]
  | (ne_state;Γ;_;m;n) => (whne m × whne n) × (well_typed (ta := de) Γ m × well_typed (ta := de) Γ n)
  | (ne_red_state;Γ;_;m;n) => (whne m × whne n) × (well_typed (ta := de) Γ m × well_typed (ta := de) Γ n)
  end.

  #[universes(polymorphic)]Definition conv_sound_type
      (x : conv_full_dom)
      (p : conv_sound_pre x)
      (r : conv_full_cod x) : Type :=
    match x, r with
    | (ty_state;Γ;_;T;V), (exception _) => ~ [Γ |-[de] T ≅ V]
    | (ty_red_state;Γ;_;T;V), (exception _) => ~ [Γ |-[de] T ≅ V]
    | (tm_state;Γ;A;t;u), (exception _) => ~ [Γ |-[de] t ≅ u : A]
    | (tm_red_state;Γ;A;t;u), (exception _) => ~ [Γ |-[de] t ≅ u : A]
    | (ne_state;Γ;_;m;n), (exception _) => ~ ∑ T, [Γ |-[de] m ~ n : T]
    | (ne_red_state;Γ;_;m;n), (exception _) => ~ ∑ T, ([Γ |-[de] m ~ n : T] × whnf T)
    | _, success _ =>  True
    end.

  Lemma _implem_conv_neg_sound :
    funrect _conv conv_sound_pre conv_sound_type.
  Proof.
    intros x pre.
    funelim (_conv x) ; cbn in pre |- *.
    
    6: simp conv_ne_red ; cbn.
    5: simp conv_ne ; destruct (build_ne_view2 _ _) eqn:e ; cbn ; try easy.
    4: simp conv_tm_red ; destruct (build_nf_view3 _ _ _) as [??? [] | | | | | | | | ]  eqn:e ;
      cbn ; try easy.
    3: simp conv_tm ; cbn.
    2: simp conv_ty_red ; cbn ; destruct (build_nf_ty_view2 _ _) eqn:e ; cbn.
    1: simp conv_ty ; cbn.
    all: try easy.
    
    - intros T' []%red_sound V' []%red_sound.
      eapply typeConvRed_prem2 in pre as [[] Hpost2]%dup ; tea.
      split ; [split|..] ; tea.
      intros [|] _ Hnty ; cbn in *.
      1: easy.
      intros _ Hty.
      eapply Hnty.
      etransitivity.
      2: etransitivity ; tea.
      1: symmetry. 
      all: eapply RedConvTyC, subject_reduction_type ; eauto.
      all: boundary.

    - destruct pre as [_ _ [pre [[]]%typePiCongAlg_prem0%dup]%dup].
      split ; [easy|..].
      intros [|] Hty ? ; cbn.
      2: now intros _ []%prod_ty_inj.
      eapply implem_conv_graph, algo_conv_sound in Hty ; cbn in * ; tea.
      eapply dup in pre as [pre ?%typePiCongAlg_prem1] ; tea.
      split ; [easy|..].
      intros [|] _ Hty' ; [easy|..].
      intros _ []%prod_ty_inj.
      eapply Hty', stability1 ; eassumption.

    - destruct pre as [_ _ [pre [[]]%typeSigCongAlg_prem0%dup]%dup].
      split ; [easy|..].
      intros [|] Hty ? ; cbn in *.
      2: now intros _ []%sig_ty_inj.
      eapply implem_conv_graph, algo_conv_sound in Hty ; tea.
      eapply dup in pre as [pre ?%typeSigCongAlg_prem1] ; tea.
      split ; [easy|..].
      intros [|] ? Hty' ; [easy|..].
      now intros _ []%sig_ty_inj.
    
    - destruct pre as [_ _ [pre [[]]%typeIdCongAlg_prem0%dup]%dup].
      split ; [easy|..].
      intros [|] Hty ? ; cbn.
      2: now intros _ [? _]%id_ty_inj.
      eapply implem_conv_graph, algo_conv_sound in Hty ; tea.
      eapply dup in pre as [pre [[]]%typeIdCongAlg_prem1%dup] ; tea.
      split ; [easy|..].
      intros [|] Hty' ? ; cbn in *.
      2: now intros _ []%id_ty_inj.
      eapply implem_conv_graph, algo_conv_sound in Hty' ; tea.
      eapply dup in pre as [pre ?%typeIdCongAlg_prem2] ; tea.
      split ; [easy|..].
      intros [|] ? Hty'' ; cbn in * ; [easy|..].
      now intros _ []%id_ty_inj.

    - eapply ty_view2_neutral_can in e as [].
      destruct pre as [?%not_can_whne ?%not_can_whne pre] ; tea.
      eapply dup in pre as [pre [[]]%typeNeuConvAlg_prem2%dup] ; tea.
      split ; [now split|..].
      intros [|] _ Hty ; cbn in * ; [easy|..].
      unshelve eintros _ Hty'%ty_conv_inj.
      1-2: now econstructor.
      cbn in Hty'.
      unshelve eapply conv_neu_conv_p in Hty' ; eauto.
      gen_typing.

    - destruct pre as [wt wu [Ht Hu]].
      eapply type_isType in Ht, Hu ; tea.
      unshelve eapply ty_mismatch_hd_view in e ; tea.
      unshelve eintros _ H_view%ty_conv_inj ; tea.
      rewrite e in H_view.
      eassumption.

    - intros ? []%red_sound ? []%red_sound ? []%red_sound.
      eapply termConvRed_prem3 in pre as [[] Hpost3]%dup ; tea.
      split ; [split|..] ; tea.
      intros [|] _ Hnty ; cbn in * ; [easy|..].
      intros _ Hty.
      eapply Hnty.
      eapply TermConv ; refold.
      2: eapply RedConvTyC, subject_reduction_type ; eauto ; boundary.
      etransitivity.
      2: etransitivity ; [eassumption|..].
      1: symmetry.
      all: eapply RedConvTeC, subject_reduction ; [..|eassumption].
      all: boundary.

    - destruct s.
      destruct pre as [??? [pre [[]]%termPiCongAlg_prem0%dup]%dup].
      split ; [easy|..].
      intros [|] Hty ? ; cbn in *.
      2:now intros _ []%prod_tm_inj.
      eapply implem_conv_graph, algo_conv_sound in Hty ; tea.
      eapply dup in pre as [pre ?%termPiCongAlg_prem1] ; tea.
      split ; [easy|..].
      intros [|] ? Hty' ; [easy|..].
      intros _ []%prod_tm_inj.
      eapply Hty', stability1 ; tea.
      now econstructor.
      
    - destruct s.
      destruct pre as [??? [pre [[]]%termSigCongAlg_prem0%dup]%dup].
      split ; [easy|..].
      intros [|] Hty ? ; cbn in *.
      2:now intros _ []%sig_tm_inj.
      eapply implem_conv_graph, algo_conv_sound in Hty ; tea.
      eapply dup in pre as [pre ?%termSigCongAlg_prem1] ; tea.
      split ; [easy|..].
      intros [|] ? Hty' ; [easy|..].
      now intros _ []%sig_tm_inj.

    - destruct s.
      destruct pre as [??? [pre [[]]%termIdCongAlg_prem0%dup]%dup].
      split ; [easy|..].
      intros [|] Hty ? ; cbn in *.
      2:now intros _ []%id_tm_inj.
      eapply implem_conv_graph, algo_conv_sound in Hty ; tea.
      eapply dup in pre as [pre [? []]%termIdCongAlg_prem1%dup] ; tea.
      split ; [easy|..].
      intros [|] Hty'%implem_conv_graph ? ; cbn in *.
      2: now intros _ []%id_tm_inj.
      eapply dup in Hty' as [Hty' ?%algo_conv_sound] ; tea.
      eapply dup in pre as [pre ?%termIdCongAlg_prem2] ; tea.
      split ; [easy|..].
      intros [|] ? Hty'' ; cbn in * ; [easy|..].
      now intros _ []%id_tm_inj.

    - destruct pre as [??? [pre [[]]%termNeuConvAlg_prem0%dup]%dup] ; tea.
      eapply whnf_view3_ty_neutral_can in e as [?%not_can_whne ?%not_can_whne] ; tea.
      split ; [now split|..].
      intros [|] ? Hty ; cbn ; [easy|..].
      
      destruct s.
      unshelve eintros _ ?%conv_neu_conv_p ; eauto.
      gen_typing.

    - destruct s.
      destruct pre as [_ wt wu [Ht Hu]].
      eapply wft_term, type_isType in Ht, Hu ; tea.
      unshelve eapply univ_mismatch_hd_view in e ; tea.
      unshelve eintros _ H_view%univ_conv_inj ; tea.
      rewrite e in H_view.
      eassumption.

    - destruct pre as [??? [pre [[]]%termFunConvAlg_prem2%dup]%dup] ; tea.
      split ; [easy|..].
      intros [|] ? Hty ; cbn ; [easy|..].

      intros _ Hty'.
      eapply Hty.
      eapply convtm_meta_conv.
      3: reflexivity.
      1: econstructor.
      1: erewrite <- !wk1_ren_on.
      1: eapply convtm_meta_conv.
      1: eapply convtm_wk ; tea.
      + boundary.
      + cbn ; reflexivity.
      + reflexivity.
      + eapply convtm_meta_conv.
        1: do 2 econstructor.
        1: boundary.
        constructor.
        all: now bsimpl.
      + bsimpl ; refold.
        rewrite scons_eta'.
        now bsimpl.
    
    - destruct pre as [??? [pre [[]]%termSuccCongAlg_prem0%dup]%dup] ; tea.
      split ; [easy|..].
      intros [|] ? Hty ; cbn in * ; [easy|..].
      unshelve eintros _ ?%nat_conv_inj.
      1-2: now constructor.
      cbn in *.
      eauto.
        
    - destruct pre as [??? [pre [[]]%termPairConvAlg_prem2%dup]%dup] ; tea.
      split ; [easy|..].
      intros [|] ; cbn in *.
      + eintros Hpost ? ; tea.
        eapply implem_conv_graph, algo_conv_sound in Hpost ; tea.
        eapply termPairConvAlg_prem3 in Hpost ; tea.
        split ; [easy|..].
        intros [|].
        1: now econstructor.
        intros ? Hnty ? Hty.
        eapply Hnty.
        now econstructor.
      + intros ? Hnty ? Hty.
        eapply Hnty.
        now econstructor.
    
    - destruct pre as [??? [pre [[]]%termNeuConvAlg_prem0%dup]%dup] ; tea.
      eapply whnf_view3_neutrals_can in e as [Wa Wn Wn'] ; tea.
      split.
      1: split ; tea ; eauto using not_can_whne.
      intros [|] ; cbn ; [easy|..].
      intros ? Hnty ? Hty.
      eapply not_can_whne in Wn, Wn' ; eauto.
      eapply Hnty.
      exists A.
      now eapply conv_neu_conv_p.
    
    - destruct pre as [w ?? []].
      eapply type_isType in w.
      2: boundary.
      unshelve eapply mismatch_hd_view in e as [(?&?&[->])|(?&?&?&?&?&[->])] ; tea.
      + unshelve eintros _ ?%nat_conv_inj ; tea.
        now rewrite e in H.

      + unshelve eintros _ ?%id_conv_inj ; tea.
        now rewrite e in H.

    - destruct (Nat.eqb_spec n n') ; cbn.
      + destruct pre as [[] [_ [? [? [(?& []) ?]]%termGen']]] ; subst.
        erewrite ctx_access_complete ; cbn.
        1: econstructor.
        all: eassumption.
        
      + intros _ [? (?&[[= ->]])%neuConvGen].
        eauto.
      
    - destruct pre as [[wn wn'] [pre [[] ]%neuAppCongAlg_prem0%dup]%dup] ; eauto.
      inversion wn ; inversion wn' ; subst.
      split ; [easy|..].
      intros [T|] ; cbn in *.
      + intros [Hpost]%implem_conv_graph ; tea ; refold.
        eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
        eapply dup in pre as [pre [[? (?&[? [? [-> Hf]]]&?)%termGen'] _]].
        destruct T ; cbn ; try easy.
        edestruct neuAppCongAlg_prem1 ; eauto.

        cbn.
        split ; [eauto|..].
        intros [|] ? ; cbn in * ; [easy|..].

        intros Hneg ? [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
        apply Hneg.
        eapply TermConv ; refold ; tea.
        eapply prod_ty_inj, Hfu.
        eauto using conv_neu_sound with boundary.

      + intros ? Hneg ? [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
        apply Hneg.
        eexists ; split ; eauto.
        now constructor.
  
    - destruct pre as [[wn wn'] [pre [[] ]%neuNatElimCong_prem0%dup]%dup] ; eauto.
      inversion wn ; inversion wn' ; subst.
      split ; [easy|..].
      intros [T|] ; cbn in *.
      2: shelve.

      intros [Hpost]%implem_conv_graph ; tea.
      eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
      eapply dup in pre as [pre [[? (?&[-> ??? Hn]&?)%termGen'] _]].
      destruct T ; try easy.
      eapply dup in pre as [pre [ []]%neuNatElimCong_prem1%dup] ; eauto.
      cbn.
      split ; [easy|..].
      intros [|] ; cbn.
      2: shelve.

      eintros [Hpost1]%implem_conv_graph%algo_conv_sound%dup ; tea ; cbn in *.
      eapply neuNatElimCong_prem2, dup in Hpost1 as [Hpost1 []] ; eauto.
      split ; [easy|..].
      intros [|] ; cbn.
      2: shelve.
      
      intros [Hpost2]%implem_conv_graph%algo_conv_sound%dup ; tea.
      eapply neuNatElimCong_prem3, dup in Hpost2 as [Hpost2 []] ; eauto.
      split ; [easy|..].
      intros [|] ; cbn ; [easy|..].

      Unshelve.
      all: intros ? Hneg ? [? (?&?&?&?&[[= <- <- <-]])%neuConvGen] ; subst.
      all: apply Hneg ; eauto.
      eexists ; split ; gen_typing.
    
    - destruct pre as [[wn wn'] [pre [[] ]%neuEmptyElimCong_prem0%dup]%dup] ; eauto.
      inversion wn ; inversion wn' ; subst.
      split ; [easy|..].
      intros [T|] ; cbn.
      2: shelve.

      intros [Hpost]%implem_conv_graph ; tea.
      eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
      eapply dup in pre as [pre [[? (?&[-> ? Hn]&?)%termGen'] _]].
      destruct T ; try easy.
      eapply dup in pre as [pre [ []]%neuEmptyElimCong_prem1%dup] ; eauto.
      cbn.
      split ; [easy|..].
      intros [|] ; cbn ; [easy|..].

      Unshelve.
      all: intros ? Hneg ? [? (?&?&[[=]])%neuConvGen] ; subst.
      all: apply Hneg ; eauto.
      eexists ; split ; gen_typing.
    
    - destruct pre as [[wn wn'] [pre [[] ]%neuFstCongAlg_prem0%dup]%dup] ; eauto.
      inversion wn ; inversion wn' ; subst.
      split ; [easy|..].
      intros [T|] ; cbn.
      
      + intros [Hpost]%implem_conv_graph ; tea.
        eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
        eapply dup in pre as [pre [[? (?&(?&?&->&Hp)&?)%termGen'] _]].
        now destruct T ; cbn.

      + intros ? Hneg ? [? (?&?&?&[[= <-]])%neuConvGen].
        eapply Hneg.
        eexists ; split ; gen_typing.
    
    - destruct pre as [[wn wn'] [pre [[] ]%neuSndCongAlg_prem0%dup]%dup] ; eauto.
      inversion wn ; inversion wn' ; subst.
      split ; [easy|..].
      intros [T|] ; cbn.
      
      + intros [Hpost]%implem_conv_graph ; tea.
        eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
        eapply dup in pre as [pre [[? (?&(?&?&->&Hp)&?)%termGen'] _]].
        now destruct T ; cbn.

      + intros ? Hneg ? [? (?&?&?&[[= <-]])%neuConvGen].
        eapply Hneg.
        eexists ; split ; gen_typing.
    
    - destruct pre as [[wn wn'] [pre [[] ]%neuIdElimCong_prem0%dup]%dup] ; eauto.
      inversion wn ; inversion wn' ; subst.
      split ; [easy|..].
      intros [T|] ; cbn.
      2: shelve.

      intros [Hpost]%implem_conv_graph ; tea.
      eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
      eapply dup in pre as [pre [[? (?&[-> ????? He]&?)%termGen'] _]].
      destruct T ; try easy.
      eapply dup in pre as [pre [ []]%neuIdElimCong_prem1%dup] ; eauto.
      cbn.
      split ; [erewrite <- !wk1_ren_on ; easy|..].
      intros [|] ; cbn.
      2: shelve.

      intros []%implem_conv_graph%algo_conv_sound%dup.
      2-3: now erewrite <- !wk1_ren_on.
      eapply neuIdElimCong_prem2 in pre ; eauto.
      2: now rewrite !wk1_ren_on.
      split ; [easy|..].
      intros [|] ; cbn ; [easy|..].

      Unshelve.
      all: intros ? Hneg ?[? (?&?&?&?&?&?&[[= <- <- <-]])%neuConvGen] ; subst.
      all: apply Hneg ; eauto.
      + eexists ; split ; gen_typing.
      + now erewrite <- !wk1_ren_on.

    - intros ? [? ?%neuConvGen].
      destruct t ; cbn in * ; try solve [easy].
      all: prod_hyp_splitter ; subst.
      all: simp build_ne_view2 in e ; cbn in *.
      all: congruence.
    
    - split ; [easy|..].
      intros [|] ? Hty ; cbn ; [easy|..].
      intros ? [? []].
      now eapply Hty.

  Qed.

  Corollary implem_tconv_sound_neg Γ T V e :
    graph tconv (Γ,T,V) (exception e) ->
    [Γ |-[de] T] -> [Γ |-[de] V] ->
    ~ [Γ |-[de] T ≅ V].
  Proof.
    intros Hgraph **.
    eapply (funrect_graph _
      (fun '(Γ',T',V') => [Γ' |-[de] T'] × [Γ' |-[de] V'])
      (fun '(Γ',T',V') _ r => match r with | success _ => True | exception _ => ~ [Γ' |-[de] T' ≅ V'] end)) in Hgraph ; try easy.
    
    intros (?&?&?) [].
    funelim (tconv _) ; cbn.
    inversion_clear eqargs.
    intros [] ; cbn ; [easy|].
    eintros ?%funrect_graph.
    2: now apply _implem_conv_neg_sound.
    all: now cbn in *.
    Unshelve.
    all: cbn ; easy.
  Qed.

End ConvSoundNeg.

Section TypingSoundNeg.
  Import AlgorithmicTypingData.
  Context `{ta : tag} `{! ConvType ta}.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

  Context (conv : (context × term × term) ⇀ exn errors unit).

  Hypothesis conv_sound :
    forall Γ A A', [Γ |-[de] A] -> [Γ |-[de] A'] -> [Γ |-[ta] A ≅ A'] -> [Γ |-[de] A ≅ A'].

  Hypothesis implem_sound : forall Γ T V,
    graph conv (Γ,T,V) ok ->
    [Γ |-[ta] T ≅ V].

  Hypothesis implem_neg_sound : forall Γ T V e,
    graph conv (Γ,T,V) (exception e) ->
    [Γ |-[de] T] -> [Γ |-[de] V] ->
    ~ [Γ |-[de] T ≅ V].

  #[universes(polymorphic)]Definition typing_sound_neg_pre
    (x : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term) : Type :=
  match x with
  | (wf_ty_state;Γ;_;T) => [|-[de] Γ]
  | (inf_state;Γ;_;t) => [|-[de] Γ]
  | (inf_red_state;Γ;_;t) => [|-[de] Γ]
  | (check_state;Γ;T;t) => [Γ |-[de] T]
  end.

  #[universes(polymorphic)]Definition typing_sound_neg_type
    (x : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term)
    (_ : typing_sound_neg_pre x)
    (r : exn errors (tstate_output x.π1)) : Type :=
  match x, r with
  | _, (success _) => True
  | (wf_ty_state;Γ;_;T), (exception _) => ~ [Γ |-[de] T]
  | (inf_state;Γ;_;t), (exception _) => forall T, ~ [Γ |-[de] t : T]
  | (inf_red_state;Γ;_;t), (exception _) => forall T, ~ [Γ |-[de] t : T]
  | (check_state;Γ;T;t), (exception _) => ~ [Γ |-[de] t : T]
  end.

  Lemma term_univ_can Γ t :
    [Γ |-[de] t : U] ->
    ~ isType t ->
    ~ isCanonical t.
  Proof.
    intros Hty His Hcan.
    destruct Hcan ; try solve [apply His ; constructor].
    all: eapply termGen' in Hty as (?&?&Hconv) ; cbn in * ; prod_hyp_splitter ; subst.
    all: unshelve eapply ty_conv_inj in Hconv ; try solve [constructor] ; now cbn in *.
  Qed.

  Lemma build_ty_view1_anomaly t :
    build_ty_view1 t = ty_view1_anomaly ->
    ~ isType t × isCanonical t.
  Proof.
    intros.
    destruct t ; cbn in * ; try solve [congruence].
    all: split ; [..|now constructor] ; intros H' ; inversion H' ;
      eapply can_whne_exclusive ; [..|eassumption] ; constructor.
  Qed.

  Lemma _implem_typing_sound_neg :
    funrect (typing conv) typing_sound_neg_pre typing_sound_neg_type.
  Proof.
    intros x Hpre.
    funelim (typing _ _) ; cbn in *.

    4: simp typing_wf_ty ; destruct (build_ty_view1 _) as [? []| |] eqn:He ; cbn.
    3: simp typing_inf_red ; cbn.
    2: simp typing_check ; cbn.
    1: funelim (typing_inf _ _) ; cbn ; inversion eqargs ; subst ; clear eqargs.
    all: try trivial.

    - intros ?? (?&[]&?)%termGen'.
    - split.
      1: boundary.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.
      
      intros Hty%implem_typing_sound _ ; cbn in * ; tea.
      destruct x ; cbn.
      2: shelve.
      all: eintros ?? (?&[-> ?%infer_U]&?)%termGen' ; tea ; congruence.
      Unshelve.
      destruct s.
      split.
      1: econstructor ; [..|eapply algo_typing_sound_generic in Hty] ; gen_typing.

      intros [|].
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.

      intros Hty'%implem_typing_sound _ ; cbn in * ; tea.
      destruct x ; cbn ; try easy.
      all: eintros ?? (?&[-> ? ?%infer_U]&?)%termGen' ; tea ; congruence.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&(?&[])&?)%termGen' ; eauto.

      intros HA%implem_typing_sound _ ; cbn in * ; tea.
      split.
      1: econstructor ; now eapply algo_typing_sound_generic in HA.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&(?&[])&?)%termGen' ; now eapply IH.
      easy.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&(?&?&[])&?)%termGen' ; now eapply IH.

      intros Hf%implem_typing_sound _ ; cbn in * ; tea.
      destruct x ; cbn.
      3: shelve.
      all: eintros ?? (?&(?&?&[? (?&?&?)%infer_prod])&?)%termGen' ; tea ; congruence.
      Unshelve.
      split.
      1: eapply prod_ty_inv ; eapply algo_typing_sound_generic in Hf ; boundary.

      intros [|] ; cbn ; eauto.
      intros _ IH ?? (?&(?&?&[])&?)%termGen'.
      eapply algo_infer_unique in Hf ; tea.
      eapply prod_ty_inj in Hf as [].
      eapply IH ; gen_typing.

    - split.
      1: eassumption.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.
      
      intros ?%implem_typing_sound _ ; cbn in * ; tea.
      destruct x ; cbn ; try easy.
      all: eintros ?? (?&[? ?%infer_nat]&?)%termGen' ; tea ; congruence.

    - split ; tea.
      intros [|] ; cbn.

      2: intros _ IH ?? (?&[]&?)%termGen' ; eapply IH ; eauto.

      intros ?%implem_typing_sound _ ; tea ; cbn in *.
      destruct x ; cbn.
      6: shelve.
      all: eintros ?? (?&[???? ?%infer_nat]&?)%termGen' ; tea ; congruence.
      Unshelve.

      assert [|-[de] Γ0,,tNat] by gen_typing.
      split ; tea.
      intros [|].
      2: intros _ IH ?? (?&[]&?)%termGen' ; eapply IH ; eauto.

      intros HP%implem_typing_sound _ ; tea ; cbn in *.
      eapply algo_typing_sound_generic in HP ; tea.
      split.
      1: now eapply typing_subst1 ; [econstructor|..].

      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; eapply IH ; eauto.
      intros _ _ ; tea ; cbn in *.
      split.
      1: now eapply elimSuccHypTy_ty.
      
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; eapply IH ; eauto.
      easy.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; eapply IH ; eauto.

      intros ?%implem_typing_sound _ ; cbn in * ; tea.
      destruct x ; cbn.
      10: shelve.
      all: eintros ?? (?&[?? ?%infer_empty]&?)%termGen' ; tea ; congruence.
      Unshelve.

      assert [|-[de] Γ0,,tEmpty] by gen_typing.
      split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; eapply IH ; eauto.
      easy.
    
    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.
      
      intros Hty%implem_typing_sound _ ; cbn in * ; tea.
      destruct x ; cbn.
      2: shelve.
      all: eintros ?? (?&[-> ?%infer_U]&?)%termGen' ; tea ; congruence.
      Unshelve.
      destruct s.
      split.
      1: econstructor ; [..|eapply algo_typing_sound_generic in Hty] ; gen_typing.

      intros [|].
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.

      intros Hty'%implem_typing_sound _ ; cbn in * ; tea.
      destruct x ; cbn ; try easy.
      all: eintros ?? (?&[-> ? ?%infer_U]&?)%termGen' ; tea ; congruence.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.

      intros HA%implem_typing_sound _ ; tea ; cbn in *.
      eapply algo_typing_sound_generic in HA ; tea.
      split ; [gen_typing|..].
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.

      intros HB%implem_typing_sound _ ; tea ; cbn in *.
      eapply algo_typing_sound_generic in HB ; tea ; [..|gen_typing].
      split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.

      intros Ha%implem_typing_sound _ ; tea ; cbn in *.
      eapply algo_typing_sound_generic in Ha ; tea.
      split.
      1: now eapply typing_subst1.
      intros [|] ; cbn ; try easy.
      intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&(?&?&[])&?)%termGen' ; now eapply IH.
      intros ?%implem_typing_sound _ ; tea ; cbn in *.
      destruct x ; cbn ; try easy.
      all: eintros ?? (?&(?&?&[? (?&?&?)%infer_sig])&?)%termGen' ; tea ; congruence.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&(?&?&[])&?)%termGen' ; now eapply IH.
      intros ?%implem_typing_sound _ ; tea ; cbn in *.
      destruct x ; cbn ; try easy.
      all: eintros ?? (?&(?&?&[? (?&?&?)%infer_sig])&?)%termGen' ; tea ; congruence.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.
      
      intros HA%implem_typing_sound _ ; tea ; cbn in *.
      destruct x0 ; cbn.
      2: shelve.
      all: eintros ?? (?&[? ?%infer_U]&?)%termGen' ; tea ; congruence.
      Unshelve.
      eapply algo_typing_sound_generic in HA ; tea.
      destruct s.

      split ; [now constructor|..].
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.

      intros _ _.
      split ; [now constructor|..].
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eapply IH.
      easy.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ ??? (?&[]&?)%termGen' ; eauto.
      intros HA%implem_typing_sound _; tea ; cbn in *.
      eapply algo_typing_sound_generic in HA ; tea.
      split ; tea.
      intros [|] _ ; cbn ; try easy.
      intros ??? (?&[]&?)%termGen' ; eauto.

    - split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eauto.

      intros HA%implem_typing_sound _ ; cbn in * ; tea.
      eapply algo_typing_sound_generic in HA ; tea.
      split ; tea.
      intros [|].
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eauto.

      intros Hx%implem_typing_sound _ ; cbn in * ; tea.
      eapply algo_typing_sound_generic in Hx ; tea.
      assert [ |-[ de ] (Γ0,, A),, tId A⟨↑⟩ x⟨↑⟩ (tRel 0)] by
        (erewrite <- !wk1_ren_on ; now eapply idElimMotiveCtx).
      split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; eapply IH ; now repeat erewrite <- !wk1_ren_on.

      intros HP%implem_typing_sound _ ; cbn in * ; tea.
      eapply algo_typing_sound_generic in HP ; tea.

      split.
      1: eapply typing_subst2 ; tea ; eapply typing_meta_conv ; [now econstructor|..] ; cbn ; now bsimpl.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eauto.

      intros _ _ ; cbn in * ; tea.
      split ; tea.
      intros [|] ; cbn.
      2: intros _ IH ?? (?&[]&?)%termGen' ; now eauto.

      intros Hy%implem_typing_sound _ ; cbn in * ; tea.
      eapply algo_typing_sound_generic in Hy ; tea.
      split.
      1: gen_typing.
      intros [|] ; cbn ; try easy.
      intros _ IH ?? (?&[]&?)%termGen' ; now eauto.

    - intros ?? (?&(?&[?? i])&?)%termGen' ; subst.
      eapply ctx_access_complete in i.
      congruence.

    - split ; [boundary|..].
      intros [] ; cbn ; try easy.
      intros Hinf%implem_typing_sound ? [|] ; cbn in * ; try easy.
      intros Hconv%implem_neg_sound Hty' ? ; tea.
      2: eapply algo_typing_sound_generic in Hinf ; tea ; boundary.
      eapply Hconv ; tea.
      eapply algo_infer_unique in Hinf ; tea.
      boundary.

    - split ; [boundary|..].
      intros [] ; cbn ; easy.

    - split ; tea.
      intros [|] ; cbn.
      2: intros ??? []%prod_ty_inv ; eauto.
      intros HA%implem_typing_sound _ ; tea ; cbn in *.
      eapply algo_typing_sound_generic in HA ; tea.
      split.
      1: gen_typing.
      intros [|] ; cbn ; try easy.
      intros ??? []%prod_ty_inv ; eauto.
  
    - split ; tea.
      intros [|] ; cbn.
      2: intros ??? []%sig_ty_inv ; eauto.
      intros HA%implem_typing_sound _ ; tea ; cbn in *.
      eapply algo_typing_sound_generic in HA ; tea.
      split.
      1: gen_typing.
      intros [|] ; cbn ; try easy.
      intros ??? []%sig_ty_inv ; eauto.
    
    - split ; tea.
      intros [|] ; cbn.
      2: intros ??? []%id_ty_inv ; eauto.
      intros HA%implem_typing_sound _ ; tea ; cbn in *.
      eapply algo_typing_sound_generic in HA ; tea.
      split ; tea.
      intros [|] ; cbn.
      2: intros ??? []%id_ty_inv ; eauto.
      intros _ _.
      split ; tea.
      intros [|] ; cbn.
      2: intros ??? []%id_ty_inv ; eauto.
      easy.

    - split ; tea.
      intros [|] ; cbn.
      + intros ?%implem_typing_sound _ ; tea ; cbn in *.
        destruct x ; cbn ; try easy.
        all: eintros ? ?%infer_U_ty ; tea ; congruence.
      + destruct n as [|? []] ; cbn.
        all: intros _ IH ? Hty.
        all: inversion Hty ; subst ; refold.
        all: now eapply IH.

    - intros ? Hty.
      inversion Hty ; subst ; refold.
      1-6: now inversion He.
      eapply build_ty_view1_anomaly in He as [].
      now eapply term_univ_can ; tea.

  Qed.

  Lemma implem_typing_sound_neg x r:
    graph (typing conv) x r ->
    forall (p : typing_sound_neg_pre x),
    typing_sound_neg_type x p r.
  Proof.
    intros.
    eapply funrect_graph.
    1: now apply _implem_typing_sound_neg.
    all: easy.
  Qed.

  Lemma _check_ctx_sound_neg :
    funrect (check_ctx conv) (fun _ => True) (fun Γ _ r => if r then True else ~[|-[de] Γ]).
  Proof.
    intros ? _.
    funelim (check_ctx _ _) ; cbn.
    - now constructor.
    - split ; [easy|].
      intros [[]|] ; cbn ; try easy.
      + intros ?%check_ctx_sound%algo_context_sound ? ; eauto.
        eintros [] Hty%implem_typing_sound_neg ;
          cbn in * ; try easy.
        intros ? Hctx ; inversion Hctx ; subst ; refold.
        easy.
      + intros _ ?? Hctx.
        inversion Hctx ; subst ; refold.
        easy.
    Unshelve.
    all: easy.
  Qed.
     
  Lemma check_ctx_sound_neg Γ e :
    graph (check_ctx conv) Γ (exception e) ->
    ~ [|-[de] Γ].
  Proof.
    eintros ?%funrect_graph.
    2: eapply _check_ctx_sound_neg ; cbn.
    all: easy.
    Unshelve.
    easy.
  Qed.

End TypingSoundNeg.