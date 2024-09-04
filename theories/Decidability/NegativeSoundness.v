(** * LogRel.Decidability.NegativeSoundness: implementation failure implies negation of typing. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel.Decidability Require Import Functions Soundness Completeness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Import DeclarativeTypingProperties.

Definition nat_hd_view (Γ : context) {t t' : term} (nft : isNat t) (nft' : isNat t') : Type :=
  match nft, nft' with
    | ZeroNat, ZeroNat => True
    | @SuccNat u, @SuccNat u' => [Γ |-[de] u ≅ u' : tNat]
    | NeNat _, NeNat _ => True
    | _, _ => False
  end.

Lemma isNat_zero (n : isNat tZero) : n = ZeroNat.
Proof.
  refine (
  match n as n' in isNat k return
    (match k as k' return (isNat k' -> Type) with | tZero => fun n'' => n'' = ZeroNat | _ => fun _ => True end n')
  with | ZeroNat => _ | _ => _ end).
  1-2: easy.
  dependent inversion w ; cbn ; easy.
Qed.

Lemma isNat_succ t (n : isNat (tSucc t)) : n = SuccNat.
Proof.
  refine (
  match n as n' in isNat k return
    (match k as k' return (isNat k' -> Type) with | tSucc _ => fun n'' => n'' = SuccNat | _ => fun _ => True end n')
  with | SuccNat => _ | _ => _ end).
  1-2: easy.
  dependent inversion w ; cbn ; easy.
Qed.

Lemma isNat_ne t (n : isNat t) : whne t -> ∑ w, n = NeNat w.
Proof.
  intros w.
  inversion w ; subst ; clear w.
  all: dependent inversion n ; subst.
  all: eexists ; reflexivity.
Qed.

Lemma nat_conv_inj : forall (Γ : context) (t t' : term) (nft : isNat t) (nft' : isNat t'),
  [Γ |-[de] t ≅ t' : tNat] ->
  nat_hd_view Γ nft nft'.
Proof.
  intros * Hconv.
  eapply Fundamental in Hconv as [HΓ Hnat _ _ Hconv].
  eapply Escape.reducibleTmEq in Hconv.
  unshelve eapply Irrelevance.LRTmEqIrrelevant' in Hconv ; try reflexivity.
  2: now eapply Nat.natRed, Properties.soundCtx.
  1: exact one.
  clear Hnat.
  cbn in *.
  set (nRed := {| NatRedTy.red := redtywf_refl (wft_term (ty_nat (Properties.soundCtx HΓ))) |}) in *.
  clearbody nRed.

  revert nft nft'.
  pattern t, t', Hconv.
  unshelve eapply NatRedTmEq.NatRedTmEq_mut_rect ; clear t t' Hconv.
  
  - exact (fun n n' _ => forall (nft : isNat n) (nft' : isNat n'), nat_hd_view Γ nft nft').
  
  - cbn.
    intros t u t' u' [_ redt%redtm_sound] [_ redu%redtm_sound] ? _ IH Ht Hu.
    eapply red_whnf in redt as ->, redu as ->.
    2-3: gen_typing.
    eauto.

  - cbn.
    intros nft nft'.
    rewrite (isNat_zero nft), (isNat_zero nft') ; cbn.
    easy.

  - cbn.
    intros ?? [] _ nft nft'.
    rewrite (isNat_succ _ nft), (isNat_succ _ nft') ; cbn.
    eapply convtm_exp ; gen_typing.

  - cbn.
    intros ?? [[]] nft nft' ; refold.
    epose proof (isNat_ne _ nft) as [? ->] ; tea.
    epose proof (isNat_ne _ nft') as [? ->] ; tea.
    cbn.
    easy.

Qed.

Definition univ_hd_view (Γ : context) {T T' : term} (nfT : isType T) (nfT' : isType T') : Type :=
  match nfT, nfT' with
    | @UnivType s, @UnivType s' => False
    | @ProdType A B, @ProdType A' B' => [Γ |-[de] A' ≅ A : U] × [Γ,, A' |-[de] B ≅ B' : U]
    | NatType, NatType => True
    | EmptyType, EmptyType => True
    | NeType _, NeType _ => True
    | @SigType A B, @SigType A' B' => [Γ |-[de] A ≅ A' : U] × [Γ,, A |-[de] B ≅ B' : U]
    | @IdType A x y, @IdType A' x' y' => [× [Γ |-[de] A' ≅ A : U], [Γ |-[de] x ≅ x' : A] & [Γ |-[de] y ≅ y' : A]]
    | _, _ => False
  end.

Theorem univ_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
  [Γ |-[de] T ≅ T' : U] ->
  univ_hd_view Γ nfT nfT'.
Proof.
  intros * Hconv.
  eapply Fundamental in Hconv as [HΓ HU HT HT' Hconv].
  eapply Escape.reducibleTmEq in Hconv.
  eapply Escape.reducibleTm in HT, HT'.
  set (HTred := Escape.reducibleTy _ HU) in *.
  clearbody HTred.
  clear HU.
  eapply Universe.univTmTy in HT, HT' ; cbn.
  unshelve eapply Universe.univEqTmEqTy in Hconv ; [idtac|eassumption|..].
  destruct (Induction.invLRU HTred) as [? lt ? ?] ; cbn in *.
  inversion lt ; subst ; clear - HT HT' Hconv.

  revert HT nfT T' nfT' HT' Hconv.
  generalize (eq_refl : zero = zero).
  generalize zero at 1 3; intros l eql HT; revert eql.

  pattern l, Γ, T, HT; apply Induction.LR_rect_TyUr; clear l Γ T HT.
  all: intros ? Γ T.
  
  - intros [? lt] -> **.
    now inversion lt.

  - intros [nT ? ne] -> nfT T' nfT' HT' [nT' ? ne']; cbn in *.
    assert (T = nT) as <- by
      (apply red_whnf ; gen_typing).
    assert (T' = nT') as <- by
      (apply red_whnf ; gen_typing).
    destruct nfT.
    1-6: apply convneu_whne in ne; inversion ne.
    destruct nfT'.
    1-6: symmetry in ne'; apply convneu_whne in ne'; inversion ne'.
    cbn. easy.

  - intros [dom cod red] _ _ -> nfT T' nfT' HT'[dom' cod' red']; cbn in *.
    assert (T = tProd dom cod) as HeqT by (apply red_whnf ; gen_typing). 
    assert (T' = tProd dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
    destruct nfT; cycle -1.
    1: subst ; exfalso ; gen_typing.
    all: try congruence.
    destruct nfT'; cycle -1.
    1: subst ; exfalso ; gen_typing.
    all: try congruence.
    inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
    destruct (Poly.polyRedEqId (NormalRed.normRedΠ0 (Induction.invLRΠ HT')) (Irrelevance.PolyRedEqSym _ polyRed0)) ; cbn in *.
    admit. (* wrong escape *)
  - intros [] -> nfT T' nfT' HT' [].
    assert (T' = tNat) as HeqT' by (eapply redtywf_whnf ; gen_typing).
    assert (T = tNat) as HeqT by (eapply redtywf_whnf ; gen_typing).
    destruct nfT; inversion HeqT.
    + destruct nfT'; inversion HeqT'.
      * constructor.
      * exfalso; subst; inversion w.
    + exfalso; subst; inversion w.
  - intros [] -> nfT T' nfT' HT' [].
    assert (T' = tEmpty) as HeqT' by (eapply redtywf_whnf ; gen_typing).
    assert (T = tEmpty) as HeqT by (eapply redtywf_whnf ; gen_typing).
    destruct nfT; inversion HeqT.
    + destruct nfT'; inversion HeqT'.
      * econstructor.
      * exfalso; subst; inversion w.
    + exfalso; subst; inversion w.
  - intros [dom cod red] _ _ -> nfT T' nfT' HT' [dom' cod' red'] ; cbn in *.
    assert (T = tSig dom cod) as HeqT by (apply red_whnf ; gen_typing).
    assert (T' = tSig dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
    destruct nfT; cycle -1.
    1: subst; inv_whne.
    all: try congruence.
    destruct nfT'; cycle -1.
    1: subst; inv_whne.
    all: try congruence.
    inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
    eapply Poly.polyRedEqId in polyRed0 as [].
    admit. (* wrong escape *)
  - intros [??? ty] _ _ -> nfT T' nfT' HT' [??? ty']; cbn in *.
    assert (T = ty) as HeqT by (apply red_whnf; gen_typing).
    assert (T' = ty') as HeqT' by (apply red_whnf; gen_typing).
    destruct nfT; cycle -1; [subst; inv_whne|..]; unfold ty in *; try congruence.
    destruct nfT'; cycle -1; [subst; inv_whne|..]; unfold ty' in *; try congruence.
    cbn; inversion HeqT; inversion HeqT'; subst.
    split.
    2-3: now Escape.escape.
Admitted.

Import DeclarativeTypingProperties AlgorithmicTypingProperties.

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
  (∑ (nft : isNat t) (nfu : isNat u), A = tNat × nat_hd_view Γ nft nfu = False) + ∑ A' x y, A = tId A' x y.
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
    1-8: econstructor ; eapply whne_can ; tea ; solve [now apply zip_can | intros c ; inversion c].
    all: now cbn.

  - destruct (build_nf_view1 t), (build_nf_view1 u) ; cbn.
    all: solve [intros [=]].

  - right.
    do 3 eexists ; reflexivity.
    
  - unshelve erewrite whne_ty_view1 ; tea ; cbn.
    destruct (build_nf_view1 t) ; cbn ; try solve [intros [=]].
    destruct (build_nf_view1 u) ; cbn ; solve [intros [=]].

Qed.

Lemma prod_tm_inj Γ A B A' B' :
  [Γ |-[de] tProd A B ≅ tProd A' B' : U] ->
  [Γ |-[de] A' ≅ A : U] × [Γ,,A' |-[de] B ≅ B' : U].
Proof.
  unshelve eintros ?%univ_conv_inj.
  1-2: now econstructor.
  now cbn in *.
Qed.

Lemma sig_tm_inj Γ A B A' B' :
  [Γ |-[de] tSig A B ≅ tSig A' B' : U] ->
  [Γ |-[de] A ≅ A' : U] × [Γ,,A |-[de] B ≅ B' : U].
Proof.
  unshelve eintros ?%univ_conv_inj.
  1-2: now econstructor.
  now cbn in *.
Qed.

#[universes(polymorphic)]Definition conv_sound_type
    (x : conv_full_dom)
    (r : conv_full_cod x) : Type :=
  match x, r with
  | (ty_state;Γ;_;T;V), (success _) =>  [Γ |-[al] T ≅ V]
  | (ty_red_state;Γ;_;T;V), (success _) => [Γ |-[al] T ≅h V]
  | (tm_state;Γ;A;t;u), (success _) => [Γ |-[al] t ≅ u : A]
  | (tm_red_state;Γ;A;t;u), (success _) =>
      whnf A -> whnf t -> whnf u -> [Γ |-[al] t ≅h u : A]
  | (ne_state;Γ;_;m;n), (success T) => [Γ |-[al] m ~ n ▹ T]
  | (ne_red_state;Γ;_;m;n), (success T) => [Γ |-[al] m ~h n ▹ T] × whnf T
  
  | (ty_state;Γ;_;T;V), (exception _) => ~ [Γ |-[de] T ≅ V]
  | (ty_red_state;Γ;_;T;V), (exception _) => ~ [Γ |-[de] T ≅ V]
  | (tm_state;Γ;A;t;u), (exception _) => ~ [Γ |-[de] t ≅ u : A]
  | (tm_red_state;Γ;A;t;u), (exception _) => ~ [Γ |-[de] t ≅ u : A]
  | (ne_state;Γ;_;m;n), (exception _) => ~ ∑ T, [Γ |-[de] m ≅ n : T]
  | (ne_red_state;Γ;_;m;n), (exception _) => ~ ∑ T, ([Γ |-[de] m ≅ n : T] × whnf T)
  end.

#[universes(polymorphic)]Definition conv_sound_pre
  (x : conv_full_dom) : Type :=
match x with
| (ty_state;Γ;_;T;V) => [Γ |-[de] T] × [Γ |-[de] V]
| (ty_red_state;Γ;_;T;V) => [× whnf T, whnf V & [Γ |-[de] T] × [Γ |-[de] V]]
| (tm_state;Γ;A;t;u) => [Γ |-[de] t : A] × [Γ |-[de] u : A]
| (tm_red_state;Γ;A;t;u) => [× whnf A, whnf t, whnf u & [Γ |-[de] t : A] × [Γ |-[de] u : A]]
| (ne_state;Γ;_;m;n) => [× (* whne m, whne n,*) well_typed (ta := de) Γ m & well_typed (ta := de) Γ n]
| (ne_red_state;Γ;_;m;n) => [× (* whne m, whne n, *) well_typed (ta := de) Γ m & well_typed (ta := de) Γ n]
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
  
  - intros T' []%red_sound V' []%red_sound.
    eapply typeConvRed_prem2 in pre as [[] Hpost2]%dup ; tea.
    split ; [split|..] ; tea.
    intros [|] Hnty ; cbn.
    1: now econstructor.
    intros Hty.
    eapply Hnty.
    etransitivity.
    2: etransitivity ; tea.
    1: symmetry. 
    all: eapply RedConvTyC, subject_reduction_type ; eauto.
    all: boundary.

  - destruct s1, s2 ; now constructor. 

  - destruct pre as [_ _ [pre [[]]%typePiCongAlg_prem0%dup]%dup].
    split ; [easy|..].
    intros [|] Hty ; cbn.
    2: now intros []%prod_ty_inj.
    eapply dup in Hty as [Hty ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre ?%typePiCongAlg_prem1] ; tea.
    split ; [easy|..].
    intros [|] Hty'.
    2:{
      intros []%prod_ty_inj.
      eapply Hty', stability1 ; eassumption.
    }
    now econstructor.

  - now econstructor.
  
  - now econstructor.
  
  - destruct pre as [_ _ [pre [[]]%typeSigCongAlg_prem0%dup]%dup].
    split ; [easy|..].
    intros [|] Hty ; cbn.
    2: now intros []%sig_ty_inj.
    eapply dup in Hty as [Hty ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre ?%typeSigCongAlg_prem1] ; tea.
    split ; [easy|..].
    intros [|] Hty'.
    2: now intros []%sig_ty_inj.
    now econstructor.
  
  - destruct pre as [_ _ [pre [[]]%typeIdCongAlg_prem0%dup]%dup].
    split ; [easy|..].
    intros [|] Hty ; cbn.
    2: now intros [? _]%id_ty_inj.
    eapply dup in Hty as [Hty ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre [[]]%typeIdCongAlg_prem1%dup] ; tea.
    split ; [easy|..].
    intros [|] Hty' ; cbn.
    2: now intros []%id_ty_inj.
    eapply dup in Hty' as [Hty' ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre ?%typeIdCongAlg_prem2] ; tea.
    split ; [easy|..].
    intros [|] Hty'' ; cbn.
    2: now intros []%id_ty_inj.
    
    now econstructor.

  - eapply ty_view2_neutral_can in e as [].
    destruct pre as [?%whne_can ?%whne_can pre] ; tea.
    eapply dup in pre as [pre [[]]%typeNeuConvAlg_prem2%dup] ; tea.
    split ; [easy|..].
    intros [|] Hty ; cbn.
    1: now econstructor.
    unshelve eintros Hty'%ty_conv_inj.
    1-2: now econstructor.
    cbn in Hty'.
    eauto.

  - destruct pre as [wt wu [Ht Hu]].
    eapply type_isType in Ht, Hu ; tea.
    unshelve eapply ty_mismatch_hd_view in e ; tea.
    unshelve eintros H_view%ty_conv_inj ; tea.
    rewrite e in H_view.
    eassumption.

  - easy.

  - intros ? []%red_sound ? []%red_sound ? []%red_sound.
    eapply termConvRed_prem3 in pre as [[] Hpost3]%dup ; tea.
    split ; [split|..] ; tea.
    intros [|] Hnty ; cbn.
    1: now econstructor.
    intros Hty.
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
    intros [|] Hty ; cbn.
    2:now intros []%prod_tm_inj.
    eapply dup in Hty as [Hty ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre ?%termPiCongAlg_prem1] ; tea.
    split ; [easy|..].
    intros [|] Hty'.
    + now econstructor.
    + intros []%prod_tm_inj.
      eapply Hty', stability1.
      4: eassumption.
      all: econstructor.
      3: now symmetry.
      all: boundary.

  - intros.
    destruct s.
    now econstructor.
    
  - intros.
    destruct s.
    now econstructor.
    
  - destruct s.
    destruct pre as [??? [pre [[]]%termSigCongAlg_prem0%dup]%dup].
    split ; [easy|..].
    intros [|] Hty ; cbn.
    2:now intros []%sig_tm_inj.
    eapply dup in Hty as [Hty ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre ?%termSigCongAlg_prem1] ; tea.
    split ; [easy|..].
    intros [|] Hty'.
    + now econstructor.
    + now intros []%sig_tm_inj.

  - admit.

  - destruct pre as [??? [pre [[]]%termNeuConvAlg_prem0%dup]%dup] ; tea.
    eapply whnf_view3_ty_neutral_can in e as [?%whne_can ?%whne_can] ; tea.
    split ; [easy|..].
    intros [|] Hty ; cbn.
    + econstructor ; tea.
      gen_typing.
    + intros ?.
      eauto.

  - destruct s.
    destruct pre as [_ wt wu [Ht Hu]].
    eapply wft_term, type_isType in Ht, Hu ; tea.
    unshelve eapply univ_mismatch_hd_view in e ; tea.
    unshelve eintros H_view%univ_conv_inj ; tea.
    rewrite e in H_view.
    eassumption.

  - destruct pre as [??? [pre [[]]%termFunConvAlg_prem2%dup]%dup] ; tea.
    split ; [easy|..].
    intros [|] Hty ; cbn.
    + intros _ _ _.
      now econstructor.
    + intros Hty'.
      eapply Hty.
      eapply convtm_meta_conv.
      3: reflexivity.
      1: econstructor.
      1: erewrite <- !Weakening.wk1_ren_on.
      1: eapply convtm_meta_conv.
      1: eapply convtm_wk ; tea.
      * boundary.
      * cbn ; reflexivity.
      * reflexivity.
      * eapply convtm_meta_conv.
        1: do 2 econstructor.
        1: boundary.
        constructor.
        all: now Weakening.bsimpl.
      * Weakening.bsimpl ; refold.
        rewrite scons_eta'.
        now Weakening.bsimpl.
    
  - now econstructor.
  
  - destruct pre as [??? [pre [[]]%termSuccCongAlg_prem0%dup]%dup] ; tea.
    split ; [easy|..].
    intros [|] Hty ; cbn.
    + now econstructor.
    + unshelve eintros ?%nat_conv_inj.
      1-2: now constructor.
      cbn in *.
      eauto.
      
  - destruct pre as [??? [pre [[]]%termPairConvAlg_prem2%dup]%dup] ; tea.
    split ; [easy|..].
    intros [|] ; cbn.
    + eintros [ Hpost%algo_conv_sound]%dup ; tea.
      eapply termPairConvAlg_prem3 in Hpost ; tea.
      split ; [easy|..].
      intros [|].
      1: now econstructor.
      intros Hnty Hty.
      eapply Hnty.
      now econstructor.
    + intros Hnty Hty.
      eapply Hnty.
      now econstructor.
  
  - now econstructor.
  
  - destruct pre as [??? [pre [[]]%termNeuConvAlg_prem0%dup]%dup] ; tea.
    split ; [easy|..].
    intros [|] ; cbn.
    + econstructor ; tea.
      now eapply whnf_view3_neutrals_can in e as [].
    + intros Hnty Hty.
      eapply Hnty.
      now eexists. 
    
  
  - destruct pre as [w ?? []].
    eapply type_isType in w.
    2: boundary.
    unshelve eapply mismatch_hd_view in e as [(?&?&[->])|] ; tea.
    + unshelve eintros ?%nat_conv_inj ; tea.
      now rewrite e in H.

    + admit.

  - destruct (Nat.eqb_spec n n') ; cbn.
    + destruct pre as [_ [? [? [(?& []) ?]]%termGen']] ; subst.
      erewrite ctx_access_complete ; cbn.
      1: econstructor.
      all: eassumption.
      
    + admit.
    
  - admit.
  
  - admit.
  
  - admit.
  
  - admit.
  
  - admit.
  
  - admit.
  
  - admit.
  
  - split ; [easy|..].
    intros [|] Hty ; cbn.
    + intros ? []%red_sound ; split ; tea.
      now econstructor.
    + intros [? []].
      now eapply Hty.
      
Admitted.