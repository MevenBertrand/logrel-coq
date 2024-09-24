(** * LogRel.Decidability.NegativeSoundness: implementation failure implies negation of typing. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms Weakening.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj DeclarativeNeutralConv AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicConvProperties AlgorithmicTypingProperties.

From LogRel.Decidability Require Import Functions Soundness Completeness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Import DeclarativeTypingProperties.

Definition nat_hd_view (Γ : context) {t t' : term} (nft : isNat t) (nft' : isNat t') : Type :=
  match nft, nft' with
    | ZeroNat, ZeroNat => True
    | @SuccNat u, @SuccNat u' => [Γ |-[de] u ≅ u' : tNat]
    | NeNat _, NeNat _ => [Γ |-[de] t ~ t' : tNat ]
    | _, _ => False
  end.

Lemma isNat_zero (n : isNat tZero) : n = ZeroNat.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.

Lemma isNat_succ t (n : isNat (tSucc t)) : n = SuccNat.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.

Lemma isNat_ne t (n : isNat t) : whne t -> ∑ w, n = NeNat w.
Proof.
  intros w.
  depelim n.
  1-2: now inversion w.
  now eexists.
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
    intros ?? [] nft nft' ; refold.
    epose proof (isNat_ne _ nft) as [? ->].
    1: now eapply conv_neu_ne in conv.
    epose proof (isNat_ne _ nft') as [? ->].
    1: now eapply conv_neu_ne in conv.
    cbn.
    assumption.

Qed.

Definition univ_hd_view (Γ : context) {T T' : term} (nfT : isType T) (nfT' : isType T') : Type :=
  match nfT, nfT' with
    | @UnivType s, @UnivType s' => False
    | @ProdType A B, @ProdType A' B' => [Γ |-[de] A' ≅ A : U] × [Γ,, A' |-[de] B ≅ B' : U]
    | NatType, NatType => True
    | EmptyType, EmptyType => True
    | NeType _, NeType _ => [Γ |- T ~ T' : U]
    | @SigType A B, @SigType A' B' => [Γ |-[de] A ≅ A' : U] × [Γ,, A |-[de] B ≅ B' : U]
    | @IdType A x y, @IdType A' x' y' => [× [Γ |-[de] A ≅ A' : U], [Γ |-[de] x ≅ x' : A] & [Γ |-[de] y ≅ y' : A]]
    | _, _ => False
  end.

Lemma escapeEqzero {Γ A B} (lr : [Γ ||-< zero > A]) :
    [Γ |- A : U] ->
    [Γ |- B : U] ->
    [ Γ ||-< zero > A ≅ B | lr ] ->
    [Γ |- A ≅ B : U].
Proof.
  remember zero as l eqn:e.
  revert e B.
  pattern l, Γ, A, lr ; eapply Induction.LR_rect_TyUr.
  all: clear.
  + intros ??? [? lt] -> **.
    inversion lt.
  + intros ??? [] -> ??? [].
    cbn in *.
    etransitivity.
    1: eapply RedConvTeC, subject_reduction ; gen_typing.
    etransitivity.
    1: gen_typing.
    symmetry.
    eapply RedConvTeC, subject_reduction ; gen_typing.

  + intros ??? [dom cod] * IHdom IHcod -> ??? [dom' cod' ??? [shpRed posRed]] ; cbn in *.
    assert [Γ |- A ⤳* tProd dom cod : U].
    {
      eapply subject_reduction ; gen_typing.
    }
    assert [Γ |- tProd dom cod : U] as [? [? [[-> ??] _]]%termGen']%dup
      by boundary.
    assert [Γ |- B ⤳* tProd dom' cod' : U].
    {
      eapply subject_reduction ; gen_typing.
    }
    assert [Γ |- tProd dom' cod' : U] as [? [? [[-> ??] _]]%termGen']%dup
      by boundary.
    eapply convtm_exp ; tea.
    1-2: repeat econstructor ; boundary.

    assert [Γ |-[de] dom ≅ dom' : U].
    {
      erewrite <- (wk_id_ren_on Γ dom).
      unshelve eapply IHdom ; eauto.
      - boundary.
      - now rewrite wk_id_ren_on.
      - erewrite <- (wk_id_ren_on Γ dom').
        eapply shpRed.
    }

    assert [Γ,, dom |-[ de ] cod ≅ cod' : U].
    {
      unshelve epose proof (IHcod _ _ _ _ (Neutral.var0 _ _ _)) as IHcod'.
      1: eapply wk1.
      3: rewrite wk1_ren_on ; reflexivity.
      1: econstructor ; [boundary|..].
      1-2: now econstructor.
      cbn in *.
      replace cod[_] with cod in IHcod'.
      2:{
        clear.
        bsimpl.
        rewrite scons_eta'.
        now bsimpl.
      }
      eapply IHcod' ; eauto.
      1: eapply stability1 ; tea.
      1-2: constructor ; boundary.
      unshelve epose proof (posRed _ _ _ _ (Neutral.var0 _ _ _)) as posRed'.
      1: eapply wk1.
      3: rewrite wk1_ren_on ; reflexivity.
      1: econstructor ; [boundary|..].
      1-2: now econstructor.
      cbn in *.
      replace cod'[_] with cod' in posRed'.
      2:{
        clear.
        bsimpl.
        rewrite scons_eta'.
        now bsimpl.
      }
      Irrelevance.irrelevance.
    }

    now constructor.

  + intros ??? [] -> ??? [].
    etransitivity.
    1: eapply RedConvTeC, subject_reduction ; gen_typing.
    etransitivity.
    1: gen_typing.
    symmetry.
    eapply RedConvTeC, subject_reduction ; gen_typing.

  + intros ??? [] -> ??? [].
    etransitivity.
    1: eapply RedConvTeC, subject_reduction ; gen_typing.
    etransitivity.
    1: gen_typing.
    symmetry.
    eapply RedConvTeC, subject_reduction ; gen_typing.

  + intros ??? [dom cod] * IHdom IHcod -> ??? [dom' cod' ??? [shpRed posRed]] ; cbn in *.
    assert [Γ |- A ⤳* tSig dom cod : U].
    {
      eapply subject_reduction ; gen_typing.
    }
    assert [Γ |- tSig dom cod : U] as [? [? [[-> ??] _]]%termGen']%dup
      by boundary.
    assert [Γ |- B ⤳* tSig dom' cod' : U].
    {
      eapply subject_reduction ; gen_typing.
    }
    assert [Γ |- tSig dom' cod' : U] as [? [? [[-> ??] _]]%termGen']%dup
      by boundary.
    eapply convtm_exp ; tea.
    1-2: repeat econstructor ; boundary.

    assert [Γ |-[de] dom ≅ dom' : U].
    {
      erewrite <- (wk_id_ren_on Γ dom).
      unshelve eapply IHdom ; eauto.
      - boundary.
      - now rewrite wk_id_ren_on.
      - erewrite <- (wk_id_ren_on Γ dom').
        eapply shpRed. 
    }

    assert [Γ,, dom |-[ de ] cod ≅ cod' : U].
    {
      unshelve epose proof (IHcod _ _ _ _ (Neutral.var0 _ _ _)) as IHcod'.
      1: eapply wk1.
      3: rewrite wk1_ren_on ; reflexivity.
      1: econstructor ; [boundary|..].
      1-2: now econstructor.
      cbn in *.
      replace cod[_] with cod in IHcod'.
      2:{
        clear.
        bsimpl.
        rewrite scons_eta'.
        now bsimpl.
      }
      eapply IHcod' ; eauto.
      1: eapply stability1 ; tea.
      1-2: constructor ; boundary.
      unshelve epose proof (posRed _ _ _ _ (Neutral.var0 _ _ _)) as posRed'.
      1: eapply wk1.
      3: rewrite wk1_ren_on ; reflexivity.
      1: econstructor ; [boundary|..].
      1-2: now econstructor.
      cbn in *.
      replace cod'[_] with cod' in posRed'.
      2:{
        clear.
        bsimpl.
        rewrite scons_eta'.
        now bsimpl.
      }
      Irrelevance.irrelevance.
    }

    now constructor.

  + intros ??? [T x y outTy ?] IH ? -> ??? [T' x' y' outTy' ? eq']; cbn in *.
    subst outTy outTy' ; cbn in *.
    assert [Γ |- A ⤳* tId T x y : U].
    {
      eapply subject_reduction ; gen_typing.
    }
    assert [Γ |- tId T x y : U] as [? [? [[-> ??] _]]%termGen']%dup
      by boundary.
    assert [Γ |- B ⤳* tId T' x' y' : U].
    {
      eapply subject_reduction ; gen_typing.
    }
    assert [Γ |- tId T' x' y' : U] as [? [? [[-> ??] _]]%termGen']%dup
      by boundary.
    cbv in eq' ; refold.
    eapply convtm_exp ; tea.
    1-2: repeat econstructor ; boundary.
    econstructor ; tea.
    * now eapply IH.
    * now Escape.escape.
    * now Escape.escape.

Qed.

Theorem univ_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
  [Γ |-[de] T ≅ T' : U] ->
  univ_hd_view Γ nfT nfT'.
Proof.
  intros * Hconv.
  assert [Γ |- T : U] as HT by boundary.
  assert [Γ |- T' : U] as HT' by boundary.
  revert HT HT'. 
  eapply Fundamental in Hconv as [HΓ HU HT HT' Hconv].
  eapply Escape.reducibleTmEq in Hconv.
  eapply Escape.reducibleTm in HT, HT'.
  set (HTred := Escape.reducibleTy _ HU) in *.
  clearbody HTred.
  clear HU.
  eapply Universe.univTmTy in HT, HT' ; cbn.
  unshelve eapply Universe.univEqTmEqTy in Hconv ; [idtac|eassumption|..].
  destruct (Induction.invLRU HTred) as [? lt ? ?] ; cbn in *.
  inversion lt ; subst ; clear - HT Hconv.

  revert HT nfT T' nfT' Hconv.
  generalize (eq_refl : zero = zero).
  generalize zero at 1 3; intros l eql HT; revert eql.

  pattern l, Γ, T, HT; apply Induction.LR_rect_TyUr; clear l Γ T HT.
  all: intros ? Γ T.
  
  - intros [? lt] -> **.
    now inversion lt.

  - intros [nT ? ne] -> nfT T' nfT' [nT' ? ne'] HT HT' ; cbn in *.
    assert (T = nT) as <- by
      (apply red_whnf ; gen_typing).
    assert (T' = nT') as <- by
      (apply red_whnf ; gen_typing).
    destruct nfT.
    1-6: apply convneu_whne in ne; inversion ne.
    destruct nfT'.
    1-6: symmetry in ne'; apply convneu_whne in ne'; inversion ne'.
    cbn. easy.

  - intros [dom cod red] _ _ -> nfT T' nfT' [dom' cod' red'] HT HT' ; cbn in *.
    assert (T = tProd dom cod) as HeqT by (apply red_whnf ; gen_typing). 
    assert (T' = tProd dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
    destruct nfT; cycle -1.
    1: subst ; exfalso ; gen_typing.
    all: try congruence.
    destruct nfT'; cycle -1.
    1: subst ; exfalso ; gen_typing.
    all: try congruence.
    inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
    edestruct (Poly.polyRedEqId _ polyRed0) ; cbn in *.
    eapply termGen' in HT as [? [[]]].
    eapply termGen' in HT' as [? [[]]].
    assert [Γ |- dom' ≅ dom : U] by
      (symmetry ; now eapply escapeEqzero).
    split ; tea.
    eapply stability1.
    3: now constructor.
    1-2: boundary.
    eapply escapeEqzero ; tea.
    eapply stability1 ; tea.
    all: boundary. 
      
  - intros [] -> nfT T' nfT' [] ??.
    assert (T' = tNat) as HeqT' by (eapply redtywf_whnf ; gen_typing).
    assert (T = tNat) as HeqT by (eapply redtywf_whnf ; gen_typing).
    destruct nfT; inversion HeqT.
    + destruct nfT'; inversion HeqT'.
      * constructor.
      * exfalso; subst; inversion w.
    + exfalso; subst; inversion w.

  - intros [] -> nfT T' nfT' [] ??.
    assert (T' = tEmpty) as HeqT' by (eapply redtywf_whnf ; gen_typing).
    assert (T = tEmpty) as HeqT by (eapply redtywf_whnf ; gen_typing).
    destruct nfT; inversion HeqT.
    + destruct nfT'; inversion HeqT'.
      * econstructor.
      * exfalso; subst; inversion w.
    + exfalso; subst; inversion w.

  - intros [dom cod red] _ _ -> nfT T' nfT' [dom' cod' red'] ?? ; cbn in *.
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
    eapply termGen' in HT as [? [[]]].
    eapply termGen' in HT' as [? [[]]].
    assert [Γ |- dom ≅ dom' : U] by now eapply escapeEqzero.
    split ; tea.
    eapply escapeEqzero ; tea.
    eapply stability1 ; tea.
    all: boundary.

  - intros [??? ty] _ _ -> nfT T' nfT' [??? ty'] ?? ; cbn in *.
    assert (T = ty) as HeqT by (apply red_whnf; gen_typing).
    assert (T' = ty') as HeqT' by (apply red_whnf; gen_typing).
    destruct nfT; cycle -1; [subst; inv_whne|..]; unfold ty in *; try congruence.
    destruct nfT'; cycle -1; [subst; inv_whne|..]; unfold ty' in *; try congruence.
    cbn; inversion HeqT; inversion HeqT'; subst ; clear HeqT HeqT' ; cbn in *.
    eapply termGen' in HT as [? [[]]].
    eapply termGen' in HT' as [? [[]]].
    split.
    2-3: now Escape.escape.
    now eapply escapeEqzero.
Qed.

Lemma empty_conv_inj (Γ : context) (t t' : term) :
  whne t -> whne t' ->
  [Γ |-[de] t ≅ t' : tEmpty] ->
  [Γ |-[de] t ~ t' : tEmpty].
Proof.
  intros * wt wt' Hconv.
  eapply Fundamental in Hconv as [HΓ Hemp _ _ Hconv].
  eapply Escape.reducibleTmEq in Hconv.
  unshelve eapply Irrelevance.LRTmEqIrrelevant' in Hconv ; try reflexivity.
  2: now eapply Empty.emptyRed, Properties.soundCtx.
  1: exact one.
  clear Hemp.
  cbn in *.
  set (nRed := {| EmptyRedTy.red := redtywf_refl (wft_term (ty_empty (Properties.soundCtx HΓ))) |}) in *.
  clearbody nRed.

  destruct Hconv as [?? ?? redL redR ? Hp].
  inversion Hp as [?? []]; subst.
  erewrite red_whnf.
  2: eapply redtm_sound, redR.
  2: now econstructor.
  erewrite (red_whnf t).
  2: eapply redtm_sound, redL.
  2: now econstructor.

  assumption.

Qed.

Definition id_hd_view (Γ : context) (A x x' : term) {t t' : term} (nft : isId t) (nft' : isId t') : Type :=
  match nft, nft' with
    | @ReflId A a, @ReflId A' a' => [Γ |- A ≅ A'] × [Γ |- a ≅ a' : A]
    | NeId _, NeId _ => [Γ |- t ~ t' : tId A x x']
    | _, _ => False
  end.

Lemma isId_refl A a (n : isId (tRefl A a)) : n = ReflId.
Proof.
  depelim n.
  1: reflexivity.
  inversion w ; cbn ; easy.
Qed.

Lemma isId_ne t (n : isId t) : whne t -> ∑ w, n = NeId w.
Proof.
  intros w.
  dependent inversion n ; subst.
  1: inversion w.
  now eexists.
Qed.

Lemma id_conv_inj : forall (Γ : context) (A x y t t' : term) (nft : isId t) (nft' : isId t'),
  [Γ |-[de] t ≅ t' : tId A x y] ->
  id_hd_view Γ A x y nft nft'.
Proof.
  intros * Hconv.
  eapply Fundamental in Hconv as [HΓ Hid _ _ Hconv].
  eapply Escape.reducibleTmEq in Hconv.
  set (HTred := Escape.reducibleTy _ Hid) in *.
  clearbody HTred.
  clear Hid.
  unshelve eapply Irrelevance.LRTmEqIrrelevant' in Hconv ; try reflexivity.
  1: exact one.
  1: now eapply LRId', Induction.invLRId.
  cbn in *.
  clear - Hconv.
  
  destruct Hconv as [u u' ? ? _ p] ; cbn in *.
  assert (t = u) as <- by (eapply red_whnf ; gen_typing).
  assert (t' = u') as <- by (eapply red_whnf ; gen_typing).
  destruct p as [? | ? ? []] ; cbn in *.

  - Escape.escape.
    rewrite (isId_refl _ _ nft), (isId_refl _ _ nft') ; cbn.
    split.
    + etransitivity ; eauto.
      now symmetry.
    + econstructor ; eauto.
      etransitivity ; eauto.
      now symmetry.

  - edestruct (isId_ne ne) as [? ->] ; [now eapply conv_neu_ne in conv |..].
    edestruct (isId_ne ne') as [? ->] ; [now eapply conv_neu_ne in conv |..].
    cbn.
    unfold IdRedTyPack.outTy in conv ; cbn in *.
    destruct (Id.IdRedTy_inv (Induction.invLRId HTred)) as [eA ex ey].
    rewrite <- eA, <- ex, <- ey in conv.
    assumption.

Qed.

Lemma neu_conv_inj (Γ : context) (A t t' : term) :
  whne A -> whne t -> whne t' ->
  [Γ |-[de] t ≅ t' : A] ->
  [Γ |-[de] t ~ t' : A].
Proof.
  intros * wA wt wt' Hconv.
  eapply Fundamental in Hconv as [HΓ Hne _ _ Hconv].
  eapply Escape.reducibleTmEq in Hconv.
  unshelve eapply Irrelevance.LRTmEqIrrelevant' in Hconv ; try reflexivity.
  1: exact one.
  1:{
    eapply Neutral.neu.
    2: eapply conv_neu_refl, neutral_ty_inv ; tea.
    all: now eapply Escape.escapeTy.
  }
  cbn in *.

  destruct Hconv as [?? redL redR ?] ; cbn in *.
  erewrite red_whnf.
  2: eapply redtm_sound, redR.
  2: now econstructor.
  erewrite (red_whnf t).
  2: eapply redtm_sound, redL.
  2: now econstructor.

  assumption.

Qed.

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
    1-8: econstructor ; eapply whne_can ; tea ; solve [now apply zip_can | intros c ; inversion c].
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
    5-8: econstructor ; eapply whne_can ; tea ; solve [now apply zip_can | intros c ; inversion c].
    all: now cbn.
    
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

Lemma id_tm_inj Γ A x y A' x' y' :
  [Γ |-[de] tId A x y ≅ tId A' x' y' : U] ->
  [× [Γ |-[de] A ≅ A' : U], [Γ |-[de] x ≅ x' : A] & [Γ |-[de] y ≅ y' : A]].
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
  | (ne_state;Γ;_;m;n), (exception _) => ~ ∑ T, [Γ |-[de] m ~ n : T]
  | (ne_red_state;Γ;_;m;n), (exception _) => ~ ∑ T, ([Γ |-[de] m ~ n : T] × whnf T)
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
    unshelve eapply univ_conv_inj in Hty'.
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

  - destruct s.
    destruct pre as [??? [pre [[]]%termIdCongAlg_prem0%dup]%dup].
    split ; [easy|..].
    intros [|] Hty ; cbn.
    2:now intros []%id_tm_inj.
    eapply dup in Hty as [Hty ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre [? []]%termIdCongAlg_prem1%dup] ; tea.
    split ; [easy|..].
    intros [|] Hty' ; cbn in *.
    2: now intros []%id_tm_inj.
    eapply dup in Hty' as [Hty' ?%algo_conv_sound] ; tea.
    eapply dup in pre as [pre ?%termIdCongAlg_prem2] ; tea.
    split ; [easy|..].
    intros [|] Hty'' ; cbn in *.
    2: now intros []%id_tm_inj.
    now econstructor.

  - destruct pre as [??? [pre [[]]%termNeuConvAlg_prem0%dup]%dup] ; tea.
    eapply whnf_view3_ty_neutral_can in e as [?%whne_can ?%whne_can] ; tea.
    split ; [easy|..].
    intros [|] Hty ; cbn.
    + econstructor ; tea.
      gen_typing.
    + destruct s.
      unshelve eintros ?%univ_conv_inj.
      1-2: now econstructor.
      cbn in *.
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
    eapply whnf_view3_neutrals_can in e as [Wa Wn Wn'].
    2: easy.
    intros [|] ; cbn.
    + now econstructor.
    + intros Hnty Hty.
      eapply whne_can in Wn, Wn' ; eauto.
      eapply Hnty.
      exists A.
      destruct Wa.
      * destruct s.
        unshelve eapply univ_conv_inj in Hty.
        1-2: now econstructor.
        now cbn in *.
      * unshelve eapply nat_conv_inj in Hty.
        1-2: now econstructor.
        now cbn in *.
      * unshelve eapply empty_conv_inj in Hty.
        all: now cbn in *.
      * unshelve eapply id_conv_inj in Hty.
        1-2: now econstructor.
        now cbn in *.
      * now eapply neu_conv_inj in Hty.
  
  - destruct pre as [w ?? []].
    eapply type_isType in w.
    2: boundary.
    unshelve eapply mismatch_hd_view in e as [(?&?&[->])|(?&?&?&?&?&[->])] ; tea.
    + unshelve eintros ?%nat_conv_inj ; tea.
      now rewrite e in H.

    + unshelve eintros ?%id_conv_inj ; tea.
      now rewrite e in H.

  - destruct (Nat.eqb_spec n n') ; cbn.
    + destruct pre as [_ [? [? [(?& []) ?]]%termGen']] ; subst.
      erewrite ctx_access_complete ; cbn.
      1: econstructor.
      all: eassumption.
      
    + intros [? (?&[[= ->]])%neuConvGen].
      eauto.
    
  - apply dup in pre as [pre [[] ]%neuAppCongAlg_prem0%dup] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    + intros [[Hpost]%dup] ; tea.
      eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
      eapply dup in pre as [pre [[? (?&[? [? [-> Hf]]]&?)%termGen'] _]].
      eapply Hfu, red_ty_compl_prod_r in Hf as (?&?&[red%redty_sound]).
      eapply red_whnf in red ; eauto ; subst.
      edestruct neuAppCongAlg_prem1 ; eauto.

      cbn.
      split ; [eauto|..].
      intros [|] ; cbn.
      1: now econstructor.

      intros Hneg [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
      apply Hneg.
      eapply TermConv ; refold ; tea.
      eapply prod_ty_inj, Hfu.
      eauto using conv_neu_sound with boundary.

    + intros Hneg [? (?&?&?&?&[[=]])%neuConvGen] ; subst.
      apply Hneg.
      eexists ; split ; eauto.
      now constructor.
 
  - apply dup in pre as [pre [[] ]%neuNatElimCong_prem0%dup] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.

    intros [[Hpost]%dup] ; tea.
    eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
    eapply dup in pre as [pre [[? (?&[-> ??? Hn]&?)%termGen'] _]].
    eapply Hfu, red_ty_compl_nat_r, redty_sound, red_whnf in Hn ; eauto ; subst.
    eapply dup in pre as [pre [ []]%neuNatElimCong_prem1%dup] ; eauto.
    cbn.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.

    intros [? [Hpost1 ?]%algo_conv_sound%dup]%dup ; tea.
    eapply neuNatElimCong_prem2, dup in Hpost1 as [Hpost1 []] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.
    
    intros [? [Hpost2 ?]%algo_conv_sound%dup]%dup ; tea.
    eapply neuNatElimCong_prem3, dup in Hpost2 as [Hpost2 []] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.
    
    intros.
    now econstructor.

    Unshelve.
    all: intros Hneg [? (?&?&?&?&[[= <- <- <-]])%neuConvGen] ; subst.
    all: apply Hneg ; eauto.
    eexists ; split ; gen_typing.
  
  - apply dup in pre as [pre [[] ]%neuEmptyElimCong_prem0%dup] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.

    intros [[Hpost]%dup] ; tea.
    eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
    eapply dup in pre as [pre [[? (?&[-> ? Hn]&?)%termGen'] _]].
    eapply Hfu, red_ty_compl_empty_r, redty_sound, red_whnf in Hn ; eauto ; subst.
    eapply dup in pre as [pre [ []]%neuEmptyElimCong_prem1%dup] ; eauto.
    cbn.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.
    
    intros.
    now econstructor.

    Unshelve.
    all: intros Hneg [? (?&?&[[=]])%neuConvGen] ; subst.
    all: apply Hneg ; eauto.
    eexists ; split ; gen_typing.
  
  - apply dup in pre as [pre [[] ]%neuFstCongAlg_prem0%dup] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    
    + intros [[Hpost]%dup] ; tea.
      eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
      eapply dup in pre as [pre [[? (?&(?&?&->&Hp)&?)%termGen'] _]].
      eapply Hfu, red_ty_compl_sig_r in Hp as (?&?&[red%redty_sound]).
      eapply red_whnf in red ; eauto ; subst.
      cbn.
      now econstructor.

    + intros Hneg [? (?&?&?&[[= <-]])%neuConvGen].
      eapply Hneg.
      eexists ; split ; gen_typing.
  
  - apply dup in pre as [pre [[] ]%neuSndCongAlg_prem0%dup] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    
    + intros [[Hpost]%dup] ; tea.
      eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
      eapply dup in pre as [pre [[? (?&(?&?&->&Hp)&?)%termGen'] _]].
      eapply Hfu, red_ty_compl_sig_r in Hp as (?&?&[red%redty_sound]).
      eapply red_whnf in red ; eauto ; subst.
      cbn.
      now econstructor.

    + intros Hneg [? (?&?&?&[[= <-]])%neuConvGen].
      eapply Hneg.
      eexists ; split ; gen_typing.
  
  - apply dup in pre as [pre [[] ]%neuIdElimCong_prem0%dup] ; eauto.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.

    intros [[Hpost]%dup] ; tea.
    eapply algo_conv_sound in Hpost as [Hconv Hfu ?] ; tea.
    eapply dup in pre as [pre [[? (?&[-> ????? He]&?)%termGen'] _]].
    eapply Hfu, red_ty_compl_id_r in He as (?&?&?&[red%redty_sound]).
    eapply red_whnf in red ; eauto ; subst.
    eapply dup in pre as [pre [ []]%neuIdElimCong_prem1%dup] ; eauto.
    cbn.
    split ; [erewrite <- !wk1_ren_on ; easy|..].
    intros [|] ; cbn.
    2: shelve.

    intros [? ?%algo_conv_sound%dup]%dup.
    2-3: now erewrite <- !wk1_ren_on.
    eapply neuIdElimCong_prem2 in pre ; eauto.
    2: now rewrite !wk1_ren_on.
    split ; [easy|..].
    intros [|] ; cbn.
    2: shelve.
    econstructor ; eauto.
    now rewrite !wk1_ren_on.

    Unshelve.
    all: intros Hneg [? (?&?&?&?&?&?&[[= <- <- <-]])%neuConvGen] ; subst.
    all: apply Hneg ; eauto.
    + eexists ; split ; gen_typing.
    + now erewrite <- !wk1_ren_on. 
    
  
  - intros [? ?%neuConvGen].
    destruct t ; cbn in * ; try solve [easy].
    all: prod_hyp_splitter ; subst.
    all: simp build_ne_view2 in e ; cbn in *.
    all: congruence.
  
  - split ; [easy|..].
    intros [|] Hty ; cbn.
    + intros ? []%red_sound ; split ; tea.
      now econstructor.
    + intros [? []].
      now eapply Hty.

Qed.