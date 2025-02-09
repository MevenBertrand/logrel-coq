(** * LogRel.LogRelConsequences: the properties from PropertiesDefinition are consequences of the logical relation. *)
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping.
From LogRel.TypingProperties Require Import Normalisation PropertiesDefinition DeclarativeProperties SubstConsequences TypeConstructorsInj NeutralConvProperties NormalisationConsequences.

From LogRel Require Import LogicalRelation Fundamental.
From LogRel.LogicalRelation Require Import Escape Irrelevance Transitivity Neutral Induction NormalRed.
From LogRel.LogicalRelation.Introductions Require Import Poly.
From LogRel.Validity Require Import Validity Escape Poly Irrelevance.

(** ** Stability of typing under substitution *)

(** A priori, we could obtain this by a painful inductive argument, but things are quite a bit easier this way. *)

Import DeclarativeTypingData.

Section Subst.

Import WeakDeclarativeTypingProperties WeakDeclarativeTypingData.

  Lemma _typing_subst : WfDeclInductionConcl
    (fun _ => True)
    (fun Γ A => forall Δ σ, [|- Δ] -> [Δ |-s σ : Γ] -> [Δ |- A[σ]])
    (fun Γ A t => forall Δ σ, [|- Δ] -> [Δ |-s σ : Γ] -> [Δ |- t[σ] : A[σ]])
    (fun Γ A B => forall Δ σ σ', [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] -> [Δ |- A[σ] ≅ B[σ']])
    (fun Γ A t u => forall Δ σ σ', [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] -> [Δ |- t[σ] ≅ u[σ'] : A[σ]]).
  Proof.
    unshelve (repeat split ; [shelve|..]).
    - intros Γ ? Ht * HΔ Hσ.
      unshelve eapply Fundamental_subst in Hσ as [].
      1,3: boundary.
      apply Fundamental in Ht as [VΓ [VA _]].
      unshelve eapply escape, VA ; tea.
      unshelve eapply irrelevanceSubst ; eassumption.
    - intros * Ht * HΔ Hσ.
      unshelve eapply Fundamental_subst in Hσ as [].
      1,3: boundary.
      apply Fundamental in Ht as [VΓ [VA] [Vt]].
      unshelve eapply escapeTerm, Vt ; tea.
      unshelve eapply irrelevanceSubst ; eassumption.
    - intros * Ht * HΔ Hσ.
      unshelve eapply Fundamental_subst_conv in Hσ as [].
      1,3: boundary.
      apply Fundamental in Ht as [VΓ VA ? Vconv] ; cbn in *.
      unshelve eapply LogicalRelation.Escape.escapeEq.
      2: unshelve eapply VA ; tea ; irrValid.
      cbn.
      eapply irrelevanceTyEq.
      eassumption.
    - intros * Ht * HΔ Hσ.
      unshelve eapply Fundamental_subst_conv in Hσ as [].
      1,3: boundary.
      apply Fundamental in Ht as [VΓ VA Vtu] ; cbn in *.
      unshelve eapply escapeEqTerm.
      2: now unshelve eapply VA ; tea ; irrValid.
      cbn.
      eapply irrelevanceTmEq.
      eassumption.
  Qed.

End Subst.

#[local, refine] Instance TypingSubstLogRel : TypingSubst (ta := de) := {}.
  Proof.
    all: intros ; now eapply _typing_subst.
  Qed.

(** ** Injectivity of type constructors *)

Section TypeConstructors.

  Import WeakDeclarativeTypingProperties WeakDeclarativeTypingData.

  Lemma _red_ty_complete_l (Γ : context) (T T' : term) :
    isType T ->
    [Γ |- T ≅ T'] ->
    ∑ T'', [Γ |- T' ⤳* T''] × isType T''.
  Proof.
    intros * tyT Hconv.
    eapply Fundamental in Hconv as [HΓ HT HT' Hconv].
    eapply reducibleTyEq in Hconv.
    set (HTred := reducibleTy _ HT) in *.
    clearbody HTred.
    clear HT.
    destruct HTred as [[] lr] ; cbn in *.
    destruct lr.
    all: destruct Hconv; eexists; split; [lazymatch goal with H : [_ |- _ :⤳*: _] |- _ => apply H end|]; constructor.
    eapply convneu_whne; now symmetry.
  Qed.

  Lemma _red_ty_complete_r (Γ : context) (T T' : term) :
    isType T' ->
    [Γ |- T ≅ T'] ->
    ∑ T'', [Γ |- T ⤳* T''] × isType T''.
  Proof.
    intros ? Hconv.
    symmetry in Hconv.
    now eapply _red_ty_complete_l in Hconv.
  Qed.


  Lemma _ty_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
    [Γ |- T ≅ T'] ->
    type_hd_view Γ nfT nfT'.
  Proof.
    intros * Hconv.
    eapply Fundamental in Hconv as [HΓ HT HT' Hconv].
    eapply reducibleTyEq in Hconv.
    set (HTred := reducibleTy _ HT) in *.
    clearbody HTred.
    clear HT.
    eapply reducibleTy in HT'.
    revert nfT T' nfT' HΓ HT' Hconv. 
    revert HTred. 
    generalize (eq_refl : one = one).
    generalize one at 1 3; intros l eql HTred; revert eql.
    pattern l, Γ, T, HTred; apply LR_rect_TyUr; clear l Γ T HTred.
    all: intros ? Γ T.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = U) as HeqT' by (eapply redtywf_whnf ; gen_typing); subst.
      assert (T = U) as HeqU by (eapply redtywf_whnf ; gen_typing). 
      destruct nfT ; inversion HeqU ; subst.
      2: now exfalso ; gen_typing.
      clear HeqU.
      remember U as T eqn:HeqU in nfT' |- * at 2.
      destruct nfT'; inversion HeqU ; subst.
      2: now exfalso ; gen_typing.
      now reflexivity.
    - intros [nT ? ne] -> nfT T' nfT' HΓ HT' [nT' ? ne']; cbn in *.
      assert (T = nT) as <- by
        (apply red_whnf ; gen_typing).
      assert (T' = nT') as <- by
        (apply red_whnf ; gen_typing).
      destruct nfT.
      1-6: apply convneu_whne in ne; inversion ne.
      destruct nfT'.
      1-6: symmetry in ne'; apply convneu_whne in ne'; inversion ne'.
      cbn. gen_typing.
    - intros [dom cod red] _ _ -> nfT T' nfT' HΓ HT'[dom' cod' red']; cbn in *.
      assert (T = tProd dom cod) as HeqT by (apply red_whnf ; gen_typing). 
      assert (T' = tProd dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
      destruct nfT; cycle -1.
      1: subst ; exfalso ; gen_typing.
      all: try congruence.
      destruct nfT'; cycle -1.
      1: subst ; exfalso ; gen_typing.
      all: try congruence.
      inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
      destruct (polyRedEqId (normRedΠ0 (invLRΠ HT')) (PolyRedEqSym _ polyRed0)).
      split; now escape.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = tNat) as HeqT' by (eapply redtywf_whnf ; gen_typing).
      assert (T = tNat) as HeqT by (eapply redtywf_whnf ; gen_typing).
      destruct nfT; inversion HeqT.
      + destruct nfT'; inversion HeqT'.
        * constructor.
        * exfalso; subst; inversion w.
      + exfalso; subst; inversion w.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = tEmpty) as HeqT' by (eapply redtywf_whnf ; gen_typing).
      assert (T = tEmpty) as HeqT by (eapply redtywf_whnf ; gen_typing).
      destruct nfT; inversion HeqT.
      + destruct nfT'; inversion HeqT'.
        * econstructor.
        * exfalso; subst; inversion w.
      + exfalso; subst; inversion w.
    - intros [dom cod red] _ _ -> nfT T' nfT' HΓ HT' [dom' cod' red'] ; cbn in *.
      assert (T = tSig dom cod) as HeqT by (apply red_whnf ; gen_typing).
      assert (T' = tSig dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
      destruct nfT; cycle -1.
      1: subst; inv_whne.
      all: try congruence.
      destruct nfT'; cycle -1.
      1: subst; inv_whne.
      all: try congruence.
      inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
      eapply polyRedEqId in polyRed0 as [].
      split ; now escape.
    - intros [??? ty] _ _ -> nfT T' nfT' HΓ HT' [??? ty']; cbn in *.
      assert (T = ty) as HeqT by (apply red_whnf; gen_typing).
      assert (T' = ty') as HeqT' by (apply red_whnf; gen_typing).
      destruct nfT; cycle -1; [subst; inv_whne|..]; unfold ty in *; try congruence.
      destruct nfT'; cycle -1; [subst; inv_whne|..]; unfold ty' in *; try congruence.
      cbn; inversion HeqT; inversion HeqT'; subst; escape; now split.
  Qed.

End TypeConstructors.

#[local, refine] Instance RedCompleteLogRel : TypeReductionComplete (ta := de) := {}.
Proof.
  all: intros ; eauto using _red_ty_complete_l, _red_ty_complete_r.
  Qed.

#[local, refine] Instance TypeConstructorsInjLogRel : TypeConstructorsInj (ta := de) := {}.
Proof.
  intros.
  now apply _ty_conv_inj.
Qed.

(** ** Injectivity of term constructors *)

Section TermConstructors.

  Import DeclarativeTypingProperties DeclarativeTypingData.

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
      eapply convtm_exp.
      1-2: eapply subject_reduction ; gen_typing.
      all: try solve [boundary|gen_typing].

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
        unshelve epose proof (IHcod _ _ _ _ _ (Neutral.var0 _ _ _)) as IHcod'.
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
        unshelve epose proof (posRed _ _ _ _ _ (Neutral.var0 _ _ _)) as posRed'.
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
      eapply convtm_exp.
      1-2: eapply subject_reduction ; gen_typing.
      all: try solve [boundary|gen_typing].

    + intros ??? [] -> ??? [].
      eapply convtm_exp.
      1-2: eapply subject_reduction ; gen_typing.
      all: try solve [boundary|gen_typing].


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
        unshelve epose proof (IHcod _ _ _ _ _ (Neutral.var0 _ _ _)) as IHcod'.
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
        unshelve epose proof (posRed _ _ _ _ _ (Neutral.var0 _ _ _)) as posRed'.
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

  Theorem _univ_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
    [Γ |-[de] T ≅ T' : U] ->
    univ_hd_view Γ nfT nfT' × (whne T -> [Γ |-[de] T ~ T' : U]).
  Proof.
    intros * Hconv.
    assert [Γ |- T : U] as HT by boundary.
    assert [Γ |- T' : U] as HT' by boundary.
    eapply Fundamental in Hconv as [HΓ HU Hconv].
    eapply reducibleTmEq in Hconv.
    set (HUred := reducibleTy _ HU) in *.
    clearbody HUred.
    clear HU.
    assert (HTred : [Γ ||-< zero > T]) by now eapply Universe.UnivEq.
    unshelve eapply Universe.UnivEqEq in Hconv ; tea.
    clear HUred HΓ.
    revert HTred nfT T' nfT' Hconv HT HT'.
    generalize (eq_refl : zero = zero).
    generalize zero at 1 3 ; intros l eql HT; revert eql.

    pattern l, Γ, T, HT ; apply Induction.LR_rect_TyUr; clear l Γ T HT.
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
      cbn.
      split ; gen_typing.

    - intros [dom cod red] _ _ -> nfT T' nfT' [dom' cod' red'] HT HT' ; cbn in *.
      assert (T = tProd dom cod) as HeqT by (apply red_whnf ; gen_typing). 
      assert (T' = tProd dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
      destruct nfT; cycle -1.
      1: subst ; exfalso ; gen_typing.
      all: try congruence.
      split ; [..|intros Hne ; now inversion Hne].
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
      1: now constructor.
      eapply escapeEqzero ; tea.
      eapply stability1 ; tea.

    - intros [] -> nfT T' nfT' [] ??.
      assert (T' = tNat) as HeqT' by (eapply redtywf_whnf ; gen_typing).
      assert (T = tNat) as HeqT by (eapply redtywf_whnf ; gen_typing).
      destruct nfT; inversion HeqT.
      1: destruct nfT'; inversion HeqT'.
      2-3: exfalso; subst; inversion w.
      split ; [..|intros Hne ; now inversion Hne].
      now cbn.

    - intros [] -> nfT T' nfT' [] ??.
      assert (T' = tEmpty) as HeqT' by (eapply redtywf_whnf ; gen_typing).
      assert (T = tEmpty) as HeqT by (eapply redtywf_whnf ; gen_typing).
      destruct nfT; inversion HeqT.
      1: destruct nfT'; inversion HeqT'.
      2-3: exfalso; subst; inversion w.
      split ; [..|intros Hne ; now inversion Hne].
      now cbn.

    - intros [dom cod red] _ _ -> nfT T' nfT' [dom' cod' red'] ?? ; cbn in *.
      assert (T = tSig dom cod) as HeqT by (apply red_whnf ; gen_typing).
      assert (T' = tSig dom' cod') as HeqT' by (apply red_whnf ; gen_typing).
      destruct nfT; cycle -1.
      1: subst; inv_whne.
      all: try congruence.
      split ; [..|intros Hne ; now inversion Hne].
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
      split ; [..|intros Hne ; now inversion Hne].
      split.
      2-3: now Escape.escape.
      now eapply escapeEqzero.
  Qed.

  Lemma _nat_conv_inj : forall (Γ : context) (t t' : term) (nft : isNat t) (nft' : isNat t'),
    [Γ |-[de] t ≅ t' : tNat] ->
    nat_hd_view Γ nft nft' × (whne t -> [Γ |-[de] t ~ t' : tNat]).
  Proof.
    intros * Hconv.
    eapply Fundamental in Hconv as [HΓ Hnat Hconv].
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
    
    - exact (fun n n' _ => forall (nft : isNat n) (nft' : isNat n'),
      nat_hd_view Γ nft nft' × (whne n -> [Γ |-[de] n ~ n' : tNat])).
    
    - cbn.
      intros t u t' u' [_ redt%redtm_sound] [_ redu%redtm_sound] ? _ IH Ht Hu.
      eapply red_whnf in redt as ->, redu as ->.
      2-3: gen_typing.
      eauto.

    - cbn.
      intros nft nft'.
      rewrite (isNat_zero nft), (isNat_zero nft') ; cbn.
      split ; [easy|..].
      intros Hne ; now inversion Hne.

    - cbn.
      intros ?? [] _ nft nft'.
      rewrite (isNat_succ _ nft), (isNat_succ _ nft') ; cbn.
      split ; [..|intros Hne ; now inversion Hne].
      eapply convtm_exp ; gen_typing.

    - cbn.
      intros ?? [] nft nft' ; refold.
      epose proof (isNat_ne _ nft) as [? ->].
      1: now eapply conv_neu_ne in conv.
      epose proof (isNat_ne _ nft') as [? ->].
      1: now eapply conv_neu_ne in conv.
      cbn.
      split ; gen_typing.

  Qed.


  Lemma _id_conv_inj : forall (Γ : context) (A x y t t' : term) (nft : isId t) (nft' : isId t'),
    [Γ |-[de] t ≅ t' : tId A x y] ->
    id_hd_view Γ A x y nft nft' × (whne t -> [Γ |-[de] t ~ t' : tId A x y]).
  Proof.
  intros * Hconv.
  eapply Fundamental in Hconv as [HΓ Hid Hconv].
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
    split ; [..|intros Hne ; now inversion Hne].
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
    split ; gen_typing.

  Qed.

End TermConstructors.

#[local, refine] Instance TermConstructorsInjLogRel : TermConstructorsInj (ta := de) := {}.
Proof.
  - intros. now eapply _univ_conv_inj.
  - intros. now eapply _nat_conv_inj.
  - intros. now eapply _id_conv_inj.
Qed.

(** ** Inversion of conversion of neutrals *)

Section NeutralConv.

  Import DeclarativeTypingProperties DeclarativeTypingData.

  Lemma _empty_conv_inj (Γ : context) (t t' : term) :
    whne t -> whne t' ->
    [Γ |-[de] t ≅ t' : tEmpty] ->
    [Γ |-[de] t ~ t' : tEmpty].
  Proof.
    intros * wt wt' Hconv.
    eapply Fundamental in Hconv as [HΓ Hemp Hconv].
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

  Lemma _neu_conv_inj (Γ : context) (A t t' : term) :
    whne A -> whne t -> whne t' ->
    [Γ |-[de] t ≅ t' : A] ->
    [Γ |-[de] t ~ t' : A].
  Proof.
    intros * wA wt wt' Hconv.
    eapply Fundamental in Hconv as [HΓ Hne Hconv].
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

End NeutralConv.

#[local, refine] Instance ConvNeutralConvPosLogRel : ConvNeutralConvPos (ta := de) := {}.
Proof.
  intros * ?? [] Hconv.
  - destruct s.
    eapply _univ_conv_inj ; gen_typing.
  - eapply _nat_conv_inj ; gen_typing.
  - eapply _empty_conv_inj ; gen_typing.
  - eapply _id_conv_inj ; gen_typing.
  - eapply _neu_conv_inj ; gen_typing.
Qed.

(** ** Completeness *)

Section Completeness.

  Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!RedTerm ta}
  `{!GenericTypingProperties ta _ _ _ _ _ _ _ _ _ _}.

  #[local, refine] Instance ConvCompleteLogRel : ConvComplete (ta := de) (ta' := ta) := {}.
  Proof.
    - now intros * [HΓ ? _ ?%(escapeEq (ta := ta))]%Fundamental.
    - now intros * [HΓ ? ?%(escapeTmEq (ta := ta)) ]%Fundamental.
  Qed.

  #[local, refine] Instance TypingCompleteLogRel : TypingComplete (ta := de) (ta' := ta) := {}.
  Proof.
    - now intros * [HΓ ?%(escapeTy (ta := ta))]%Fundamental.
    - now intros * [_ _ ?%escapeTm]%(Fundamental (ta := ta)).
  Qed.

End Completeness.

(** ** Weak-head normalisation *)

Section Normalisation.

  Lemma norm_wk : forall t (ρ : nat -> nat), normalising t -> normalising t⟨ρ⟩.
  Proof.
    intros * [r].
    exists r⟨ρ⟩.
    + now apply credalg_wk.
    + now apply whnf_ren.
  Qed.

  Lemma norm_exp : forall t u, [t ⤳* u] -> normalising u -> normalising t.
  Proof.
    intros t u ? [r].
    exists r; tea.
    now etransitivity.
  Qed.

  Lemma norm_whnf : forall t, whnf t -> normalising t.
  Proof.
    intros; exists t; tea.
    reflexivity.
  Qed.

  Lemma norm_isFun : forall t, isFun t -> normalising t.
  Proof.
    intros t []; apply norm_whnf; now constructor.
  Qed.

  Lemma norm_isPair : forall t, isPair t -> normalising t.
  Proof.
    intros t []; apply norm_whnf; now constructor.
  Qed.

  Let nf : tag := mkTag.

  #[local] Instance WfContextNf : WfContext nf := fun Γ => True.
  #[local] Instance WfTypeNf : WfType nf := fun Γ A => True.
  #[local] Instance TypingNf : Typing nf := fun Γ A t => True.
  #[local] Instance ConvTypeNf : ConvType nf := fun Γ A B => normalising A × normalising B.
  #[local] Instance ConvTermNf : ConvTerm nf := fun Γ A t u => normalising t × normalising u.
  #[local] Instance ConvNeuConvNf : ConvNeuConv nf := fun Γ A m n => whne m × whne n.
  #[local] Instance RedTypeNf : RedType nf := fun Γ A B => [A ⤳* B].
  #[local] Instance RedTermNf : RedTerm nf := fun Γ A t u => [t ⤳* u].

  #[local, refine] Instance WfCtxNfProperties : WfContextProperties (ta := nf) := {}.
  Proof.
  all: try constructor.
  Qed.

  #[local, refine] Instance WfTypeNfProperties : WfTypeProperties (ta := nf) := {}.
  Proof.
  all: try constructor.
  Qed.

  #[local, refine] Instance TypingNfProperties : TypingProperties (ta := nf) := {}.
  Proof.
  all: try constructor.
  Qed.

  #[local, refine] Instance ConvTypeNfProperties : ConvTypeProperties (ta := nf) := {}.
  Proof.
  all: try (intros; split; apply norm_whnf; now constructor).
  + intros * []; now split.
  + intros; split.
    - intros t u []; now split.
    - intros t u v [] []; now split.
  + intros * ? []; split; now apply norm_wk.
  + intros * ? ? []; split; now eapply norm_exp.
  Qed.

  #[local, refine] Instance ConvTermNfProperties : ConvTermProperties (ta := nf) := {}.
  Proof.
  all: try (intros; split; apply norm_whnf; now constructor).
  + intros; split.
    - intros t u []; now split.
    - intros t u v [] []; now split.
  + intros * [] ?; now split.
  + intros * ? []; split; now apply norm_wk.
  + intros * ? ? ? ? ? ? []; split; now eapply norm_exp.
  + intros * ? []; split; now apply norm_whnf, whnf_whne.
  + intros * ? ? ? Hf ? Hg []; split.
    - apply norm_isFun; destruct Hf as [|? []]; now constructor.
    - apply norm_isFun; destruct Hg as [|? []]; now constructor.
  + intros * ? ? ? Hp ? Hp' ?; split; apply norm_isPair.
    - destruct Hp as [|? []]; now constructor.
    - destruct Hp' as [|? []]; now constructor.
  Qed.

  #[local, refine] Instance ConvNeuNfProperties : ConvNeuProperties (ta := nf) := {}.
  Proof.
  + intros; split.
    - intros t u []; now split.
    - intros t u v [] []; now split.
  + intros * [] ?; now split.
  + intros * ? []; split; now apply whne_ren.
  + intros * []; assumption.
  + intros; split; constructor.
  + intros * [] ?; split; now constructor.
  + intros * ? ? ? []; split; now constructor.
  + intros * ? []; split; now constructor.
  + intros * []; split; now constructor.
  + intros * []; split; now constructor.
  + intros * ??????? []; split; now constructor.
  Qed.

  #[local, refine] Instance RedTermNfProperties : RedTermProperties (ta := nf) := {}.
  Proof.
  all: try now (intros; apply redalg_one_step; constructor).
  + intros; now apply credalg_wk.
  + intros; eassumption.
  + now constructor.
  + intros; now apply redalg_app.
  + intros; now apply redalg_natElim.
  + intros; now apply redalg_natEmpty.
  + intros; now apply redalg_fst.
  + intros; now apply redalg_snd.
  + intros; now eapply redalg_idElim.
  + intros; assumption.
  + intros; reflexivity.
  Qed.

  #[local, refine] Instance RedTypeNfProperties : RedTypeProperties (ta := nf) := {}.
  Proof.
  all: try now intros; eassumption.
  + intros; now apply credalg_wk.
  + constructor.
  + intros; reflexivity.
  Qed.

  #[local] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ _ _ := {}.

  Corollary _tm_norm {Γ A t} : [Γ |-[de] t : A] -> normalising t.
  Proof. 
    intros [?? H]%TermRefl%Fundamental.
    eapply (escapeTmEq (ta := nf)) in H as [].
    assumption.
  Qed.

  Corollary _ty_norm {Γ A} : [Γ |-[de] A] -> normalising A.
  Proof.
    intros [??? H]%TypeRefl%Fundamental.
    eapply (escapeEq (ta := nf)) in H as [].
    assumption.
  Qed.

End Normalisation.

#[local, refine] Instance NormalisationLogRel : Normalisation (ta := de) := {}.
  Proof.
    all: intros ; eauto using _tm_norm, _ty_norm.
  Qed.