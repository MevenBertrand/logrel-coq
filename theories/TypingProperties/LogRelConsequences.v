(** * LogRel.LogRelConsequences: the properties from PropertiesDefinition are consequences of the logical relation. *)
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences NormalisationConsequences.

From LogRel Require Import LogicalRelation Fundamental.
From LogRel.LogicalRelation Require Import Escape Irrelevance Transitivity Neutral Induction NormalRed.
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
      unshelve eapply transEq.
      4: now apply Vconv.
      2-3: unshelve eapply VB ; tea.
      all: irrValid.
    - intros * Ht * HΔ Hσ.
      unshelve eapply Fundamental_subst_conv in Hσ as [].
      1,3: boundary.
      apply Fundamental in Ht as [VΓ VA Vt Vu Vtu] ; cbn in *.
      unshelve eapply escapeEqTerm.
      2: now unshelve eapply VA ; tea ; irrValid.
      cbn.
      eapply transEqTerm.
      + cbn.
        unshelve eapply Vtu.
      + cbn.
        eapply Vu.
        all: irrValid.
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


  Lemma ty_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
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
    intros [???? H]%TermRefl%Fundamental.
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

(** ** Canonicity **)

(** Every closed natural number is a numeral, i.e. an iteration of [tSucc] on [tZero]. *)

Section NatCanonicityInduction.

  Import WeakDeclarativeTypingProperties WeakDeclarativeTypingData.

  Let numeral : nat -> term := fun n => Nat.iter n tSucc tZero.

  #[local] Coercion numeral : nat >-> term.

  #[local] Lemma red_nat_empty : [ε ||-Nat tNat].
  Proof.
    repeat econstructor.
  Qed.

  Lemma nat_red_empty_ind :
    (forall t, [ε ||-Nat t : tNat | red_nat_empty] ->
    ∑ n : nat, [ε |- t ≅ n : tNat]) ×
    (forall t, NatProp red_nat_empty t -> ∑ n : nat, [ε |- t ≅ n : tNat]).
  Proof.
    apply NatRedInduction.
    - intros * [? []] ? _ [n] ; refold.
      exists n.
      now etransitivity.
    - exists 0 ; cbn.
      now repeat constructor.
    - intros ? _ [n].
      exists (S n) ; simpl.
      now econstructor.
    - intros ? [? ?].
      exfalso.
      eapply no_neutral_empty_ctx ; tea.
      now eapply convneu_whne.
  Qed.

  Lemma _nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ n : tNat].
  Proof.
    intros Ht.
    assert [LRNat_ one red_nat_empty | ε ||- t : tNat] as ?%nat_red_empty_ind.
    {
      apply Fundamental in Ht as [?? Vt%reducibleTm].
      irrelevance.
    }
    now assumption.
  Qed.

End NatCanonicityInduction.

#[local, refine] Instance NatCanonicityLogRel : NatCanonicity (ta := de) := {}.
Proof.
  auto using _nat_canonicity.
Qed.