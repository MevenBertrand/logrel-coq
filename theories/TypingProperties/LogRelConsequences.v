(** * LogRel.LogRelConsequences: the properties from PropertiesDefinition are consequences of the logical relation. *)
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeConstructorsInj NeutralConvProperties NormalisationConsequences.

From LogRel Require Import LogicalRelation Fundamental.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Nat Empty.
From LogRel.Validity Require Import Validity Irrelevance Properties ValidityTactics.

From Equations Require Import Equations.

Set Printing Primitive Projection Parameters.

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
      apply Fundamental in Ht as [VΓ VA].
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
      apply Fundamental in Ht as [VΓ VA] ; cbn in *.
      unshelve eapply LogicalRelation.Escape.escapeEq.
      2: unshelve eapply VA ; tea; now eapply irrelevanceSubst.
    - intros * Ht * HΔ Hσ.
      unshelve eapply Fundamental_subst_conv in Hσ as [? Vσ].
      1,3: boundary.
      apply Fundamental in Ht as [VΓ VA Vtu] ; cbn in *.
      eapply (irrelevanceSubst _ VΓ _ HΔ) in Vσ; instValid Vσ; now escape.
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
    eapply Fundamental in Hconv as [HΓ Hconv].
    pose proof (whredR (redValidTy Hconv)) as [].
    eexists; split; [gtyping| tea].
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

  Lemma type_hd_view_irr {Γ T0 T0' T1 T1'}
    (nfT0 : isType T0) (nfT0' : isType T0') (nfT1 : isType T1) (nfT1' : isType T1') :
    T0 = T1 -> T0' = T1' -> type_hd_view Γ nfT0 nfT0' -> type_hd_view Γ nfT1 nfT1'.
  Proof.
    intros ??.
    enough (h : type_hd_view Γ nfT0 nfT0' = type_hd_view Γ nfT1 nfT1')
    by now rewrite h.
    subst; f_equal; apply isType_uniq.
  Qed.

  Lemma _ty_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
    [Γ |- T ≅ T'] ->
    type_hd_view Γ nfT nfT'.
  Proof.
    intros * Hconv.
    assert (wfΓ : [|- Γ]) by gtyping.
    eapply Fundamental in Hconv as [HΓ Hconv].
    eapply redValidTy in Hconv.
    eapply (type_hd_view_irr (whredL Hconv).(tyred_whnf_isType) (whredR Hconv).(tyred_whnf_isType)).
    1,2: symmetry ; now eapply whredty_whnf, isType_whnf.
    clear nfT nfT' HΓ; remember one as l eqn: e; revert e wfΓ.
    caseLR Hconv; cbn; try easy.
    - intros [] _ _; gtyping.
    - intros RΠ _ ?; split. 1: now destruct RΠ.
      now unshelve eapply escapeEq, (instKripkeFamConv _ RΠ.(PolyRed.posRed)).
    - intros RΣ _ ?; split. 1: now destruct RΣ.
      now unshelve eapply escapeEq, (instKripkeFam _ RΣ.(PolyRed.posRed)).
    - intros [] _ _; escape; now split.
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

Instance whredTmLR `{GenericTypingProperties} {Γ A B l} (RAB : [Γ ||-<l> A ≅ B]) :
  WhRedTmRel Γ (whredL RAB).(tyred_whnf) (RAB.(LRPack.eqTm)).
Proof.
  caseLR RAB; intros; try typeclasses eauto.
  - apply URedTmEqWhRedRel.
  - apply neRedTmWhRedTm.
  - apply IdRedTmWhRedRel.
Defined.
(* whredtm_conv *)

Section TermConstructors.

  Import DeclarativeTypingProperties DeclarativeTypingData.

  (* TODO: Unused ? *)
  Lemma escapeEqzero_fwd {Γ A B l} (lr : [Γ ||-< l > A ≅ B]) :
    let A':= (whredL lr).(tyred_whnf) in
    let B':= (whredR lr).(tyred_whnf) in
    [Γ |- A ≅ B : U] -> [Γ |- A' ≅ B' : U].
  Proof.
    intros ?? [?? ?%redValidTm]%Fundamental.
    subst A' B'.
    assert (Vtu' : [LRU_ (invLRU (redValidTy VA)) | _ ||- A ≅ B : _]) by now eapply irrLR.
    pose proof (whredtm_ty_det (whredL lr) (whredtmL Vtu')) as ->.
    pose proof (whredtm_ty_det (whredR lr) (whredtmR Vtu')) as ->.
    apply (whredtm_conv Vtu').
  Qed.

  Lemma escapeEqzero_bwd {Γ A B l} (lr : [Γ ||-< l > A ≅ B]) :
    let A':= (whredL lr).(tyred_whnf) in
    let B':= (whredR lr).(tyred_whnf) in
    [Γ |- A : U] -> [Γ |- B : U] ->
    ([Γ |- A' : U] -> [Γ |- B' : U] -> [Γ |- A' ≅ B' : U]) ->
    [Γ |- A ≅ B : U].
  Proof.
    intros; subst A' B'.
    destruct (whredL lr) as [A'], (whredR lr) as [B']; cbn in *.
    assert [Γ |-[de] A ⤳ A' : U] by (eapply subject_reduction; gtyping).
    assert [Γ |-[de] B ⤳ B' : U] by (eapply subject_reduction; gtyping).
    assert [Γ |-[de] A' : U] by boundary.
    assert [Γ |-[de] B' : U] by boundary.
    eapply convtm_exp; cycle -1; [eauto|..]; tea; gtyping.
  Qed.


  Lemma escapeEqzero {Γ A B} (lr : [Γ ||-< zero > A ≅ B]) :
    [Γ |- A : U] ->
    [Γ |- B : U] ->
    [Γ |- A ≅ B : U].
  Proof.
    intros wtA wtB; eapply (escapeEqzero_bwd lr); tea.
    remember zero as l eqn:e; revert e; clear wtA wtB; indLR lr; cbn.
    + intros [? lt] -> **.
      inversion lt.
    + intros [] -> **; gtyping.
    + intros [dom dom' cod cod'] IHdom IHcod eql
      [? [? [[-> ??] _]]%termGen']%dup
      [? [? [[-> ??] _]]%termGen']%dup
      ; cbn in *.

      assert (wfΓ : [|- Γ]) by gtyping.

      assert (hdom : [Γ |-[de] dom ≅ dom' : U]).
      {
        unshelve epose proof (H := escapeEqzero_bwd _ _ _ (IHdom Γ wk_id wfΓ eql)).
        1,2: now rewrite wk_id_ren_on.
        now rewrite 2! wk_id_ren_on in H.
      }

      assert [Γ,, dom |-[ de ] cod ≅ cod' : U].
      {
        unshelve epose proof (IHcod (Γ,,dom) _ _ (wk1 dom) _ (Neutral.var0 _ _ _) eql) as IHcod'.
        2: now rewrite wk1_ren_on.
        1,2: gtyping.
        unshelve epose proof (H := escapeEqzero_bwd _ _ _ IHcod').
        1,2: rewrite var0_wk1_id; tea; now eapply stability1.
        now rewrite 2! var0_wk1_id in H.
      }

      now constructor.

    + intros; gtyping.
    + intros; gtyping.
    + intros [dom dom' cod cod'] IHdom IHcod eql
      [? [? [[-> ??] _]]%termGen']%dup
      [? [? [[-> ??] _]]%termGen']%dup
      ; cbn in *.
      assert (wfΓ : [|- Γ]) by gtyping.

      assert (hdom : [Γ |-[de] dom ≅ dom' : U]).
      {
        unshelve epose proof (H := escapeEqzero_bwd _ _ _ (IHdom Γ wk_id wfΓ eql)).
        1,2: now rewrite wk_id_ren_on.
        now rewrite 2! wk_id_ren_on in H.
      }

      assert [Γ,, dom |-[ de ] cod ≅ cod' : U].
      {
        unshelve epose proof (IHcod (Γ,,dom) _ _ (wk1 dom) _ (Neutral.var0 _ _ _) eql) as IHcod'.
        2: now rewrite wk1_ren_on.
        1,2: gtyping.
        unshelve epose proof (H := escapeEqzero_bwd _ _ _ IHcod').
        1,2: rewrite var0_wk1_id; tea; now eapply stability1.
        now rewrite 2! var0_wk1_id in H.
      }

      now constructor.

    + intros []; cbn; intros ih eql [? [? [[-> ??] _]]%termGen']%dup [? [? [[-> ??] _]]%termGen']%dup.
      escape; constructor; tea.
      eapply (escapeEqzero_bwd tyRed); tea; eauto.
  Qed.

  Lemma univ_hd_view_irr {Γ T0 T0' T1 T1'}
    (nfT0 : isType T0) (nfT0' : isType T0') (nfT1 : isType T1) (nfT1' : isType T1') :
    T0 = T1 -> T0' = T1' -> univ_hd_view Γ nfT0 nfT0' -> univ_hd_view Γ nfT1 nfT1'.
  Proof.
    intros ??.
    enough (h : univ_hd_view Γ nfT0 nfT0' = univ_hd_view Γ nfT1 nfT1')
    by now rewrite h.
    subst; f_equal; apply isType_uniq.
  Qed.

  #[local]
  Theorem _univ_conv_view : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
    [Γ |-[de] T ≅ T' : U] ->
    univ_hd_view Γ nfT nfT'.
  Proof.
    intros * [HconvU Hconv]%dup.
    assert (wfΓ : [|- Γ]) by gtyping.
    eapply Fundamental in Hconv as [HΓ ? Hconv].
    eapply redValidTm, (UnivEq zero) in Hconv.
    assert ([Γ |- (whredL Hconv).(tyred_whnf) : U] × [Γ |- (whredR Hconv).(tyred_whnf) : U]) as [wtL wtR]
    by (pose proof (escapeEqzero_fwd Hconv HconvU); split; boundary).
    eapply (univ_hd_view_irr (whredL Hconv).(tyred_whnf_isType) (whredR Hconv).(tyred_whnf_isType)).
    1,2: symmetry ; now eapply whredty_whnf, isType_whnf.
    remember zero as l eqn: e; revert e wfΓ wtL wtR; clear nfT nfT' HΓ VA HconvU;  caseLR Hconv; cbn; try easy.
    - intros [? lt] ?; subst; inversion lt.
    - intros [] **; cbn; gtyping.
    - intros []; cbn; intros -> ? [? [? [[-> ??] _]]%termGen']%dup [? [? [[-> ??] _]]%termGen']%dup.
      split.
      + eapply escapeEqzero; tea; symmetry.
        apply (instKripke wfΓ (PolyRed.shpRed polyRed)).
      + eapply stability1; [now symmetry|].
        eapply escapeEqzero; tea; [| now eapply stability1].
        apply (instKripkeFam wfΓ (PolyRed.posRed polyRed)).
    - intros []; cbn; intros -> ? [? [? [[-> ??] _]]%termGen']%dup [? [? [[-> ??] _]]%termGen']%dup.
      split.
      + eapply escapeEqzero; tea.
        apply (instKripke wfΓ (PolyRed.shpRed polyRed)).
      + eapply escapeEqzero; tea; [| now eapply stability1].
        apply (instKripkeFam wfΓ (PolyRed.posRed polyRed)).
    - intros []; cbn; intros -> ? [? [[->] _]]%termGen' [? [[->] _]]%termGen'.
      escape; split; tea.
      now eapply escapeEqzero.
  Qed.


  Theorem _univ_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
    [Γ |-[de] T ≅ T' : U] ->
    univ_hd_view Γ nfT nfT' × (whne T -> [Γ |-[de] T ~ T' : U]).
  Proof.
    split; [now apply _univ_conv_view|].
    intros neT.
    eapply Fundamental in H as [?? Hconv%redValidTm%(UnivEq zero)].
    unshelve epose proof (invLREqL Hconv _ (NeType neT)) as [[] []]; [reflexivity|].
    cbn in *; pose proof (redtywf_whnf redR (isType_whnf _ nfT')); now subst.
  Qed.


  Lemma NatPropEq_isNat {Γ : context} {t t' : term} :
    NatPropEq Γ t t' -> isNat t × isNat t'.
  Proof.
    intros [| |?? []]; split; constructor.
    all: eapply convneu_whne; eassumption + now symmetry.
  Defined.

  Lemma _nat_prop_inj (Γ : context) (wfΓ : [|-Γ]) (t t' : term) (Rt : NatPropEq Γ t t')
    (nftt' := NatPropEq_isNat Rt) : nat_hd_view Γ (fst nftt') (snd nftt').
  Proof.
    induction Rt as [| ?? Rn| ?? []]; cbn; try easy; [|gtyping].
    (unshelve now eapply (escapeTm (Nat.natRed wfΓ))); constructor.
  Qed.

  Lemma isNat_uniq {t} (p q : isNat t) : p = q.
  Proof.
    destruct p; depind q; try easy; try now inversion w.
    f_equal; eapply whne_uniq.
  Qed.

  Lemma nat_hd_view_irr {Γ t0 t0' t1 t1'}
    (nft0 : isNat t0) (nft0' : isNat t0') (nft1 : isNat t1) (nft1' : isNat t1') :
    t0 = t1 -> t0' = t1' -> nat_hd_view Γ nft0 nft0' -> nat_hd_view Γ nft1 nft1'.
  Proof.
    intros ??.
    enough (h : nat_hd_view Γ nft0 nft0' = nat_hd_view Γ nft1 nft1')
    by now rewrite h.
    subst; f_equal; apply isNat_uniq.
  Qed.

  Lemma _nat_conv_inj : forall (Γ : context) (t t' : term) (nft : isNat t) (nft' : isNat t'),
    [Γ |-[de] t ≅ t' : tNat] ->
    nat_hd_view Γ nft nft' × (whne t -> [Γ |-[de] t ~ t' : tNat]).
  Proof.
    intros * Hconv.
    eapply Fundamental in Hconv as [HΓ Hnat Hconv].
    eapply redValidTm in Hconv.
    assert (wfΓ : [|- Γ]) by (escape; gtyping).
    assert (Rt : [Nat.natRed (l:=one) wfΓ| _ ||- t ≅ t' : _]) by now eapply irrLR.
    pose proof (whredtm_whnf (whredtmL Rt) (isNat_whnf _ nft)).
    pose proof (whredtm_whnf (whredtmR Rt) (isNat_whnf _ nft')).
    destruct Rt; cbn in *; subst; split.
    1: now unshelve now eapply nat_hd_view_irr, _nat_prop_inj.
    destruct prop as [| | ?? []]; intros h; tea; now inversion h.
  Qed.


  Lemma IdPropEq_isId {Γ l A x y} {t t' : term} {IA : [Γ ||-Id<l> tId A x y ≅ tId A x y]}:
    IdPropEq IA t t' -> isId t × isId t'.
  Proof.
    intros [|?? []]; split; constructor.
    all: eapply convneu_whne; eassumption + now symmetry.
  Defined.

  Lemma _id_prop_inj {Γ l A x y} {t t' : term} (IA : [Γ ||-<l> tId A x y ≅ tId A x y])
   (Rt : IdPropEq (normRedId IA) t t') (nftt' := IdPropEq_isId Rt) :
   id_hd_view Γ A x y (fst nftt') (snd nftt').
  Proof.
    induction Rt as [| ?? []]; cbn in * ; [split|gtyping].
    - etransitivity; tea; now symmetry.
    - eapply convtm_conv; tea; etransitivity; [symmetry|]; now eapply escapeTm.
  Qed.

  Lemma isId_uniq {t} (p q : isId t) : p = q.
  Proof.
    destruct p; depind q; try easy; try now inversion w.
    f_equal; eapply whne_uniq.
  Qed.

  Lemma id_hd_view_irr {Γ A x y t0 t0' t1 t1'}
    (nft0 : isId t0) (nft0' : isId t0') (nft1 : isId t1) (nft1' : isId t1') :
    t0 = t1 -> t0' = t1' -> id_hd_view Γ A x y nft0 nft0' -> id_hd_view Γ A x y nft1 nft1'.
  Proof.
    intros ??.
    enough (h : id_hd_view Γ A x y nft0 nft0' = id_hd_view Γ A x y nft1 nft1')
    by now rewrite h.
    subst; f_equal; apply isId_uniq.
  Qed.

  Lemma _id_conv_inj Γ A x y t t' (nft : isId t) (nft' : isId t') :
    [Γ |-[de] t ≅ t' : tId A x y] ->
    id_hd_view Γ A x y nft nft' × (whne t -> [Γ |-[de] t ~ t' : tId A x y]).
  Proof.
    intros * Hconv.
    eapply Fundamental in Hconv as [HΓ Hid Hconv].
    eapply redValidTm in Hconv.
    assert (Rt : [LRId' (normRedId (redValidTy Hid))| _ ||- t ≅ t' : _]) by now eapply irrLR.
    pose proof (whredtm_whnf (whredtmL Rt) (isId_whnf _ nft)).
    pose proof (whredtm_whnf (whredtmR Rt) (isId_whnf _ nft')).
    destruct Rt; cbn in *; subst; split.
    1: (unshelve now eapply id_hd_view_irr, _id_prop_inj); cycle 2; tea.
    destruct prop as [| ?? []]; intros h; tea; now inversion h.
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
    eapply redValidTm in Hconv.
    assert (wfΓ : [|- Γ]) by (escape; gtyping).
    assert (Rt : [emptyRed (l:=one) wfΓ| _ ||- t ≅ t' : _]) by now eapply irrLR.
    pose proof (whredtm_whnf (whredtmL Rt) (whnf_whne wt)).
    pose proof (whredtm_whnf (whredtmR Rt) (whnf_whne wt')).
    now destruct Rt as [???? []]; cbn in *; subst.
  Qed.

  Lemma _neu_conv_inj (Γ : context) (A t t' : term) :
    whne A -> whne t -> whne t' ->
    [Γ |-[de] t ≅ t' : A] ->
    [Γ |-[de] t ~ t' : A].
  Proof.
    intros * wA wt wt' Hconv.
    eapply Fundamental in Hconv as [HΓ Hne Hconv].
    pose (RA := LRne_ one (invLRne wA (redValidTy Hne))).
    destruct (redValidTm' RA Hconv) as [?? redL redR].
    pose proof (redtmwf_whnf redL (whnf_whne wt)).
    pose proof (redtmwf_whnf redR (whnf_whne wt')).
    subst.
    eapply convneu_conv; tea; symmetry.
    exact (whredL_conv RA).
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
  `{!GenericTypingProperties ta _ _ _ _ _ _ _ _}.

  #[local, refine] Instance ConvCompleteLogRel : ConvComplete (ta := de) (ta' := ta) := {}.
  Proof.
    - now intros * [HΓ ?%redValidTy%(escapeEq (ta := ta))]%Fundamental.
    - now intros * [HΓ ? ?%redValidTm%(escapeTm (ta := ta)) ]%Fundamental.
  Qed.

  #[local, refine] Instance TypingCompleteLogRel : TypingComplete (ta := de) (ta' := ta) := {}.
  Proof.
    - now intros * [HΓ ?%redValidTy%(escapeTy (ta := ta))]%Fundamental.
    - now intros * [_ _ ?%redValidTm%escapeTm]%(Fundamental (ta := ta)).
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

  #[local] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ := {}.

  Corollary _tm_norm {Γ A t} : [Γ |-[de] t : A] -> normalising t.
  Proof.
    intros [?? H%redValidTm]%TermRefl%Fundamental.
    eapply (escapeTm (ta := nf)) in H as (?&?&[]).
    assumption.
  Qed.

  Corollary _ty_norm {Γ A} : [Γ |-[de] A] -> normalising A.
  Proof.
    intros [? H%redValidTy]%TypeRefl%Fundamental.
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

  #[local] Lemma red_nat_empty : [ε ||-Nat tNat ≅ tNat].
  Proof.
    repeat econstructor.
  Qed.

  Lemma nat_red_empty_ind :
  (forall t u, [ε ||-Nat t ≅ u :Nat] -> ∑ n : nat, [ε |- t ≅ n : tNat]) ×
  (forall t u, NatPropEq ε t u -> ∑ n : nat, [ε |- t ≅ n : tNat]).
  Proof.
    apply NatRedEqInduction.
    - intros * [? []] ? ? _ [n] ; refold.
      exists n.
      now etransitivity.
    - exists 0 ; cbn.
      now repeat constructor.
    - intros ? ? _ [n].
      exists (S n) ; simpl.
      now econstructor.
    - intros ? ? [? ? []].
      exfalso.
      now eapply no_neutral_empty_ctx.
  Qed.

  Lemma _nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ n : tNat].
  Proof.
    intros Ht.
    assert [LRNat_ one red_nat_empty | ε ||- t : tNat] as ?%nat_red_empty_ind.
    {
      apply Fundamental in Ht as [?? Vt%redValidTm].
      now eapply irrLR.
    }
    now assumption.
  Qed.


End NatCanonicityInduction.

#[local, refine] Instance NatCanonicityLogRel : NatCanonicity (ta := de) := {}.
Proof.
  auto using _nat_canonicity.
Qed.