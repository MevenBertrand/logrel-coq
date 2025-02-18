(** * LogRel.Normalisation: definition and properties of normalisation. *)
From Coq Require Import CRelationClasses ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping.

Record normalising (t : term) := {
  norm_val : term;
  norm_red : [ t ⤳* norm_val ];
  norm_whnf : whnf norm_val;
}.

(** Deep normalisation, based on a type to incorporate η laws *)

(** Deeply normalising terms (at a given type) *)
Inductive dnorm_tm : context -> term -> term -> Type :=
| termDeepRed {Γ t t' A A'} :
  [A ⤳* A'] ->
  [t ⤳* t'] ->
  dnf_tm Γ A' t' ->
  dnorm_tm Γ A t
(** Deep normal forms (whnf, recursively containing normalising subterms) *)
with dnf_tm : context -> term -> term -> Type :=
| termDeepPi {Γ A B} :
    dnorm_tm Γ U A ->
    dnorm_tm (Γ,,A) U B ->
    dnf_tm Γ U (tProd A B)
| termDeepNat {Γ} :
    dnf_tm Γ U tNat
| termDeepZero {Γ} :
    dnf_tm Γ tNat tZero
| termDeepSucc {Γ t} :
    dnorm_tm Γ tNat t ->
    dnf_tm Γ tNat (tSucc t)
| termDeepEmpty {Γ} :
    dnf_tm Γ U tEmpty
| termDeepFun {Γ f A B} :
    whnf f ->
    dnorm_tm (Γ,,A) B (eta_expand f) ->
    dnf_tm Γ (tProd A B) f
| termDeepSig {Γ A B} :
    dnorm_tm Γ U A ->
    dnorm_tm (Γ,,A) U B ->
    dnf_tm Γ U (tSig A B)
| termDeepPair {Γ p A B} :
  whnf p ->
  dnorm_tm Γ A (tFst p) ->
  dnorm_tm Γ B[(tFst p)..] (tSnd p) ->
  dnf_tm Γ (tSig A B) p
| termDeepId {Γ A x y} :
  dnorm_tm Γ U A ->
  dnorm_tm Γ A x ->
  dnorm_tm Γ A y ->
  dnf_tm Γ U (tId A x y)
| termDeepRefl {Γ A A' x x' y} :
  dnf_tm Γ (tId A' x' y) (tRefl A x)
| termDeepNeu {Γ m T P} :
  isPosType P ->
  dneu Γ T m ->
  dnf_tm Γ P m
(** Deep neutrals (wh neutrals, with recursively normalising/neutral subterms).
    Note that the type is "inferred". *)    
with dneu : context -> term -> term -> Type :=
| neuDeepVar {Γ n decl} :
  in_ctx Γ n decl ->
  dneu Γ decl (tRel n)
| neuDeepApp {Γ n t A B} :
  dneu_red Γ (tProd A B) n ->
  dnorm_tm Γ A t ->
  dneu Γ B[t..] (tApp n t)
| neuDeepNatElim {Γ n P hz hs} :
  dneu_red Γ tNat n ->
  dnorm_ty (Γ,,tNat) P ->
  dnorm_tm Γ P[tZero..] hz ->
  dnorm_tm Γ (elimSuccHypTy P) hs ->
  dneu Γ P[n..] (tNatElim P hz hs n)
| neuDeepEmptyElim {Γ P n} :
  dneu_red Γ tEmpty n ->
  dnorm_ty (Γ,,tEmpty) P ->
  dneu Γ P[n..] (tEmptyElim P n)
| neuDeepFst {Γ n A B} :
  dneu_red Γ (tSig A B) n ->
  dneu Γ A (tFst n)
| neuDeepSnd {Γ n A B} :
  dneu_red Γ (tSig A B) n ->
  dneu Γ B[(tFst n)..] (tSnd n)
| neuDeepIdElim {Γ A A' x x' P hr y y' n} :
  dneu_red Γ (tId A' x' y') n ->
  dnorm_ty (Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) P ->
  dnorm_tm Γ P[tRefl A x .: x..] hr ->
  dneu Γ P[n .: y..] (tIdElim A x P hr y n)

with dneu_red : context -> term -> term -> Type :=
| neuDeepRed {Γ n A A'} :
  dneu Γ A n ->
  [A ⤳* A'] ->
  whnf A' ->
  dneu_red Γ A' n

(** Deeply normalising types *)
with dnorm_ty : context -> term -> Type :=
| typeDeepNorm {Γ A A'} :
  [A ⤳* A'] ->
  dnf_ty Γ A' ->
  dnorm_ty Γ A
(** **** Conversion of types reduced to weak-head normal forms *)
with dnf_ty : context -> term -> Type :=
| typeDeepU {Γ} :
  dnf_ty Γ U
| typeDeepPi {Γ A B} :
  dnorm_ty Γ A ->
  dnorm_ty (Γ,,A) B ->
  dnf_ty Γ (tProd A B)
| typeDeepNat {Γ} :
  dnf_ty Γ tNat
| typeDeepEmpty {Γ} :
  dnf_ty Γ tEmpty
| typeDeepSig {Γ A B} :
  dnorm_ty Γ A ->
  dnorm_ty (Γ,,A) B ->
  dnf_ty Γ (tSig A B)
| typeDeepId {Γ A x y} :
  dnorm_ty Γ A ->
  dnorm_tm Γ A x ->
  dnorm_tm Γ A y ->
  dnf_ty Γ (tId A x y)
| typeDeepNeu {Γ m T} :
  dneu Γ T m ->
  dnf_ty Γ m.

Section InductionScheme.

  Scheme 
    Minimality for dnorm_tm Sort Type with
    Minimality for dnf_tm   Sort Type with
    Minimality for dneu     Sort Type with
    Minimality for dneu_red Sort Type with
    Minimality for dnorm_ty Sort Type with
    Minimality for dnf_ty   Sort Type.

  Combined Scheme _DeepNormInduction from
      dnorm_tm_rect_nodep,
      dnf_tm_rect_nodep,
      dneu_rect_nodep,
      dneu_red_rect_nodep,
      dnorm_ty_rect_nodep,
      dnf_ty_rect_nodep.

  Let _DeepNormInductionType :=
    ltac:(let ind := fresh "ind" in
        pose (ind := _DeepNormInduction);
        refold ;
        let ind_ty := type of ind in
        exact ind_ty).

  Let DeepNormInductionType :=
    ltac: (let ind := eval cbv delta [_DeepNormInductionType] zeta
      in _DeepNormInductionType in
      let ind' := polymorphise ind in
    exact ind').

  Lemma DeepNormInduction : DeepNormInductionType.
  Proof.
    intros PNormTm PNfTm PNeu PNeuRed PNormTy PNfTy **.
    pose proof (_DeepNormInduction PNormTm PNfTm PNeu PNeuRed PNormTy PNfTy) as H.
    destruct H as (?&?&?&?&?&?).
    all: try (assumption ; fail).
    repeat (split;[assumption|]); assumption.
  Qed.

  Definition DeepNormInductionConcl :=
    ltac:(
      let t := eval cbv delta [DeepNormInductionType] beta in DeepNormInductionType in
      let t' := remove_steps t in
      exact t').

End InductionScheme.

Lemma dnf_whnf :
  DeepNormInductionConcl
  (fun (Γ : context) (A t : term) => True)
  (fun (Γ : context) (A t : term) => isType A × whnf t)
  (fun (Γ : context) (A t : term) => whne t)
  (fun (Γ : context) (A t : term) => whnf A × whne t)
  (fun (Γ : context) (A : term) => True)
  (fun (Γ : context) (A : term) => isType A).
Proof.
  apply DeepNormInduction.
  all: intros ; prod_splitter ; prod_hyp_splitter ;
    try solve [eauto using isPosType_isType, isFun_whnf, isPair_whnf | econstructor ; eauto].
Qed.

Lemma dnf_ren :
  DeepNormInductionConcl
  (fun (Γ : context) (A t : term) => forall Δ (ρ : Δ ≤ Γ), dnorm_tm Δ A⟨ρ⟩ t⟨ρ⟩)
  (fun (Γ : context) (A t : term) => forall Δ (ρ : Δ ≤ Γ), dnf_tm Δ A⟨ρ⟩ t⟨ρ⟩)
  (fun (Γ : context) (A t : term) => forall Δ (ρ : Δ ≤ Γ), dneu Δ A⟨ρ⟩ t⟨ρ⟩)
  (fun (Γ : context) (A t : term) => forall Δ (ρ : Δ ≤ Γ), dneu_red Δ A⟨ρ⟩ t⟨ρ⟩)
  (fun (Γ : context) (A : term) => forall Δ (ρ : Δ ≤ Γ), dnorm_ty Δ A⟨ρ⟩)
  (fun (Γ : context) (A : term) => forall Δ (ρ : Δ ≤ Γ), dnf_ty Δ A⟨ρ⟩).
Proof.
  apply DeepNormInduction.
  all: try (intros ; solve [now econstructor ; eauto using credalg_wk]).
  all: try solve [econstructor ; eauto ; cbn ; now erewrite <- !wk_up_ren_on].
  - intros * ?? IH **.
    econstructor.
    1: now apply whnf_ren.
    epose proof (IH _ (wk_up _ _)) as IH' ; cbn in IH'.
    assert (forall t, t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨up_ren ρ⟩) as ->
      by (now asimpl).
    now rewrite wk_up_ren_on in IH'.
  - econstructor ; eauto.
    1: now apply whnf_ren.
    erewrite <- wk_up_ren_on, wk_fst, <- subst_ren_wk_up; eauto.
  - econstructor ; eauto.
    now apply isPosType_ren.
  - intros.
    econstructor.
    now eapply in_ctx_wk.
  - intros.
    erewrite subst_ren_wk_up.
    econstructor ; eauto.
    now rewrite wk_prod.
  - intros.
    erewrite subst_ren_wk_up.
    econstructor ; eauto.
    + now erewrite <- wk_up_ren_on.
    + now erewrite <- (wk_up_ren_on _ _ _ tNat), <- (subst_ren_wk_up (n := tZero) ρ).
    + now erewrite <- wk_up_ren_on, wk_elimSuccHypTy.
  - intros.
    erewrite subst_ren_wk_up.
    econstructor ; eauto.
  - intros.
    erewrite subst_ren_wk_up.
    econstructor ; eauto.
    now rewrite wk_sig.
  - intros * ?? ? IHP ? IHr **.
    erewrite <- !wk_idElim, subst_ren_wk_up2.
    econstructor ; eauto.
    + now erewrite !wk_up_wk1.
    + now rewrite wk_refl, <- subst_ren_wk_up2.
  - econstructor ; eauto using credalg_wk.
    now apply whnf_ren.
    Unshelve.
    all: assumption.
Qed.

Lemma dnf_det :
  DeepNormInductionConcl
    (fun (Γ : context) (A t : term) => True)
    (fun (Γ : context) (A t : term) => True)
    (fun (Γ : context) (A t : term) => forall T, dneu Γ T t -> T = A)
    (fun (Γ : context) (A t : term) => forall T, dneu_red Γ T t -> T = A)
    (fun (Γ : context) (A : term) => True)
    (fun (Γ : context) (A : term) => True).
Proof.
  apply DeepNormInduction.
  all: try easy.
  all: intros until T ; intros HT.
  all: inversion HT ; subst ; eauto using in_ctx_inj.
  all: match goal with | H : forall _ : _, _ -> _ = _, H' : _ |- _ => apply H in H' end.
  1-3: congruence.
  subst ; now eapply whred_det.
Qed.



(** Untyped deeply normalising terms *)
Inductive udnorm : term -> Type :=
| UDeepRed {t t'} :
  [t ⤳* t'] ->
  udnf t' ->
  udnorm t
(** Deep normal forms (whnf, recursively containing normalising subterms), untyped (no η-expansion) *)
with udnf : term -> Type :=
| UDeepU :
    udnf U
| UDeepPi {A B} :
    udnorm A ->
    udnorm B ->
    udnf (tProd A B)
| UDeepNat :
    udnf tNat
| UDeepZero :
    udnf tZero
| UDeepSucc {t} :
    udnorm t ->
    udnf (tSucc t)
| UDeepEmpty :
    udnf tEmpty
| UDeepLam {A f} :
    udnorm f ->
    udnf (tLambda A f)
| UDeepSig {A B} :
    udnorm A ->
    udnorm B ->
    udnf (tSig A B)
| UDeepPair {A B p q} :
  udnorm p ->
  udnorm q ->
  udnf (tPair A B p q)
| UDeepId {A x y} :
  udnorm A ->
  udnorm x ->
  udnorm y ->
  udnf (tId A x y)
| UDeepRefl {A x} :
  udnf (tRefl A x)
| UDeepNeu {m} :
  udneu m ->
  udnf m
(** Deep neutrals (wh neutrals, with recursively normalising/neutral subterms), untyped *)    
with udneu : term -> Type :=
| UDeepVar {n} :
  udneu (tRel n)
| neuUDeepApp {n t} :
  udneu n ->
  udnorm t ->
  udneu (tApp n t)
| neuUDeepNatElim {n P hz hs} :
  udneu n ->
  udnorm P ->
  udnorm hz ->
  udnorm hs ->
  udneu (tNatElim P hz hs n)
| neuUDeepEmptyElim {P n} :
  udneu n ->
  udnorm P ->
  udneu (tEmptyElim P n)
| neuUDeepFst {n} :
  udneu n ->
  udneu (tFst n)
| neuUDeepSnd {n} :
  udneu n ->
  udneu (tSnd n)
| neuUDeepIdElim {A x P hr y n} :
  udneu n ->
  udnorm P ->
  udnorm hr ->
  udneu (tIdElim A x P hr y n).

Section InductionScheme.

  Scheme 
    Minimality for udnorm Sort Type with
    Minimality for udnf   Sort Type with
    Minimality for udneu     Sort Type.

  Combined Scheme _UDeepNormInduction from
      udnorm_rect_nodep,
      udnf_rect_nodep,
      udneu_rect_nodep.

  Let _UDeepNormInductionType :=
    ltac:(let ind := fresh "ind" in
        pose (ind := _UDeepNormInduction);
        refold ;
        let ind_ty := type of ind in
        exact ind_ty).

  Let UDeepNormInductionType :=
    ltac: (let ind := eval cbv delta [_UDeepNormInductionType] zeta
      in _UDeepNormInductionType in
      let ind' := polymorphise ind in
    exact ind').

  Lemma UDeepNormInduction : UDeepNormInductionType.
  Proof.
    intros PNorm PNf PNeu  **.
    pose proof (_UDeepNormInduction PNorm PNf PNeu) as H.
    destruct H as (?&?&?).
    all: try (assumption ; fail).
    repeat (split;[assumption|]); assumption.
  Qed.

  Definition UDeepNormInductionConcl :=
    ltac:(
      let t := eval cbv delta [UDeepNormInductionType] beta in UDeepNormInductionType in
      let t' := remove_steps t in
      exact t').

End InductionScheme.

Section DeepUDeep.

  Lemma udeep_ren :
  UDeepNormInductionConcl
    (fun t => forall ρ, udnorm t⟨ρ⟩)
    (fun t => forall ρ, udnf t⟨ρ⟩)
    (fun t => forall ρ, udneu t⟨ρ⟩).
  Proof.
    apply UDeepNormInduction.
    all: try solve [econstructor ; eauto].
    intros * Hred **.
    econstructor.
    1: now eapply credalg_wk in Hred.
    eauto.
  Qed.

  Lemma udnf_whnf :
    UDeepNormInductionConcl
    (fun _ => True)
    (fun t => whnf t)
    (fun t => whne t).
  Proof.
    apply UDeepNormInduction.
    all: intros ; prod_splitter ; prod_hyp_splitter ;
      try solve [eauto using isPosType_isType, isFun_whnf, isPair_whnf | econstructor ; eauto].
  Qed.

  Lemma udeep_exp t t' : udnorm t -> [t' ⤳* t] -> udnorm t'.
  Proof.
    intros Hnorm ?.
    inversion Hnorm ; subst.
    econstructor ; [|eassumption].
    now etransitivity.
  Qed.

  Lemma udeep_red t t' : udnorm t -> [t ⤳* t'] -> udnorm t'.
  Proof.
    intros Hnorm ?.
    inversion Hnorm ; subst.
    econstructor ; [|eassumption].
    eapply whred_red_det ; tea.
    now apply udnf_whnf.
  Qed.

  (* Lemma deep_udeep :
    DeepNormInductionConcl
      (fun _ _ t => (udnorm t) × (whne t -> udneu t))
      (fun _ _ t => (udnf t) × (whne t -> udneu t))
      (fun _ _ t => udneu t)
      (fun _ _ t => udneu t)
      (fun _ t => (udnorm t) × (whne t -> udneu t))
      (fun _ t => (udnf t) × (whne t -> udneu t)).
  Proof.
    apply DeepNormInduction.
    all: try (intros ; try split ; intros ; solve
      [easy | now econstructor | match goal with | Hne : whne _ |- _ => inversion Hne end]).
    - intros ? t t' **.
      prod_hyp_splitter ; split ; intros.
      1: now econstructor.
      enough (t = t') as -> by easy.
      apply red_whnf ; gen_typing.
    - intros ? f * Hfun Hnf [? Hne].
      assert (whne f -> udneu f).
      {
        intros.
        assert (whne (eta_expand f)) as Hexp by (constructor ; now eapply whne_ren).
        specialize (Hne Hexp).
        inversion Hne ; subst.
        erewrite <- (wk_section (wk1 _)).
        eapply udeep_ren.
        now erewrite wk1_ren_on.
        Unshelve.
        all: eassumption.
      }
      split ; [..|easy].
      destruct Hfun ; [|now constructor].
      constructor.
      eapply udeep_red.
      1: eassumption.
      econstructor ; eauto using eta_expand_beta ; reflexivity.
    - intros * Hpair Hnf [IHf Hne] ? [IHs].
      assert (whne p -> udneu p).
      {
        intros.
        specialize (Hne ltac:(gen_typing)).
        now inversion Hne.
      }
      split ; [..|easy].
      destruct Hpair ; [..|now econstructor].
      constructor ; eauto.
      + eapply udeep_red.
        1: eapply IHf.
        econstructor.
        1: now econstructor.
        reflexivity.
      + eapply udeep_red.
        1: eapply IHs.
        econstructor.
        1: now econstructor.
        reflexivity.
    - intros * ? ? [].
      split.
      1: now econstructor.
      intros.
      enough (A = A') as -> by easy.
      now eapply red_whne.
  Qed. *)

End DeepUDeep.