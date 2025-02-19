(** * LogRel.Normalisation: definition and properties of normalisation. *)
From Coq Require Import CRelationClasses ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping.

Record normalising (t : term) := {
  norm_val : term;
  norm_red : [ t ⤳* norm_val ];
  norm_whnf : whnf norm_val;
}.

(** ** Deep normalisation, based on a type to incorporate η laws *)

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