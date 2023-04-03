(** * LogRel.DeclarativeInstance: proof that declarative typing is an instance of generic typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction UntypedValues Weakening GenericTyping DeclarativeTyping.

Import DeclarativeTypingData.

(** ** Generation *)

(** The generation lemma (the name comes from the PTS literature), gives a 
stronger inversion principle on typing derivations, that give direct access
to the last non-conversion rule, and bundle together all conversions.

Note that because we do not yet know that [Γ |- t : T] implies [Γ |- T],
we cannot use reflexivity in the case where the last rule was not a conversion
one, and we get the slightly clumsy disjunction of either an equality or a
conversion proof. We get a better version of generation later on, once we have
this implication. *)

Definition termGenData (Γ : context) (t T : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× T = decl, [|- Γ]& in_ctx Γ n decl]
    | tProd A B =>  [× T = U, [Γ |- A : U] & [Γ,, A |- B : U]]
    | tLambda A t => ∑ B, [× T = tProd A B, [Γ |- A] & [Γ,, A |- t : B]]
    | tApp f a => ∑ A B, [× T = B[a..], [Γ |- f : tProd A B] & [Γ |- a : A]]
    | tSort _ => False
    | tNat => T = U
    | tBool => T = U
    | tZero => T = tNat
    | tSucc n => T = tNat × [Γ |- n : tNat]
    | tNatElim P hz hs n =>
      [× T = P[n..], [Γ,, tNat |- P], [Γ |- hz : P[tZero..]], [Γ |- hs : elimSuccHypTy P] & [Γ |- n : tNat]]
    | tTrue => T = tBool
    | tFalse => T = tBool
    | tAlpha n => T = tBool × [Γ |- n : tNat]
    | tBoolElim P ht hf b =>
      [× T = P[b..], [Γ,, tBool |- P], [Γ |- ht : P[tTrue..]], [Γ |- hf : P[tFalse..]] & [Γ |- b : tBool]]
    | tEmpty => T = U
    | tEmptyElim P e =>
      [× T = P[e..], [Γ,, tEmpty |- P] & [Γ |- e : tEmpty]]
  end.

                       
Inductive tree Γ t : term -> Type :=
| here : forall A, termGenData Γ t A -> tree Γ t A
| conv : forall A A', termGenData Γ t A' -> [Γ |- A' ≅ A] -> tree Γ t A
| split : forall {n} {ne : not_in_LCon (pi1 (rsnd Γ)) n} {A A' A''},
    tree (Γ ,,l (ne, true)) t A' -> tree (Γ ,,l (ne, true)) t A'' ->
    [Γ ,,l (ne, true) |- A' ≅ A] -> [Γ ,,l (ne, false) |- A'' ≅ A] ->
    tree Γ t A.

(*
Lemma termGen Γ t A :
  [Γ |- t : A] -> tree Γ t A.
Proof.
  induction 1.
  - apply here ; exists decl ; split ; easy.
  - inversion  IHTypingDecl1.
    + inversion IHTypingDecl2.
      * apply here.
        split.
        reflexivity.
        eexists ; [ reflexivity | .. |  ].

    
  all: try (apply here ; eexists ; split ; [..|left ; reflexivity] ; cbn ; by_prod_splitter).

  
Lemma termGen Γ t A :
  [Γ |- t : A] ->
  (∑ A', (termGenData Γ t A') × ((A' = A) + [Γ |- A' ≅ A])).
Proof.
  induction 1.
  all: try (eexists ; split ; [..|left ; reflexivity] ; cbn ; by_prod_splitter).
  1:{ destruct IHTypingDecl as [? [? [-> | ]]].
    * prod_splitter; tea; now right.
    * prod_splitter; tea; right; now eapply TypeTrans. }
  + eexists ; split ; [ ..| left ; reflexivity].
    cbn ; prod_splitter ; auto.
    destruct IHTypingDecl1 as [? [? [-> | ]]].
    simpl.
    prod_splitter.
Qed.

Lemma prod_ty_inv Γ A B :
  [Γ |- tProd A B] ->
  [Γ |- A] × [Γ,, A |- B].
Proof.
  intros Hty.
  inversion Hty ; subst ; clear Hty.
  1: easy.
  prod_splitter.
  - apply (ϝwfType (ne := ne)).
    + inversion H.
      pose (t:= WfDeclInduction).
      apply WfDeclInduction in H.
      induction H. ; try easy.
      subst.
    easy.
    easy.
  eapply termGen in H as (?&[-> ]&_).
  split ; now econstructor.
Qed.*)

(** ** Stability by weakening *)

Lemma subst_ren_wk_up {Γ Δ P A} {ρ : Γ ≤ Δ}: forall n, P[n..]⟨ρ⟩ = P⟨wk_up A ρ⟩[n⟨ρ⟩..].
Proof. intros; now bsimpl. Qed.


Section TypingWk.
  Import DeclarativeTypingData.
  
  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩].
  Let PTm (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].



  Theorem typing_wk : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction.
    - trivial.
    - trivial.
    - intros ? ? IH.
      now econstructor.
    - admit.
    - intros Γ A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros * _  ? * IHA.
      econstructor.
      now eapply IHA.
    - admit.
    -admit.
    - intros * _ IHΓ Hnth ? * ?.
      eapply typing_meta_conv.
      1: econstructor ; tea.
      1: eapply in_ctx_wk ; tea.
      reflexivity.
    - admit.
    - intros * _ IHA _ IHB ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      econstructor ; tea.
      now eapply IHA.

    - intros * _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply typing_meta_conv.
      1: econstructor.
      1: now eapply IHf.
      1: now eapply IHu.
      now asimpl.
    - intros; now constructor.
    - intros; now constructor.
    - intros; cbn; econstructor; eauto.
    - admit.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      erewrite subst_ren_wk_up; eapply wfTermNatElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhs.
        unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
      * now eapply ihn.
    - intros; now constructor.
    - intros ; now constructor.
    - intros ; now constructor.
    - admit.
    - intros ; now constructor.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up; eapply wfTermEmptyElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * now eapply ihe.

    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - admit.
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
    - intros * _ IHA ? ρ ?.
      eapply TypeRefl.
      now eapply IHA.
    - intros * _ IH ? ρ ?.
      econstructor.
      now eapply IH.
    - intros * _ IH ? ρ ?.
      now econstructor ; eapply IH.
    - intros * _ IHA _ IHB ? ρ ?.
      eapply TypeTrans.
      + now eapply IHA.
      + now eapply IHB.
    - admit.
    - intros Γ u t A B _ IHA _ IHt _ IHu ? ρ ?.
      cbn.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHA.
      + eapply IHt with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
      + now eapply IHu.
      + now asimpl.
      + now asimpl. 
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        pose (IHA _ ρ H).
        econstructor; tea. now econstructor.
    - intros Γ u u' f f' A B _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHf.
      + now eapply IHu.
      + now asimpl.
      + now asimpl.
    - intros Γ f f' A B _ IHA _ IHf _ IHg _ IHe ? ρ ?.
      cbn.
      econstructor.
      1-3: easy.
      specialize (IHe _ (wk_up _ ρ)).
      cbn in IHe.
      repeat rewrite renRen_term in IHe.
      cbn in * ; refold.
      bsimpl.
      eapply IHe.
      econstructor ; tea.
      now eapply IHA.
    - intros * ? ih **; cbn; constructor; now apply ih.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      erewrite subst_ren_wk_up.
      eapply TermNatElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply ihhz.
        2: reflexivity.
        now erewrite subst_ren_wk_up.
      * eapply convtm_meta_conv.
        1: now eapply ihhs.
        2: reflexivity.
        unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
      * now eapply ihn.
    - intros * ? ihP ? ihhz ? ihhs **.
      erewrite subst_ren_wk_up.
      eapply TermNatElimZero; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhs.
        unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **.
      erewrite subst_ren_wk_up.
      eapply TermNatElimSucc; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhs.
        unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
      * now eapply ihn.
    - admit.
    - admit.
    - admit.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up.
      eapply TermEmptyElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * now eapply ihe.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHA ? ρ ?.
      now econstructor.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHt' ? ρ ?.
      now econstructor.
    - intros ; now econstructor.
    - admit.
    - intros * Ht Ht' Hf Hf' * H.
      eapply ϝTermConv.
      + destruct Δ as [Δ lΔ] ; destruct Γ as [Γ lΓ].
        cbn in *.
        pose (q:= fun rho =>  Ht' (Δ , lΔ) rho H).
        apply q.
      assumption.
      econstructor.
  Qed.

End TypingWk.

(** ** A first set of boundary conditions *)

(** These lemmas assert that various boundary conditions, ie that if a certain typing-like relation
holds, some of its components are themselves well-formed. For instance, if [Γ |- t ⇒* u : A] then
[Γ |- t : A ]. The tactic boundary automates usage of these lemmas. *)

(** We cannot prove yet that all boundaries are well-typed: this needs stability of typing
by substitution and injectivity of type constructors, which we get from the logical relation.*)

Section Boundaries.
  Import DeclarativeTypingData.

  Definition boundary_ctx_ctx {Γ A} : [|- Γ,, A] -> [|- Γ].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_ctx_tip {Γ A} : [|- Γ,, A] -> [Γ |- A].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_tm_ctx {Γ} {t A} :
      [ Γ |- t : A ] -> 
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ctx_ctx.
  Qed.

  Definition boundary_ty_ctx {Γ} {A} :
      [ Γ |- A ] -> 
      [ |- Γ ].
  Proof.
    induction 1; now eauto using boundary_tm_ctx.
  Qed.

  Definition boundary_tm_conv_ctx {Γ} {t u A} :
      [ Γ |- t ≅ u : A ] -> 
      [ |- Γ ].
  Proof.
      induction 1 ; now eauto using boundary_tm_ctx.
  Qed.

  Definition boundary_ty_conv_ctx {Γ} {A B} :
      [ Γ |- A ≅ B ] -> 
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ty_ctx, boundary_tm_conv_ctx.
  Qed.


  Definition boundary_ored_l {Γ t u K} : 
    [ Γ |- t ⇒ u ∈ K ] ->
    match K with istype => [ Γ |- t ] | isterm A => [ Γ |- t : A ] end.
  Proof.
    induction 1.
    all: econstructor ; eauto.
    1,3: now econstructor.
    econstructor; now eapply boundary_tm_ctx.
  Qed.

  Definition boundary_ored_tm_l {Γ t u A} : 
    [ Γ |- t ⇒ u : A] ->
    [ Γ |- t : A ].
  Proof.
  apply @boundary_ored_l with (K := isterm A).
  Qed.

  Definition boundary_ored_ty_l {Γ A B} : 
    [ Γ |- A ⇒ B ] ->
    [ Γ |- A ].
  Proof.
  apply @boundary_ored_l with (K := istype).
  Qed.

  Definition boundary_red_l {Γ t u K} : 
    [ Γ |- t ⇒* u ∈ K] ->
    match K with istype => [ Γ |- t ] | isterm A => [ Γ |- t : A ] end.
  Proof.
    induction 1; eauto.
    now eapply boundary_ored_l.
  Qed.

  Definition boundary_red_tm_l {Γ t u A} : 
    [ Γ |- t ⇒* u : A] ->
    [ Γ |- t : A ].
  Proof.
    apply @boundary_red_l with (K := isterm A).
  Qed.

  Definition boundary_red_ty_l {Γ A B} : 
    [ Γ |- A ⇒* B ] ->
    [ Γ |- A ].
  Proof.
    apply @boundary_red_l with (K := istype).
  Qed.

End Boundaries.

#[export] Hint Resolve
  boundary_ctx_ctx boundary_ctx_tip boundary_tm_ctx
  boundary_ty_ctx boundary_tm_conv_ctx boundary_ty_conv_ctx
  boundary_ored_tm_l boundary_ored_ty_l boundary_red_tm_l
  boundary_red_ty_l : boundary.


(** ** Inclusion of the various reductions in conversion *)

Definition RedConv {Γ} {t u : term} {K} :
  [Γ |- t ⇒ u ∈ K] -> 
  match K with istype => [Γ |- t ≅ u] | isterm A => [Γ |- t ≅ u : A] end.
Proof.
induction 1.
1,4,5: now econstructor.
all: econstructor; tea; now econstructor.
Qed.

Definition RedConvTe {Γ} {t u A : term} :
    [Γ |- t ⇒ u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
apply @RedConv with (K := isterm A).
Qed.

Definition RedConvC {Γ} {t u : term} {K} :
    [Γ |- t ⇒* u ∈ K] -> 
    match K with istype => [Γ |- t ≅ u] | isterm A => [Γ |- t ≅ u : A] end.
Proof.
  induction 1.
  - destruct K; now constructor.
  - now eapply RedConv.
  - destruct K; [now eapply TypeTrans|now eapply TermTrans].
Qed.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⇒* u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
apply @RedConvC with (K := isterm A).
Qed.

Definition RedConvTy {Γ} {A B : term} :
    [Γ |- A ⇒ B] -> 
    [Γ |- A ≅ B].
Proof.
apply @RedConv with (K := istype).
Qed.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⇒* B] -> 
    [Γ |- A ≅ B].
Proof.
apply @RedConvC with (K := istype).
Qed.

Lemma oredtm_meta_conv (Γ : context) (t u u' A A' : term) :
  [Γ |- t ⇒ u : A] ->
  A' = A ->
  u' = u ->
  [Γ |- t ⇒ u' : A'].
Proof.
  now intros ? -> ->.
Qed.

(** ** Weakenings of reduction *)

Lemma oreddecl_wk {Γ Δ t u K} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- t ⇒ u ∈ K] ->
  match K with istype => [Δ |- t⟨ρ⟩ ⇒ u⟨ρ⟩] | isterm A => [Δ |- t⟨ρ⟩ ⇒ u⟨ρ⟩ : A⟨ρ⟩] end.
Proof.
  intros ? red.
  induction red as [| | | | | | |]; refold.
  - cbn in *.
    eapply oredtm_meta_conv.
    1: econstructor.
    + now eapply typing_wk.
    + eapply typing_wk with (ρ := wk_up _ ρ) ; tea.
      econstructor ; tea.
      now eapply typing_wk.
    + now eapply typing_wk.
    + now asimpl.
    + now asimpl. 
  - cbn in *.
    eapply oredtm_meta_conv.
    1: econstructor.
    + now eauto.
    + now eapply typing_wk.
    + now asimpl.
    + reflexivity.
  - cbn. erewrite subst_ren_wk_up.
    eapply natElimSubst; tea.
    * erewrite <- wk_up_ren_on.
      refine (fst (snd typing_wk) _ _ w _ (wk_up _ ρ) _). 
      constructor; tea; now constructor.
    * eapply typing_meta_conv.
      1: now eapply typing_wk.
      now bsimpl.
    * eapply typing_meta_conv.
      1: now eapply typing_wk.
      unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
    Unshelve. all: tea.
  - cbn. erewrite subst_ren_wk_up.
    eapply natElimZero; tea.
    * erewrite <- wk_up_ren_on.
      refine (fst (snd typing_wk) _ _ w _ (wk_up _ ρ) _). 
      constructor; tea; now constructor.
    * eapply typing_meta_conv.
      1: now eapply typing_wk.
      now bsimpl.
    * eapply typing_meta_conv.
      1: now eapply typing_wk.
      unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
    Unshelve. all: tea.
  - cbn. erewrite (subst_ren_wk_up (A := tNat)).
    eapply natElimSucc.
    * erewrite <- wk_up_ren_on.
      refine (fst (snd typing_wk) _ _ w _ (wk_up _ ρ) _). 
      constructor; tea; now constructor.
    * eapply typing_meta_conv.
      1: now eapply typing_wk.
      now bsimpl.
    * eapply typing_meta_conv.
      1: now eapply typing_wk.
      unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
    * change tNat with tNat⟨ρ⟩; now eapply typing_wk.
  - cbn. erewrite subst_ren_wk_up.
    eapply (@emptyElimSubst _); tea.
    * erewrite <- wk_up_ren_on.
      refine (fst (snd typing_wk) _ _ w _ (wk_up _ ρ) _). 
      constructor; tea; now constructor.
    Unshelve. all: tea.
  - econstructor.
    1: eassumption.
    now eapply typing_wk.
  - now econstructor.
Qed.

Lemma oredtmdecl_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- t ⇒ u : A] -> [Δ |- t⟨ρ⟩ ⇒ u⟨ρ⟩ : A⟨ρ⟩].
Proof.
apply @oreddecl_wk with (K := isterm A).
Qed.

Lemma redtmdecl_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- t ⇒* u : A] -> [Δ |- t⟨ρ⟩ ⇒* u⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros * ?.
  induction 1.
  - econstructor ; now apply typing_wk.
  - econstructor ; now eapply oredtmdecl_wk.
  - now econstructor.
Qed.

Lemma oredtydecl_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- A ⇒ B] -> [Δ |- A⟨ρ⟩ ⇒ B⟨ρ⟩].
Proof.
apply @oreddecl_wk with (K := istype).
Qed.

Lemma redtydecl_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- A ⇒* B] -> [Δ |- A⟨ρ⟩ ⇒* B⟨ρ⟩].
Proof.
  intros * ?.
  induction 1.
  - now econstructor ; apply typing_wk.
  - now econstructor ; eapply oredtydecl_wk.
  - now econstructor.
Qed.

(** ** Derived rules for multi-step reduction *)

Lemma redtmdecl_app Γ A B f f' t :
  [ Γ |- f ⇒* f' : tProd A B ] ->
  [ Γ |- t : A ] ->
  [ Γ |- tApp f t ⇒* tApp f' t : B[t..] ].
Proof.
  intros Hf ?.
  remember (tProd A B) as T in *.
  induction Hf.
  + subst.
    now do 2 econstructor.
  + subst.
    now do 2 econstructor.
  + now econstructor.
Qed.

Lemma redtmdecl_conv Γ t u A A' : 
  [Γ |- t ⇒* u : A] ->
  [Γ |- A ≅ A'] ->
  [Γ |- t ⇒* u : A'].
Proof.
  intros Ht ?.
  induction Ht.
  + now do 2 econstructor.
  + now do 2 econstructor.
  + now econstructor.
Qed.

Lemma redtydecl_term Γ A B :
  [ Γ |- A ⇒* B : U] -> [Γ |- A ⇒* B ].
Proof.
  remember U as T.
  induction 1 ; subst.
  + now do 2 econstructor.
  + now do 2 econstructor.
  + now econstructor.
Qed.

#[export] Instance RedTermTrans Γ A : Transitive (red_tm Γ A).
Proof.
  now econstructor.
Qed.

#[export] Instance RedTypeTrans Γ : Transitive (red_ty Γ).
Proof.
  now econstructor.
Qed.

(** ** Bundling the properties together in an instance *)

Module DeclarativeTypingProperties.
  Export DeclarativeTypingData.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-2: now constructor.
    all: boundary. 
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    all: try now econstructor.
    - intros.
      now eapply typing_wk.
    - easy.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    all: try (intros; now econstructor).
    - intros.
      now eapply typing_wk.
    - easy. 
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := de) := {}.
  Proof.
  - now econstructor.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now apply typing_wk.
  - easy.
  - intros.
    eapply TypeTrans ; [eapply TypeTrans | ..].
    2: eassumption.
    2: eapply TypeSym.
    all: now eapply RedConvTyC.
  - econstructor.
    now econstructor.
  - now econstructor.
  - now do 2 econstructor.
  - now repeat econstructor.
  Qed.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de) := {}.
  Proof.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - easy.
  - intros.
    econstructor.
    2: now eapply TypeSym, RedConvTyC.
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - intros. eassumption.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - now do 2 econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de) := {}.
  Proof.
  - split ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - easy.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - now econstructor.
  - now econstructor.
  Qed.

  #[export, refine] Instance OneStepRedTermDeclProperties : OneStepRedTermProperties (ta := de) := {}.
  Proof.
    all: intros; now econstructor.
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
  - easy. 
  - intros. now eapply boundary_red_tm_l.
  - intros. now constructor.
  - intros.
    now eapply redtmdecl_app.
  - intros Γ P hz hs n n' HP Hhz Hhs Hn Hr Hcong.
    revert Hcong; induction Hr; intros Hcong.
    + apply red_id.
      now econstructor.
    + apply red_red.
      now constructor.
    + eapply red_trans.
      * apply IHHr1; [assumption|].
        intros w Hw.
        eapply TypeTrans; [apply TypeSym|]; eapply Hcong; [eassumption|].
        now transitivity t'.
      * eapply redtmdecl_conv; [eapply IHHr2|].
        -- now eapply boundary_red_tm_l.
        -- intros w Hw; now apply Hcong.
        -- eapply TypeTrans; [apply TypeSym|]; apply Hcong; [assumption|].
          now transitivity t'.
  - intros Γ P n n' HP Hn Hr Hcong.
    revert Hcong; induction Hr; intros Hcong.
    + apply red_id.
      now econstructor.
    + apply red_red.
      now constructor.
    + eapply red_trans.
      * apply IHHr1; [assumption|].
        intros w Hw.
        eapply TypeTrans; [apply TypeSym|]; eapply Hcong; [eassumption|].
        now transitivity t'.
      * eapply redtmdecl_conv; [eapply IHHr2|].
        -- now eapply boundary_red_tm_l.
        -- intros w Hw; now apply Hcong.
        -- eapply TypeTrans; [apply TypeSym|]; apply Hcong; [assumption|].
          now transitivity t'.
  - intros.
    now eapply redtmdecl_conv.
  - intros.
    now econstructor.
  Qed.

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtydecl_wk.
  - easy.
  - intros. now eapply boundary_red_ty_l.
  - intros.
    now eapply redtydecl_term.
  - intros.
    now econstructor.
  Qed.

  Export UntypedValues.WeakValuesProperties.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProperties.
