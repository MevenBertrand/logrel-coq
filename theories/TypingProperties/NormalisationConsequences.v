(** * LogRel.NormalisationConsequences: direct consequences of normalisation. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All Sections GenericTyping DeclarativeTyping PropertiesDefinition SubstConsequences NeutralConvProperties TypeConstructorsInj DeclarativeProperties Normalisation.

Import DeclarativeTypingProperties.


Section ConvPosNormalising.
  Context `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de}
    `{!Strengthening de} `{!ConvNeutralConvPos de} `{!DeepNormalisation de}.

  Lemma ne_conv_str_ex (Γ Δ : context) (A t u : term) (ρ : Γ ≤ Δ) :
    [ |-[ de ] Δ] ->
    [Γ |-[ de ] t⟨ρ⟩ ~ u⟨ρ⟩ : A] ->
    ∑ A', [Δ |-[ de ] t ~ u : A'] × [Γ |- A'⟨ρ⟩ ≅ A].
  Proof.
    intros HΔ Hconv.
    remember t⟨_⟩ as t' in Hconv.
    remember u⟨_⟩ as u' in Hconv.
    induction Hconv in Δ, HΔ, ρ, t, Heqt', u, Hequ' |- * ; refold.

    - destruct t ; cbn in * ; try solve [congruence].
      destruct u ; cbn in * ; try solve [congruence].
      inversion Heqt' ; subst ; clear Heqt'.
      inversion Hequ' ; subst ; clear Hequ'.
      eapply section_inj in H0.
      2: now apply section_wk.
      subst.
      eapply in_ctx_str in i as (?&->&?).
      eexists ; split.
      1: constructor ; tea.
      constructor.
      eapply typing_wk ; tea.
      eapply boundary_tm.
      now econstructor.
    - destruct t ; cbn in * ; try solve [congruence].
      destruct u ; cbn in * ; try solve [congruence].
      inversion Heqt' ; subst ; clear Heqt'.
      inversion Hequ' ; subst ; clear Hequ'.
      edestruct IHHconv as (T&Hne&(?&?&[red])%red_compl_prod_r) ; tea.
      1-2: reflexivity.
      eapply redty_sound, credalg_str in red as (T'&e&?).
      destruct T' ; cbn in * ; try solve [congruence].
      inversion e ; subst ; clear e.
      eexists ; split.
      + econstructor.
        2: eapply tm_conv_str ; tea ; now econstructor.
        econstructor ; tea.
        eapply subject_reduction_type ; tea.
        boundary.
      + unshelve erewrite subst_ren_wk_up ; [easy|..].
        eapply typing_subst1 ; tea.
        constructor.
        boundary.
    - destruct t ; cbn in * ; try solve [congruence].
      destruct u ; cbn in * ; try solve [congruence].
      inversion Heqt' ; subst ; clear Heqt'.
      inversion Hequ' ; subst ; clear Hequ'.
      edestruct IHHconv as (T&Hne&red%red_compl_nat_r) ; tea ; refold.
      1-2: reflexivity.
      eapply redty_sound, credalg_str in red as (T'&e&?).
      destruct T' ; cbn in * ; try solve [congruence].
      clear e.
      eexists ; split.
      1: econstructor.
      + econstructor ; tea.
        eapply subject_reduction_type ; tea.
        boundary.
      + unshelve eapply ty_conv_str.
        2: eapply wk_up.
        2: now rewrite !wk_up_ren_on.
        now repeat constructor.
      + eapply tm_conv_str ; tea.
        now unshelve erewrite subst_ren_wk_up, wk_up_ren_on.
      + eapply tm_conv_str ; tea.
        now unshelve erewrite <- wk_elimSuccHypTy, wk_up_ren_on.
      + unshelve erewrite subst_ren_wk_up, wk_up_ren_on ; [easy|..].
        constructor.
        eapply typing_subst1.
        2: boundary.
        change tNat with (tNat⟨ρ⟩).
        eapply typing_wk.
        1: econstructor ; [|eapply subject_reduction_type ; tea].
        all: boundary.
    - destruct t ; cbn in * ; try solve [congruence].
      destruct u ; cbn in * ; try solve [congruence].
      inversion Heqt' ; subst ; clear Heqt'.
      inversion Hequ' ; subst ; clear Hequ'.
      edestruct IHHconv as (T&Hne&red%red_compl_empty_r) ; tea ; refold.
      1-2: reflexivity.
      eapply redty_sound, credalg_str in red as (T'&e&?).
      destruct T' ; cbn in * ; try solve [congruence].
      clear e.
      eexists ; split.
      1: econstructor.
      + unshelve eapply ty_conv_str.
        2: eapply wk_up.
        2: now rewrite !wk_up_ren_on.
        now repeat constructor.
      + econstructor ; tea.
        now eapply subject_reduction_type ; boundary.
      + unshelve erewrite subst_ren_wk_up, wk_up_ren_on ; [easy|..].
        constructor.
        eapply typing_subst1.
        2: boundary.
        change tEmpty with (tEmpty⟨ρ⟩).
        eapply typing_wk.
        1: econstructor ; [|eapply subject_reduction_type ; tea].
        all: boundary.
    - destruct t ; cbn in * ; try solve [congruence].
      destruct u ; cbn in * ; try solve [congruence].
      inversion Heqt' ; subst ; clear Heqt'.
      inversion Hequ' ; subst ; clear Hequ'.
      edestruct IHHconv as (T&Hne&(?&?&[red])%red_compl_sig_r) ; tea.
      1-2: reflexivity.
      eapply redty_sound, credalg_str in red as (T'&e&?).
      destruct T' ; cbn in * ; try solve [congruence].
      inversion e ; subst ; clear e.
      eexists ; split ; tea.
      econstructor.
      econstructor ; tea.
      eapply subject_reduction_type ; tea.
      boundary.
    - destruct t ; cbn in * ; try solve [congruence].
      destruct u ; cbn in * ; try solve [congruence].
      inversion Heqt' ; subst ; clear Heqt'.
      inversion Hequ' ; subst ; clear Hequ'.
      edestruct IHHconv as (T&Hne&(?&?&[red])%red_compl_sig_r) ; tea.
      1-2: reflexivity.
      eapply redty_sound, credalg_str in red as (T'&e&?).
      destruct T' ; cbn in * ; try solve [congruence].
      inversion e ; subst ; clear e.
      eexists ; split ; tea.
      + econstructor.
        econstructor ; tea.
        eapply subject_reduction_type ; tea.
        boundary.
      + unshelve erewrite subst_ren_wk_up, wk_up_ren_on ; [easy|..].
        eapply typing_subst1 ; tea.
        constructor.
        change (tFst ?t⟨ρ⟩) with ((tFst t)⟨ρ⟩).
        eapply typing_wk.
        2: boundary.
        econstructor.
        econstructor.
        2: eapply subject_reduction_type ; tea.
        all: boundary.
    - destruct t ; cbn in * ; try solve [congruence].
      destruct u ; cbn in * ; try solve [congruence].
      inversion Heqt' ; subst ; clear Heqt'.
      inversion Hequ' ; subst ; clear Hequ'.
      edestruct IHHconv as (T&Hne&(?&?&?&[red])%red_compl_id_r) ; tea ; refold.
      1-2: reflexivity.
      eapply redty_sound, credalg_str in red as (T'&e&?).
      destruct T' ; cbn in * ; try solve [congruence].
      inversion e ; subst ; clear e.
      eexists ; split.
      1: econstructor.
      + now eapply ty_conv_str.
      + now eapply tm_conv_str.
      + unshelve eapply ty_conv_str.
        2: unshelve eapply wk_up.
        2: unshelve eapply wk_up.
        2: eassumption.
        * apply idElimMotiveCtx.
          1: eapply ty_str ; tea ; boundary.
          eapply tm_str ; tea ; boundary.
        * rewrite !wk1_ren_on in c1.
          replace (t3⟨_⟩) with t3⟨upRen_term_term (upRen_term_term ρ)⟩ by now bsimpl.
          replace (u3⟨_⟩) with u3⟨upRen_term_term (upRen_term_term ρ)⟩ by now bsimpl.
          replace ((tId _ _ _)⟨_⟩) with (tId t1⟨ρ⟩⟨↑⟩ t2⟨ρ⟩⟨↑⟩ (tRel 0)) by now bsimpl.
          assumption.
      + eapply tm_conv_str ; tea.
        eapply convtm_meta_conv ; tea ; try reflexivity.
        now bsimpl.
      + now eapply tm_conv_str.
      + econstructor ; tea.
        etransitivity.
        1: now eapply subject_reduction_type ; boundary.
        constructor.
        2-3: eapply tm_conv_str ; tea ; now econstructor.
        now eapply ty_conv_str.
      + evar (t : term).
        replace (t3[_]⟨ρ⟩) with t.
        1: unfold t ; constructor.
        2: subst t ; now bsimpl.
        eapply typing_subst2 ; tea ; try solve [boundary].
        eapply typing_meta_conv.
        2: shelve.
        econstructor.
        eapply typing_wk ; boundary.
        Unshelve.
        1: etransitivity.
        1: now eapply typing_wk ; [..|boundary] ; eapply subject_reduction_type ; tea ; boundary.
        1: econstructor ; tea.
        1-2: now econstructor.
        substify.
        now bsimpl.
    - edestruct IHHconv as (?&[]); tea.
      eexists ; split ; tea.
      now etransitivity.
  Qed.

  Corollary ne_conv_str (Γ Δ : context) (A t u : term) (ρ : Γ ≤ Δ) :
    [ |-[ de ] Δ] ->
    [Γ |-[ de ] t⟨ρ⟩ ~ u⟨ρ⟩ : A⟨ρ⟩] ->
    [Δ |-[ de ] t ~ u : A].
  Proof.
    intros ? (?&[])%ne_conv_str_ex ; tea.
    econstructor ; tea.
    now eapply ty_conv_str.
  Qed.

End ConvPosNormalising.

#[refine]Instance NormDeepNorm `{ta : tag} `{DeepNormalisation ta} : Normalisation ta := {}.
Proof.
  - intros * [* ?? ?%dnf_whnf]%tm_dnorm.
    now econstructor.
  - intros * [* ? ?%dnf_whnf]%ty_dnorm.
    econstructor ; gen_typing.
Qed.

(** ** Well-foundedness of reduction *)

Theorem typing_acc_cored Γ t `{!Normalisation de} :
  well_formed Γ t ->
  Acc cored t.
Proof.
  intros [[] Hty] ; cbn in Hty.
  all: first [
    apply ty_norm in Hty as [wh red] |
    apply tm_norm in Hty as [wh red]].
  all: induction red.
  - econstructor.
    intros t' [red].
    exfalso.
    eapply whnf_nored ; tea.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
  - econstructor.
    intros t' [red].
    exfalso.
    now eapply whnf_nored.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
Qed.

(** ** Consistency *)
(** There are no closed proofs of false, i.e. no closed inhabitants of the empty type.*)

Section Consistency.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de} `{!Normalisation de}.


  Lemma no_neutral_empty_ctx {A t} : whne t -> [ε |-[de] t : A] -> False.
  Proof.
    intros wh; induction wh in A |- *.
    - intros [? [[? [?? h]]]]%termGen'; inversion h.
    - intros [? [[? [? []]]]]%termGen'; eauto.
    - intros [? [[? []]]]%termGen'; eauto.
    - intros [? [[? []]]]%termGen'; eauto.
    - intros [? [[? [? []]]]]%termGen'; eauto.
    - intros [? [[? [? []]]]]%termGen'; eauto.
    - intros [? [[?]]]%termGen'; eauto.
  Qed.

  Lemma wty_norm {Γ t A} : [Γ |- t : A] ->
    ∑ wh, [× whnf wh, [Γ |- t ⤳* wh : A]& [Γ |- wh : A]].
  Proof.
    intros wtyt.
    pose proof (tm_norm wtyt) as [wh red].
    pose proof (h := subject_reduction _ _ _ _ wtyt red).
    assert [Γ |- wh : A] by (destruct h; boundary).
    now eexists.
  Qed.

  Lemma consistency {t} : [ε |- t : tEmpty] -> False.
  Proof.
    intros [wh []]%wty_norm; refold.
    eapply no_neutral_empty_ctx; tea.
    eapply empty_isEmpty; tea.
  Qed.

End Consistency.


(** ** Canonicity *)
(** Every closed natural number is convertible to a numeral. Note that we really need
  deep normalisation here, with only wh normalisation we would only get that a closed natural
  number is convertible to 0 or a successor, but would have no control over the argument of the latter. *)
Section Canonicity.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}
    `{!DeepNormalisation de}.

  Let Pnorm Γ A t := (Γ = ε) -> A = tNat -> [ε |- t : tNat] ->
    ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
  Let Pnf Γ A t := (Γ = ε) -> A = tNat -> [ε |- t : tNat] ->
    ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
  Let Pneu (Γ : context) (A t : term) := True.
  Let Pty (Γ : context) (A : term) := True.

  Lemma nat_canonicity {t} : [ε |- t : tNat] ->
    ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
  Proof.
    intros [Hty Hnorm%tm_dnorm]%dup.
      epose proof (DeepNormInduction Pnorm Pnf Pneu Pneu Pty Pty) as
      [Hconcl _] ; cycle -1.
    1:{
      unfold Pnorm in Hconcl.
      eapply Hconcl.
      all: eauto.
    }
    all: clear Hty Hnorm ; unfold Pnorm, Pnf, Pneu, Pty ; cbn ; try solve [constructor].
    all: try solve [congruence].
    - intros * Hred Hred' _ IH -> -> Hty.
      eapply red_whnf in Hred ; subst ; [..|gen_typing].
      eapply subject_reduction in Hred' ; tea.
      edestruct IH ; eauto.
      1: boundary.
      eexists ; etransitivity ; tea.
      now eapply RedConvTeC.
    - intros.
      exists 0 ; cbn.
      now constructor.
    - intros * _ IH -> _ (?&[->]&?)%termGen'.
      destruct IH ; eauto.
      eexists (S _) ; cbn.
      now constructor.
    - intros * ? Hne ** ; subst.
      exfalso.
      eapply no_neutral_empty_ctx ; tea.
      now eapply dnf_whnf in Hne.
  Qed.

End Canonicity.