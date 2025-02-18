(** * LogRel.Strengthening: proof of the strengthening property. *)
From LogRel Require Import Utils Sections Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences TypeConstructorsInj NeutralConvProperties Normalisation.
From LogRel.Algorithmic Require Import BundledAlgorithmicTyping.

Import DeclarativeTypingProperties AlgorithmicTypedConvData BundledTypingData.

  (** ** Strengthening *)
  (** Removing unused variables from a context preserves typing. *)

Section ConvStr.
  
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Γ ≤ Δ) A' B',
    A = A'⟨ρ⟩ -> B = B'⟨ρ⟩ ->
    [Δ |-[al] A' ≅ B'].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ (ρ : Γ ≤ Δ) A' B',
    A = A'⟨ρ⟩ -> B = B'⟨ρ⟩ ->
    [Δ |-[al] A' ≅h B'].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ (ρ : Γ ≤ Δ) t' u',
    t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ ->
    ∑ A', A = A'⟨ρ⟩ × [Δ |-[al] t' ~ u' ▹ A'].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Γ ≤ Δ) t' u',
    t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ ->
    ∑ A', A = A'⟨ρ⟩ × [Δ |-[al] t' ~h u' ▹ A'].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Γ ≤ Δ) t' u' A',
    A = A'⟨ρ⟩ -> t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ ->
    [Δ |-[al] t' ≅ u' : A'].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Γ ≤ Δ) t' u' A',
    A = A'⟨ρ⟩ -> t = t'⟨ρ⟩ -> u = u'⟨ρ⟩ ->
    [Δ |-[al] t' ≅h u' : A'].

  #[local] Ltac push_renaming :=
    repeat match goal with
    | eq : _ = ?t⟨_⟩ |- _ =>
        destruct t ; cbn in * ; try solve [congruence] ;
        inversion eq ; subst ; clear eq
    end.

  Theorem algo_conv_str :
    AlgoConvInductionConcl PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoConvInduction.
    - intros * Hred Hred' ? IH * -> ->.
      eapply credalg_str in Hred as [? [->]], Hred' as [? [->]].
      econstructor ; tea.
      now eapply IH.
    - intros * ? IHA ? IHB ? **.
      push_renaming.
      econstructor.
      + now eapply IHA.
      + now eapply IHB with(ρ := wk_up _ ρ).
    - intros ; push_renaming.
      econstructor.
    - intros ; push_renaming.
      now econstructor.
    - intros ; push_renaming.
      now econstructor.
    - intros * ? IHA ? IHB ? * ??.
      push_renaming.
      econstructor.
      + now eapply IHA.
      + now eapply IHB with (ρ := wk_up _ ρ).
    - intros * ? IHA ? IHa ? IHa' **.
      push_renaming.
      econstructor.
      + eapply IHA ; reflexivity.
      + eapply IHa ; reflexivity.
      + eapply IHa' ; reflexivity. 
    - intros * ?? ? IH ** ; subst.
      edestruct IH as [? [->]].
      1-2 : reflexivity.
      econstructor ; tea.
      all: now eapply whne_ren.
    - intros * Hin **.
      push_renaming.
      apply in_ctx_str in Hin as [? [-> ]].
      eexists ; split.
      1: reflexivity.
      eapply section_inj in H1 as ->.
      2: eapply section_wk.
      now econstructor.
    - intros * ? IHm ? IHt **.
      push_renaming.
      edestruct IHm as [? []].
      1-2: reflexivity.
      push_renaming.
      eexists ; split.
      2: econstructor ; tea.
      2: eapply IHt.
      2-4: reflexivity.
      now bsimpl.
    - intros * ? IHn ? IHP ? IHz ? IHs **.
      push_renaming.
      edestruct IHn as [? []].
      1-2: reflexivity.
      push_renaming.
      eexists ; split ; cycle -1.
      1: econstructor ; tea.
      + eapply IHP with (ρ := wk_up tNat ρ).
        all: reflexivity.
      + eapply IHz.
        2-3: reflexivity.
        now bsimpl.
      + eapply IHs.
        2-3: reflexivity.
        unfold elimSuccHypTy ; cbn.
        now bsimpl.
      + now bsimpl.
    - intros * ? IHn ? IHP **.
      push_renaming.
      edestruct IHn as [? []].
      1-2: reflexivity.
      push_renaming.
      eexists ; split ; cycle -1.
      1: econstructor ; tea.
      + eapply IHP with (ρ := wk_up tEmpty ρ).
        all: reflexivity.
      + now bsimpl.
    - intros * ? IHm **.
      push_renaming.
      edestruct IHm as [? []].
      1-2: reflexivity.
      push_renaming.
      eexists ; split.
      2: econstructor ; tea.
      reflexivity.
    - intros * ? IHm **.
      push_renaming.
      edestruct IHm as [? []].
      1-2: reflexivity.
      push_renaming.
      eexists ; split.
      2: econstructor ; tea.
      now bsimpl.
    - intros * ? IHn ? IHP ? IHe **.
      push_renaming.
      edestruct IHn as [? []].
      1-2: reflexivity.
      push_renaming.
      eexists ; split ; cycle -1.
      1: econstructor ; tea.
      + unshelve eapply IHP.
        * unshelve eexists.
          1: exact (_wk_up (_wk_up ρ)).
          evar (A : term) ; replace (tId _ _ _) with A ; subst A.
          1: do 2 eapply well_up ; eauto.
          now bsimpl.
        * reflexivity.
        * reflexivity.
      + eapply IHe.
        2-3: reflexivity.
        now bsimpl.
      + now bsimpl.
    - intros * ? IH red ** ; subst.
      edestruct IH as [? []].
      1-2: reflexivity.
      subst.
      eapply credalg_str in red as [? [-> ]].
      eexists ; split ; [reflexivity|..].
      econstructor ; tea.
      now eapply whnf_ren.
    - intros * red red' red'' ? IH * -> -> ->.
      eapply credalg_str in red as [? [->]], red' as [? [->]], red'' as [? [->]].
      now econstructor.
    - intros * ? IHA ? IHB **.
      push_renaming.
      econstructor.
      + eapply IHA ; reflexivity.
      + eapply IHB with (ρ := wk_up _ ρ).
        all: reflexivity.
    - intros ; push_renaming.
      econstructor.
    - intros ; push_renaming.
      econstructor.
    - intros * ? IH **.
      push_renaming.
      econstructor.
      eapply IH.
      all: reflexivity.
    - intros ; push_renaming.
      econstructor.
    - intros * ?? ? IH **.
      subst.
      push_renaming.
      econstructor.
      1-2: now eapply isFun_ren.
      eapply IH with (ρ := wk_up _ ρ).
      all: now bsimpl.
    - intros * ? IHA ? IHB **.
      push_renaming.
      econstructor.
      + eapply IHA ; reflexivity.
      + eapply IHB with (ρ := wk_up _ ρ).
        all: reflexivity.
    - intros * ?? ? IHf ? IHs **.
      subst.
      push_renaming.
      econstructor.
      1-2: now eapply isPair_ren.
      + eapply IHf ; reflexivity.
      + eapply IHs.
        2-3: reflexivity.
        now bsimpl.
    - intros * ? IHA ? IHa ? IHa' **.
      push_renaming.
      econstructor.
      + eapply IHA ; reflexivity.
      + eapply IHa ; reflexivity.
      + eapply IHa' ; reflexivity.
    - intros **.
      push_renaming.
      now econstructor.
    - intros * ? IH **.
      subst.
      edestruct IH as [? [-> ]].
      1-2: reflexivity.
      econstructor ; tea.
      now eapply isPosType_ren.
  Qed.

End ConvStr.