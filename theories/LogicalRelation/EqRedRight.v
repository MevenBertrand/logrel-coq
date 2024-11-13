(** * LogRel.EqRedRight: Reducibility of the rhs of a reducible conversion between types. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Reflexivity Escape Irrelevance Weakening Transitivity Neutral.

Set Universe Polymorphism.


Section Consequence.
Context `{GenericTypingProperties}.


Lemma PolyRedEqRedRight {Γ l A B A' B'} (PA : PolyRed Γ l A B)
  (ihA : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [|- Δ]) X,
    [PolyRed.shpRed PA ρ h | Δ ||- A⟨ρ⟩ ≅ X] -> [Δ ||-< l > X])
  (ihB : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [|- Δ])
    (ha : [PolyRed.shpRed PA ρ h | Δ ||- a ≅ b : A⟨ρ⟩]) X,
    [PolyRed.posRed PA ρ h ha | Δ ||- B[a .: ρ >> tRel] ≅ X] ->
    [Δ ||-< l > X]) :
  PolyRedEq PA A' B' -> PolyRed Γ l A' B'.
Proof.
  destruct PA; intros []; cbn in *.
  assert [|-Γ] by gen_typing.
  assert (hdom: forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] -> [Δ ||-< l > A'⟨ρ⟩]).
  1:{ intros; eapply ihA; eauto. Unshelve. tea. }
  assert (hcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ)
    (h : [ |-[ ta ] Δ]), [hdom Δ ρ h | Δ ||- a ≅ b : A'⟨ρ⟩] ->
    [Δ ||-< l > B'[a .: ρ >> tRel]]).
  1:{
    intros; eapply ihB; eauto. Unshelve.
    2: tea.
    2: eapply LRTmEqConv; tea.
    unshelve eapply LRTyEqSym; cycle 1 ; eauto.
  }
  assert [Γ |- A'] by now eapply escape, instKripke.
  assert [|-Γ,,A'] by gen_typing.
  unshelve econstructor; tea.
  - unshelve epose proof (hcod (Γ,,A') (tRel 0) (tRel 0) (wk1 _) _ _); tea.
    1: eapply var0; tea; now bsimpl.
    escape.
    (* These should be lemmas... *)
    replace B' with B'[tRel 0 .: wk1 (Γ := Γ) A' >> tRel]; tea.
    clear; bsimpl; rewrite scons_eta'; now bsimpl.
  - intros.
    assert [hdom Δ ρ h | _ ||- _ ≅ A⟨ρ⟩].
    1: eapply LRTyEqSym ; unshelve eauto; tea.
    assert [shpRed Δ ρ h | _ ||- a ≅ b : _].
    1: eapply LRTmEqConv; tea.
    eapply LRTransEq; [eapply LRTyEqSym, LRTransEq|].
    2,3: eauto.
    unshelve eauto; tea; now symmetry.
    Unshelve.
    2,3,5: tea.
    2: now symmetry.
Qed.

#[program]
Definition mkIdRedTy {Γ l A} ty lhs rhs (outTy := tId ty lhs rhs)
    (red : [Γ |- A :⤳*: outTy])
    (tyRed : [ LogRel l | Γ ||- ty ])
    (lhsRed : [ tyRed | Γ ||- lhs : _ ])
    (rhsRed : [ tyRed | Γ ||- rhs : _ ]) : [Γ ||-Id<l> A] :=
  {| IdRedTy.ty := ty ;
     IdRedTy.lhs := lhs ;
     IdRedTy.rhs := rhs |}.
Next Obligation.
  pose proof (reflLRTyEq tyRed).
  escape. timeout 1 gen_typing.
Qed.
Next Obligation. apply LRTmEqPER. Qed.
Next Obligation. now apply wk. Qed.
Next Obligation.
  irrelevance0. 2: now eapply wkEq.
  match goal with [ H : _ =1 _ |- _] =>
    clear -H; bsimpl; rewrite H; now bsimpl
  end.
  Unshelve. tea.
Qed.
Next Obligation.
  irrelevance0. 2: now eapply wkTermEq.
  match goal with [ H : _ =1 _ |- _] =>
    clear -H; bsimpl; rewrite H; now bsimpl
  end.
  Unshelve. tea.
Qed.

Lemma LRTyEqRedRight {Γ l A B} (RA : [Γ ||-<l> A]) :
  [RA | Γ ||- A ≅ B] -> [Γ ||-<l> B].
Proof.
  revert B; pattern l, Γ, A, RA.
  apply LR_rect_TyUr; clear l Γ A RA.
  - intros ??? [l0] ? []; eapply LRU_; exists l0; tea.
  - intros ??? [] ? [nf']; eapply LRne_; exists nf'; tea.
    cbn in *; now eapply urefl.
  - intros ??? [] ??? [A' B']; cbn in *; eapply LRPi'.
    exists A' B'; tea.
    1,2: now eapply urefl.
    now eapply PolyRedEqRedRight.
  - intros ????? []; eapply LRNat_; now constructor.
  - intros ????? []; eapply LREmpty_; now constructor.
  - intros ??? [] ??? [A' B']; cbn in *; eapply LRSig'.
    exists A' B'; tea.
    1,2: now eapply urefl.
    now eapply PolyRedEqRedRight.
  - intros ??? [] ??? [tynf l r]; cbn in *; eapply LRId', (mkIdRedTy tynf l r); tea.
    all: eapply LRTmEqConv;[| now eapply urefl]; tea.
    Unshelve. eauto.
  Qed.

End Consequence.

Ltac eqty_escape_right RA H ::=
  let X := fresh "EscR" H in
  pose proof (X := escape (LRTyEqRedRight RA H)).

