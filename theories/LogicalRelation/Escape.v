(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All LogicalRelation GenericTyping.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProperties}.

  Lemma escape {l Γ A} :
      [Γ ||-< l > A ] ->
      [Γ |- A].
  Proof.
    intros lr.
    pattern l, Γ, A, lr.
    eapply LR_rect_TyUr.
    - intros * [].
      now gen_typing.
    - intros ? * [].
      now gen_typing.
    - intros ??? [] **; cbn in *.
      now gen_typing.
    - intros ??? []; gen_typing.
    - intros ??? []; gen_typing.
    - intros ??? [] **; gen_typing.
    - intros ??? [] **; gen_typing.
  Qed.

  Lemma escapeEq {l Γ A B} (lr : [Γ ||-< l > A]) :
      [ Γ ||-< l > A ≅ B | lr ] ->
      [Γ |- A ≅ B].
  Proof.
    pattern l, Γ, A, lr ; eapply LR_rect_TyUr.
    + intros ??? [] [].
      gen_typing.
    + intros ??? [] [].
      cbn in *.
      eapply convty_exp.
      all: gen_typing.
    + intros ??? [] * ? ? [] ; cbn in *.
      gen_typing.
    + intros ??? [] []; gen_typing.
    + intros ??? [] []; gen_typing.
    + intros ??? [] * ? ? []; cbn in *.
      eapply convty_exp. all: gen_typing.
    + intros ??? [???? red] ?? [???? red']; cbn in *.
      eapply convty_exp; tea;[eapply red | eapply red'].
  Qed.

  Definition escapeTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t : A].
  Proof.
    pattern l, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ??? [] [[]] ; cbn in *.
      gen_typing.
    - intros ??? [] [] ; cbn in *.
      gen_typing.
    - intros ??? [] * ?? [[]] ; cbn in *.
      gen_typing.
    - intros ??? [] []; gen_typing.
    - intros ??? [] []; gen_typing.
    - intros ??? [] * ?? [[]] ; cbn in *.
      gen_typing.
    - intros ??? IA _ _ [].
      unfold_id_outTy; destruct IA; cbn in *; gen_typing.
  Qed.

  Definition escapeEqTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t ≅ u : A].
  Proof.
    pattern l, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ??? [] [[] []] ; cbn in *.
      eapply (convtm_conv (A := U)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [ty] [] ; cbn in *.
      assert (isPosType ty).
      {
      constructor.
      now eapply convneu_whne.
      }
      eapply (convtm_conv (A := ty)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [dom cod] * ?? [[termL] [termR]] ; cbn in *.
      eapply (convtm_conv (A := tProd dom cod)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [] []; cbn in *.
      eapply (convtm_conv (A := tNat)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
    - intros ??? [] []; cbn in *.
      eapply (convtm_conv (A := tEmpty)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
    - intros ??? [dom cod] * ?? [[termL] [termR]] ; cbn in *.
      eapply (convtm_conv (A := tSig dom cod)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [ty lhs rhs] _ _ []; unfold_id_outTy; cbn in *.
      eapply (convtm_conv (A := tId ty lhs rhs)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
  Qed.

  Lemma escapeConv {l Γ A} (RA : [Γ ||-<l> A]) :
    forall B,
    [Γ ||-<l> A ≅ B | RA] ->
    [Γ |- B].
  Proof.
    pattern l, Γ, A, RA; eapply LR_rect_TyUr; clear l Γ A RA.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * ihdom ihcod ? []; gen_typing.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * ??? []; gen_typing.
    - intros * _ _ ? []; gen_typing.
  Qed.

End Escapes.


(* hack to redefine the symmetric version for term later *)
Ltac sym_escape RA H := idtac.
Ltac eqty_escape_right RA H := idtac.

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-< _ > _] |- _] =>
    try
     (let X := fresh "Esc" H in
     pose proof (X := escape H));
    block H
  | [H : [_ ||-<_> _ ≅ _ | ?RA ] |- _] =>
    try
      (let X := fresh "Esc" H in
      pose proof (X := escapeEq RA H)) ;
    try (eqty_escape_right RA H) ;
    block H
  (* | [H : [_ ||-<_> _ : _ | ?RA] |- _] =>
    let X := fresh "R" H in
    try pose proof (X := escapeTerm RA H) ;
    block H *)
  | [H : [_ ||-<_> _ ≅ _ : _ | ?RA] |- _] =>
    try (let X := fresh "R" H in pose proof (X := escapeEqTerm RA H)) ;
    try (let X := fresh "Rl" H in pose proof (X := escapeTerm RA H)) ;
    try (sym_escape RA H) ;
    block H
  end; unblock.
