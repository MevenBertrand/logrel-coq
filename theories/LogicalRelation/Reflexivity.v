(** * LogRel.LogicalRelation.Reflexivity: reflexivity of the logical relation. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape.

Set Universe Polymorphism.
Set Printing Universes.

Section Reflexivities.
  Context `{GenericTypingProperties}.

  Definition reflLRTyEq {l Γ A} (lr : [ Γ ||-< l > A ] ) : [ Γ ||-< l > A ≅ A | lr ].
  Proof.
    pattern l, Γ, A, lr; eapply LR_rect_TyUr; intros ??? [] **.
    all: try match goal with H : PolyRed _ _ _ _ |- _ => destruct H; econstructor; tea end.
    all: try now econstructor.
    (* econstructor; tea; now eapply escapeEqTerm. *)
  Qed.


  (* Deprecated *)
  #[deprecated(note="Use reflLRTyEq")]
  Corollary LRTyEqRefl {l Γ A eqTy eqTm}
    (lr : LogRel l Γ A eqTy eqTm) : eqTy A.
  Proof.
    pose (R := Build_LRPack Γ A eqTy eqTm).
    pose (Rad := Build_LRAdequate (pack:=R) lr).
    change [Rad | _ ||- _ ≅ A ]; now eapply reflLRTyEq.
  Qed.


  Ltac eqrefl := etransitivity; tea; now symmetry.

  Lemma NeNfEqRefl {Γ k l A} : [Γ ||-NeNf k ≅ l : A] -> [Γ ||-NeNf k ≅ k : A] × [Γ ||-NeNf l ≅ l : A].
  Proof. intros []; split; econstructor; tea; eqrefl. Qed.

  Lemma NeNfEqLRefl {Γ k l A} : [Γ ||-NeNf k ≅ l : A] -> [Γ ||-NeNf k ≅ k : A].
  Proof. now intros []%NeNfEqRefl. Qed.

  Lemma NeNfEqRRefl {Γ k l A} : [Γ ||-NeNf k ≅ l : A] -> [Γ ||-NeNf l ≅ l : A].
  Proof. now intros []%NeNfEqRefl. Qed.

  Lemma reflNatRedTmEq {Γ A} {NA : [Γ ||-Nat A]} :
      (forall t u : term, [Γ ||-Nat t ≅ u : A | NA] -> [Γ ||-Nat t ≅ t : A | NA] × [Γ ||-Nat u ≅ u : A | NA])
    × (forall t u : term, NatPropEq NA t u -> NatPropEq NA t t × NatPropEq NA u u).
  Proof.
    eapply NatRedEqInduction.
    - intros * ???? [] ; split; econstructor; tea; eqrefl.
    - split; now econstructor.
    - intros * ? []; split;  now econstructor.
    - intros * []%NeNfEqRefl; split; now econstructor.
  Qed.

  Lemma reflEmptyRedTmEq {Γ A} {NA : [Γ ||-Empty A]} :
      (forall t u : term, [Γ ||-Empty t ≅ u : A | NA] -> [Γ ||-Empty t ≅ t : A | NA] × [Γ ||-Empty u ≅ u : A | NA])
    × (forall t u : term, EmptyPropEq Γ t u -> EmptyPropEq Γ t t × EmptyPropEq Γ u u).
  Proof.
    apply EmptyRedEqInduction.
    - intros * ???? []; split; econstructor; tea; eqrefl.
    - intros ?? []%NeNfEqRefl; split; now econstructor.
  Qed.

  Lemma reflIdPropEq {Γ l A} (IA : [Γ ||-Id<l> A]) t u
    (Pt : IdPropEq IA t u) : IdPropEq IA t t × IdPropEq IA u u.
  Proof.
    destruct Pt as[|??[]%NeNfEqRefl]; split; now constructor.
  Qed.

  Lemma reflIdRedTmEq {Γ l A} (IA : [Γ ||-Id<l> A]) t u (Rt : [Γ ||-Id<l> t ≅ u : _ | IA]) : [Γ ||-Id<l> t ≅ t : _ | IA] × [Γ ||-Id<l> u ≅ u : _ | IA].
  Proof. destruct Rt as [????? []%reflIdPropEq] ; split; econstructor; tea; eqrefl. Qed.

(*
  Definition reflLRTmEq@{h i j k l} {l Γ A} (lr : [ LogRel@{i j k l} l | Γ ||- A ] ) :
    forall t u,
      [ Γ ||-<l> t ≅ u : A | lr ] ->
      [ Γ ||-<l> t ≅ t : A | lr ] × [ Γ ||-<l> u ≅ u : A | lr ].
  Proof.
    pattern l, Γ, A, lr; eapply LR_rect_TyUr; clear l Γ A lr; intros l Γ A.
    - intros h t u [? ? ? Rt Ru Rtu%TyEqRecFwd]; cbn in *.
      pose proof (Rt' := reflLRTyEq@{h i k j} (RedTyRecFwd@{h i j k} _ Rt)).
      pose proof (Ru' := reflLRTyEq@{h i k j} (RedTyRecFwd@{h i j k} _ Ru)).
      split; unshelve econstructor; tea.
      1,3: eqrefl.
      all: now eapply TyEqRecFwd.
    - intros [] t u [].
      split; econstructor ; cbn in *; tea; eqrefl.
    - intros ??? t u [].
      split; unshelve econstructor ; cbn in *; tea; try eqrefl.
      all: apply PiRedTmEq.app.
    - intros; now apply reflNatRedTmEq.
    - intros; now apply reflEmptyRedTmEq.
    - intros ? ihdom ihcod t u [??? eqfst eqsnd].
      split; unshelve econstructor ; cbn in *; tea; try eqrefl.
      all: intros Δ ρ h; pose proof (ihdom Δ ρ h _ _ (eqfst _ _ _)) as [hL hR]; tea.
      (* Problem of irrelevance of the relation *)
      1,2: admit.
    - intros; now eapply reflIdRedTmEq.
  Admitted.
  (* Qed. *)

  (* Deprecated *)
  Corollary LRTmEqRefl@{h i j k l} {l Γ A eqTy eqTm} (lr : LogRel@{i j k l} l Γ A eqTy eqTm) :
    forall t u, eqTm t u -> eqTm t t × eqTm u u.
  Proof.
    pose (R := Build_LRPack Γ A eqTy eqTm).
    pose (Rad := Build_LRAdequate (pack:=R) lr).
    intros t u ?; change ([Rad | _ ||- t ≅ t : _ ] × [Rad | _ ||- u ≅ u : _ ]); now eapply reflLRTmEq.
  Qed.
*)
End Reflexivities.

