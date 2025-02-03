(** * LogRel.LogicalRelation.ShapeView: relating reducibility witnesses of reducibly convertible types.*)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section ShapeViews.
  Context `{GenericTypingProperties}.

(** ** Definition *)

(** A shape view is inhabited exactly on the diagonal, ie when the two types are reducible
  in the same way. *)

  Definition ShapeView@{i j k l i' j' k' l'} Γ
    A {lA A'} B {lB B'} (RA : [LogRel@{i j k l} lA | Γ ||- A ≅ A']) (RB : [LogRel@{i' j' k' l'} lB | Γ ||- B ≅ B']) : Set :=
    match RA.(LRAd.adequate), RB.(LRAd.adequate) with
      | LRU _ _, LRU _ _ => True
      | LRne _ _, LRne _ _ => True
      | LRPi _ _ _, LRPi _ _ _ => True
      | LRNat _ _, LRNat _ _ => True
      | LREmpty _ _, LREmpty _ _ => True
      | LRSig _ _ _, LRSig _ _ _ => True
      | LRId _ _ _, LRId _ _ _ => True
      | _, _ => False
    end.

  Arguments ShapeView Γ A {lA A'} B {lB B'} !RA !RB.

  (* Definition ShapeView@{i j k l i' j' k' l'} Γ
    A {lA A' eqtmA} B {lB B' eqtmB}
    (lrA : LogRel@{i j k l} lA Γ A A' eqtmA) (lrB : LogRel@{i' j' k' l'} lB Γ B B' eqtmB) : Set :=
    match lrA, lrB with
      | LRU _ _, LRU _ _ => True
      | LRne _ _, LRne _ _ => True
      | LRPi _ _ _, LRPi _ _ _ => True
      | LRNat _ _, LRNat _ _ => True
      | LREmpty _ _, LREmpty _ _ => True
      | LRSig _ _ _, LRSig _ _ _ => True
      | LRId _ _ _, LRId _ _ _ => True
      | _, _ => False
    end. *)

  (* Arguments ShapeView Γ A {lA eqTyA redTyA} B {lB eqTyB redTyB}
  !lrA !lrB. *)

(** ** The main property *)

(** We show that two reducibly convertible types must have the same shape view. Said otherwise,
if two reducible types are reducibly convertible, then they must be reducible in the same way.
This lets us relate different reducibility proofs when we have multiple such proofs, typically
when showing symmetry or transitivity of the logical relation. *)

  Definition abstract_let {A B} (a : A) : (forall x: A, x = a -> B)  -> let x := a in B := fun h => h a eq_refl.

  Ltac revert_let t := let x := fresh "x" in pose (x := t); revert x; simple refine (abstract_let _ _). (*; apply (abstract_let t). *)

  From Equations Require Import Equations.
  Record nfTy := mkNfTy { ty : term ; isty : isType ty }.
  Derive NoConfusion for nfTy.
  Definition toNfTy {Γ A} (rA : [Γ |- A ↘ ]) := mkNfTy rA.(tyred_whnf) rA.(tyred_whnf_isType).

  Lemma whredty_det' {Γ A} (rA rA' : [Γ |- A ↘ ]) : toNfTy rA = toNfTy rA'.
  Proof.
    unfold toNfTy; pose proof (e := whredty_det _ _ rA rA'); destruct rA, rA'; cbn in *; subst.
    f_equal; eapply isType_uniq.
  Qed.

  Lemma ShapeViewConv@{i j k l i' j' k' l' i'' j'' k'' l''} {Γ A lA A' B lB B' l}
    (RA : [LogRel@{i j k l} lA | Γ ||- A ≅ A']) (RB : [LogRel@{i' j' k' l'} lB | Γ ||- B ≅ B']) :
    [LogRel@{ i'' j'' k'' l''} l | Γ ||- A ≅ B] -> ShapeView@{i j k l i' j' k' l'} Γ A B RA RB.
  Proof.
    intros RAB.
    set (rA := whredL RAB); set (rA' := whredL RA); set (rB := whredR RAB); set (rB' := whredL RB).
    generalize (whredty_det' rA rA') (whredty_det' rB rB'); subst rA rA' rB rB'.
    unfold ShapeView; destruct RA as [? adA], RB as [? adB], RAB as [? adAB]; cbn; destruct adA, adB, adAB; cbn;
    intros eqA eqB ; try first [exact I| discriminate eqA| discriminate eqB].
  Qed.

(*
  Lemma red_whnf@{i j k l} {Γ A lA eqTyA eqTmA}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA eqTmA) :
    ∑ nf, [Γ |- A :⤳*: nf] × whnf nf.
  Proof.
    pattern lA, Γ, A, eqTyA, eqTmA, lrA; eapply LR_rect; intros ??[].
    all: eexists; split; tea; constructor; tea.
    now eapply convneu_whne.
  Defined.

  Lemma eqTy_red_whnf@{i j k l} {Γ A lA eqTyA eqTmA B}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA eqTmA) :
    eqTyA B -> ∑ nf, [Γ |- B :⤳*: nf] × whnf nf.
  Proof.
    pattern lA, Γ, A, eqTyA, eqTmA, lrA.
    eapply LR_rect_LogRelRec@{i j k l k}; intros ??? [].
    3,6,7: intros ??.
    all: intros []; eexists; split; tea; constructor; tea.
    eapply convneu_whne; now symmetry.
  Defined.

  Lemma ShapeViewConv@{i j k l i' j' k' l'} {Γ A lA eqTyA eqTmA B lB eqTyB eqTmB}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA eqTmA) (lrB : LogRel@{i' j' k' l'} lB Γ B eqTyB eqTmB) :
    eqTyA B ->
    ShapeView@{i j k l i' j' k' l'} Γ A B lrA lrB.
  Proof.
    intros eqAB.
    pose (x := eqTy_red_whnf lrA eqAB).
    pose (y:= red_whnf lrB).
    pose proof (h := redtywf_det (snd x.π2) (snd y.π2) (fst x.π2) (fst y.π2)).
    revert eqAB x y h.
    destruct lrA; destruct lrB; intros []; cbn; try easy; try discriminate.
    all: try now (intros e; destruct neA as [? ? ne]; subst; apply convneu_whne in ne; inversion ne).
    all: try now (intros e; subst; symmetry in eq; apply convneu_whne in eq; inversion eq).
  Qed. *)

(** ** More properties *)
(* KM: looks like it is not used anywhere anymore *)

(*
  Corollary ShapeViewRefl@{i j k l i' j' k' l'} {Γ A lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel@{i' j' k' l'} lA' Γ A eqTyA' redTmA' eqTmA') :
    ShapeView@{i j k l i' j' k' l'} Γ A A lrA lrA'.
  Proof.
    now eapply ShapeViewConv, LRTyEqRefl.
  Qed.

  Definition ShapeView3 Γ
    A {lA eqTyA redTmA redTyA}
    B {lB eqTyB redTmB redTyB}
    C {lC eqTyC redTmC redTyC}
    (lrA : LogRel lA Γ A eqTyA redTmA redTyA)
    (lrB : LogRel lB Γ B eqTyB redTmB redTyB)
    (lrC : LogRel lC Γ C eqTyC redTmC redTyC)
    : Set :=
    match lrA, lrB, lrC with
      | LRU _ _, LRU _ _, LRU _ _ => True
      | LRne _ _, LRne _ _, LRne _ _ => True
      | LRPi _ _ _, LRPi _ _ _, LRPi _ _ _ => True
      | LRNat _ _, LRNat _ _, LRNat _ _ => True
      | LREmpty _ _, LREmpty _ _, LREmpty _ _ => True
      | LRSig _ _ _, LRSig _ _ _, LRSig _ _ _ => True
      | LRId _ _ _, LRId _ _ _, LRId _ _ _ => True
      | _, _, _ => False
    end.


  Arguments ShapeView3 Γ A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB} C {lC eqTyC redTmC redTyC}
  !lrA !lrB !lrC.

  Lemma combine Γ
    A {lA eqTyA redTmA redTyA}
    B {lB eqTyB redTmB redTyB}
    C {lC eqTyC redTmC redTyC}
    (lrA : LogRel lA Γ A eqTyA redTmA redTyA)
    (lrB : LogRel lB Γ B eqTyB redTmB redTyB)
    (lrC : LogRel lC Γ C eqTyC redTmC redTyC) :
    ShapeView Γ A B lrA lrB -> ShapeView Γ B C lrB lrC -> ShapeView3 Γ A B C lrA lrB lrC.
  Proof.  destruct lrA, lrB, lrC; easy. Qed.
*)
End ShapeViews.
