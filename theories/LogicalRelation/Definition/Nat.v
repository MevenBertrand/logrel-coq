(** * LogRel.LogicalRelation.Definition.Nat : Definition of the logical relation for nat *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of natural number type *)
Module NatRedTy.

  Record NatRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Set :=
  {
    redL : [Γ |- A :⤳*: tNat] ;
    redR : [Γ |- B :⤳*: tNat]
  }.

  Arguments NatRedTy {_ _ _}.

  Section NatRedTy.
  Context `{ta : tag} `{WfType ta} `{RedType ta}.

  Definition whredL {Γ A B} : NatRedTy Γ A B -> [Γ |- A ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition whredR {Γ A B} : NatRedTy Γ A B -> [Γ |- B ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  End NatRedTy.

End NatRedTy.

Export NatRedTy(NatRedTy, Build_NatRedTy).
Notation "[ Γ ||-Nat A ≅ B ]" := (NatRedTy Γ A B) (at level 0, Γ, A at level 50).

#[program]
Instance WhRedTyNatRedTy `{GenericTypingProperties} {Γ} : WhRedTyRel Γ (NatRedTy Γ) :=
  {|
    whredtyL := fun A B RAB => NatRedTy.whredL RAB ;
    whredtyR := fun A B RAB => NatRedTy.whredR RAB ;
  |}.
Next Obligation. destruct h; gtyping. Qed.


Module NatRedTmEq.
Section NatRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {Γ : context}.

  Inductive NatRedTmEq : term -> term -> Set :=
  | Build_NatRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⤳*: nfL : tNat])
    (redR : [Γ |- u :⤳*: nfR : tNat ])
    (eq : [Γ |- nfL ≅ nfR : tNat])
    (prop : NatPropEq nfL nfR) : NatRedTmEq t u

  with NatPropEq : term -> term -> Set :=
  | zeroReq :
    NatPropEq tZero tZero
  | succReq {n n'} :
    NatRedTmEq n n' ->
    NatPropEq (tSucc n) (tSucc n')
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tNat] -> NatPropEq ne ne'.

  Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Definition whnfL {t u} : NatPropEq t u -> whnf t.
    Proof.
      intros [].
      1,2: constructor.
      unshelve eapply NeNf.whredL; cycle 3; tea.
    Qed.

    Definition whnfR {t u} : NatPropEq t u -> whnf u.
    Proof.
      intros [].
      1,2: constructor.
      unshelve eapply NeNf.whredR; cycle 3; tea.
    Qed.

    Definition whredL {t u} : NatRedTmEq t u -> [Γ |- t ↘ tNat].
    Proof.
      intros []; econstructor; tea; now eapply whnfL.
    Defined.

    Definition whredR {t u} : NatRedTmEq t u -> [Γ |- u ↘ tNat].
    Proof.
      intros []; econstructor; tea; now eapply whnfR.
    Defined.

  End Def.


Scheme NatRedTmEq_mut_rect := Induction for NatRedTmEq Sort Type with
    NatPropEq_mut_rect := Induction for NatPropEq Sort Type.

Combined Scheme _NatRedInduction from
  NatRedTmEq_mut_rect,
  NatPropEq_mut_rect.

Combined Scheme _NatRedEqInduction from
  NatRedTmEq_mut_rect,
  NatPropEq_mut_rect.

Let _NatRedEqInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _NatRedEqInduction);
      let ind_ty := type of ind in
      exact ind_ty).

Let NatRedEqInductionType :=
  ltac: (let ind := eval cbv delta [_NatRedEqInductionType] zeta
    in _NatRedEqInductionType in
    let ind' := polymorphise ind in
  exact ind').

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
Lemma NatRedEqInduction : NatRedEqInductionType.
Proof.
  intros PRedEq PPropEq **; split; now apply (_NatRedEqInduction PRedEq PPropEq).
Defined.

End NatRedTmEq.
Arguments NatRedTmEq {_ _ _ _ _}.
Arguments NatPropEq {_ _ _ _ _}.
End NatRedTmEq.

Export NatRedTmEq(NatRedTmEq,Build_NatRedTmEq, NatPropEq, NatRedEqInduction).

Notation "[ Γ ||-Nat t ≅ u :Nat]" := (@NatRedTmEq _ _ _ _ _ Γ t u).  (* (at level 0, Γ, t, u, A, RA at level 50). *)

#[program]
Instance NatRedTmEqWhRed `{GenericTypingProperties} {Γ} : WhRedTmRel Γ tNat (NatRedTmEq Γ) :=
  {| whredtmL := fun t u Rtu => NatRedTmEq.whredL Rtu ;
    whredtmR := fun t u Rtu => NatRedTmEq.whredR Rtu |}.
Next Obligation.
  now destruct h.
Qed.