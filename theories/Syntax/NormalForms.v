(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From Coq Require Import ssrbool.
From Equations Require Import Equations. (* for depelim *)
From LogRel Require Import AutoSubst.Extra Utils.
From LogRel.Syntax Require Import BasicAst Context.

(** ** Weak-head normal forms and neutrals. *)

Inductive whnf : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {A B} : whnf (tProd A B)
  | whnf_tLambda {A t} : whnf (tLambda A t)
  | whnf_tNat : whnf tNat
  | whnf_tZero : whnf tZero
  | whnf_tSucc {n} : whnf (tSucc n)
  | whnf_tEmpty : whnf tEmpty
  | whnf_tSig {A B} : whnf (tSig A B)
  | whnf_tPair {A B a b} : whnf (tPair A B a b)
  | whnf_tId {A x y} : whnf (tId A x y)
  | whnf_tRefl {A x} : whnf (tRefl A x)
  | whnf_whne {n} : whne n -> whnf n
with whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_tFst {p} : whne p -> whne (tFst p)
  | whne_tSnd {p} : whne p -> whne (tSnd p)
  | whne_tIdElim {A x P hr y e} : whne e -> whne (tIdElim A x P hr y e).

#[global] Hint Constructors whne whnf : gen_typing.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
    try solve [inversion H] ; block H
  end; unblock.

Lemma neSort s : whne (tSort s) -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi A B : whne (tProd A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda A t : whne (tLambda A t) -> False.
Proof.
  inversion 1.
Qed.

#[global] Hint Resolve neSort nePi neLambda : gen_typing.

(** ** Restricted classes of normal forms *)

Inductive isType : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType { A B} : isType (tProd A B)
  | NatType : isType tNat
  | EmptyType : isType tEmpty
  | SigType {A B} : isType (tSig A B)
  | IdType {A x y} : isType (tId A x y)
  | NeType {A}  : whne A -> isType A.

Inductive isPosType : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | EmptyPos : isPosType tEmpty
  | IdPos {A x y} : isPosType (tId A x y)
  | NePos {A}  : whne A -> isPosType A.

Inductive isFun : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | NeFun  {f} : whne f -> isFun f.

Inductive isNat : term -> Type :=
  | ZeroNat : isNat tZero
  | SuccNat {t} : isNat (tSucc t)
  | NeNat {n} : whne n -> isNat n.

Inductive isPair : term -> Type :=
  | PairPair {A B a b} : isPair (tPair A B a b)
  | NePair {p} : whne p -> isPair p.

Inductive isId : term -> Type :=
  | ReflId {A a} : isId (tRefl A a)
  | NeId {n} : whne n -> isId n.

Definition isPosType_isType t (i : isPosType t) : isType t.
Proof. destruct i; now constructor. Defined.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf t (i : isType t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isFun_whnf : isFun >-> whnf.

Definition isPair_whnf t (i : isPair t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isPair_whnf : isPair >-> whnf.

Definition isNat_whnf t (i : isNat t) : whnf t :=
  match i with
  | ZeroNat => whnf_tZero
  | SuccNat => whnf_tSucc
  | NeNat n => whnf_whne n
  end.

Definition isId_whnf t (i : isId t) : whnf t :=
  match i with
  | ReflId => whnf_tRefl
  | NeId n => whnf_whne n
  end.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isPair_whnf isId_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat isId : gen_typing.

Equations Derive Signature for isNat.

Lemma isNat_zero (n : isNat tZero) : n = ZeroNat.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.

Lemma isNat_succ t (n : isNat (tSucc t)) : n = SuccNat.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.

Lemma isNat_ne t (n : isNat t) : whne t -> ∑ w, n = NeNat w.
Proof.
  intros w.
  depelim n.
  1-2: now inversion w.
  now eexists.
Qed.

Derive Signature for isId.

Lemma isId_refl A a (n : isId (tRefl A a)) : n = ReflId.
Proof.
  depelim n.
  1: reflexivity.
  inversion w ; cbn ; easy.
Qed.

Lemma isId_ne t (n : isId t) : whne t -> ∑ w, n = NeId w.
Proof.
  intros w.
  dependent inversion n ; subst.
  1: inversion w.
  now eexists.
Qed.

(** ** Canonical forms *)

Inductive isCanonical : term -> Type :=
  | can_tSort {s} : isCanonical (tSort s)
  | can_tProd {A B} : isCanonical (tProd A B)
  | can_tLambda {A t} : isCanonical (tLambda A t)
  | can_tNat : isCanonical tNat
  | can_tZero : isCanonical tZero
  | can_tSucc {n} : isCanonical (tSucc n)
  | can_tEmpty : isCanonical tEmpty
  | can_tSig {A B} : isCanonical (tSig A B)
  | can_tPair {A B a b}: isCanonical (tPair A B a b)
  | can_tId {A x y}: isCanonical (tId A x y)
  | can_tRefl {A x}: isCanonical (tRefl A x).

#[global] Hint Constructors isCanonical : gen_typing.

Lemma can_whne_exclusive t : isCanonical t -> whne t -> False.
Proof.
  intros Hcan Hne.
  inversion Hcan ; subst ; inversion Hne.
Qed.

Lemma whnf_can_whne t : whnf t -> isCanonical t + whne t.
Proof.
  intros [].
  all: try solve [left ; now constructor | now right].
Qed.

Lemma not_can_whne t : whnf t -> ~ isCanonical t -> whne t.
Proof.
  intros []%whnf_can_whne ; eauto.
  now intros [].
Qed.

Lemma not_whne_can t : whnf t -> ~ whne t -> isCanonical t.
Proof.
  intros []%whnf_can_whne ; eauto.
  now intros [].
Qed.

(** ** Normal and neutral forms are stable by renaming *)

Section RenWhnf.

  #[local] Ltac push_renaming :=
  repeat match goal with
  | eq : _ = ?t⟨_⟩ |- _ =>
      destruct t ; cbn in * ; try solve [congruence] ;
      inversion eq ; subst ; clear eq
  end.

  Variable (ρ : nat -> nat).

  Lemma whne_ren t : whne (t⟨ρ⟩) <~> whne t.
  Proof.
    split.
    - remember t⟨ρ⟩ as t'.
      intros Hne.
      induction Hne in t, Heqt' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
    - induction 1 ; cbn.
      all: now econstructor.
  Qed.

  Lemma whnf_ren t : whnf (t⟨ρ⟩) <~> whnf t.
  Proof.
    split.
    - remember t⟨ρ⟩ as t'.
      intros Hnf.
      induction Hnf in t, Heqt' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isType_ren A : isType (A⟨ρ⟩) <~> isType A.
  Proof.
    split.
    - remember A⟨ρ⟩ as A'.
      intros Hty.
      induction Hty in A, HeqA' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isPosType_ren A : isPosType (A⟨ρ⟩) <~> isPosType A.
  Proof.
    split.
    - remember A⟨ρ⟩ as A'.
      intros Hty.
      induction Hty in A, HeqA' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isFun_ren f : isFun (f⟨ρ⟩) <~> isFun f.
  Proof.
    split.
    - remember f⟨ρ⟩ as f'.
      intros Hfun.
      induction Hfun in f, Heqf' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.


  Lemma isPair_ren p : isPair (p⟨ρ⟩) <~> isPair p.
  Proof.
    split.
    - remember p⟨ρ⟩ as p'.
      intros Hpair.
      induction Hpair in p, Heqp' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isId_ren p : isId (p⟨ρ⟩) <~> isId p.
  Proof.
    split.
    - remember p⟨ρ⟩ as p'.
      intros Hid.
      induction Hid in p, Heqp' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isCanonical_ren t : isCanonical (t⟨ρ⟩) <~> isCanonical t.
  Proof.
    split.
    all: destruct t ; cbn ; inversion 1.
    all: now econstructor.
  Qed.

End RenWhnf.

#[global] Hint Resolve whne_ren whnf_ren isType_ren isPosType_ren isFun_ren isId_ren isCanonical_ren : gen_typing.