(** * LogRel.Fundamental: declarative typing implies the logical relation for any generic instance. *)
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Weakening Neutral Induction NormalRed.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion Reflexivity SingleSubst Escape.
From LogRel.Validity.Introductions Require Import Application Universe Pi Lambda Var Nat Empty SimpleArr Sigma Id.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Primitive Projection Parameters.

(** ** Definitions *)

(** These records bundle together all the validity data: they do not only say that the
relevant relation holds, but also that all its boundaries hold as well. For instance,
FundTm tells that not only the term is valid at a given type, but also that this type is
itself valid, and that the context is as well. This is needed because the definition of
later validity relations depends on earlier ones, and makes using the fundamental lemma
easier, because we can simply invoke it to get all the validity properties we need. *)

Definition FundCon `{GenericTypingProperties}
  (Γ : context) : Type := [||-v Γ ].

Module FundTy.
  Record FundTy `{GenericTypingProperties} {Γ : context} {A : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ]
  }.

  Arguments FundTy {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTy.

Export FundTy(FundTy,Build_FundTy).

Module FundTyEq.
  Record FundTyEq `{GenericTypingProperties}
    {Γ : context} {A B : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    VB : [ Γ ||-v< one > B | VΓ ];
    VAB : [ Γ ||-v< one > A ≅ B | VΓ | VA ]
  }.
  Arguments FundTyEq {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTyEq.

Export FundTyEq(FundTyEq,Build_FundTyEq).

Module FundTm.
  Record FundTm `{GenericTypingProperties}
    {Γ : context} {A t : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    Vt : [ Γ ||-v< one > t : A | VΓ | VA ];
  }.
  Arguments FundTm {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTm.

Export FundTm(FundTm,Build_FundTm).

Module FundTmEq.
  Record FundTmEq `{GenericTypingProperties}
    {Γ : context} {A t u : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    Vtu : [ Γ ||-v< one > t ≅ u : A | VΓ | VA ];
  }.
  Arguments FundTmEq {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTmEq.

Export FundTmEq(FundTmEq,Build_FundTmEq).

Module FundSubst.
  Record FundSubst `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ] ;
  }.
  Arguments FundSubst {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundSubst.

Export FundSubst(FundSubst,Build_FundSubst).

Module FundSubstConv.
  Record FundSubstConv `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ σ' : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Veq : [VΔ | Γ ||-v σ ≅ σ' : Δ | wfΓ ] ;
  }.
  Arguments FundSubstConv {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundSubstConv.

Export FundSubstConv(FundSubstConv,Build_FundSubstConv).

(** ** The main proof *)

(** Each cases of the fundamental lemma is proven separately, and the final proof simply
brings them all together. *)

Section Fundamental.
  (** We need to have in scope both the declarative instance and a generic one, which we use
  for the logical relation. *)
  Context `{GenericTypingProperties}.
  Import DeclarativeTypingData.

  Lemma FundConNil : FundCon ε.
  Proof.
  unshelve econstructor.
  + unshelve econstructor; intros; exact unit.
  + constructor.
  Qed.

  Lemma FundConCons (Γ : context) (A : term)
  (fΓ : FundCon Γ) (fA : FundTy Γ A) : FundCon (Γ,, A).
  Proof.
    destruct fA as [ VΓ VA ].
    eapply validSnoc. exact VA.
  Qed.

  Lemma FundTyU (Γ : context) (fΓ : FundCon Γ) : FundTy Γ U.
  Proof.
    now unshelve (econstructor; eapply UValid).
  Qed.

  Lemma FundTyPi (Γ : context) (F G : term)
    (fF : FundTy Γ F) (fG : FundTy (Γ,, F) G)
    : FundTy Γ (tProd F G).
  Proof.
    destruct fF as [ VΓ VF ]. destruct fG as [ VΓF VG ].
    econstructor.
    unshelve eapply (PiValid VΓ).
    - assumption.
    - now eapply irrelevanceTy.
  Qed.

  Lemma FundTyUniv (Γ : context) (A : term)
    (fA : FundTm Γ U A)
    : FundTy Γ A.
  Proof.
    destruct fA as [ VΓ VU RA]. econstructor.
    now eapply univValid.
  Qed.

  Lemma FundTmVar : forall (Γ : context) (n : nat) decl,
    FundCon Γ ->
    in_ctx Γ n decl -> FundTm Γ decl (tRel n).
  Proof.
    intros Γ n d FΓ hin.
    unshelve econstructor; tea.
    + eapply in_ctx_valid in hin as []; now eapply embValidTyOne.
    + now eapply varnValid.
  Qed.

  Lemma FundTmProd : forall (Γ : context) (A B : term),
    FundTm Γ U A ->
    FundTm (Γ,, A) U B -> FundTm Γ U (tProd A B).
  Proof.
    intros * [] []; econstructor.
    eapply PiValidU; irrValid.
    Unshelve.
    3: eapply UValid.
    2: eapply univValid.
    all:tea.
  Qed.

  Lemma FundTmLambda : forall (Γ : context) (A B t : term),
    FundTy Γ A ->
    FundTm (Γ,, A) B t -> FundTm Γ (tProd A B) (tLambda A t).
  Proof.
    intros * [] []; econstructor.
    eapply lamValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmApp : forall (Γ : context) (f a A B : term),
    FundTm Γ (tProd A B) f ->
    FundTm Γ A a -> FundTm Γ B[a..] (tApp f a).
  Proof.
    intros * [] []; econstructor.
    now eapply appValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmConv : forall (Γ : context) (t A B : term),
    FundTm Γ A t ->
    FundTyEq Γ A B -> FundTm Γ B t.
  Proof.
    intros * [] []; econstructor.
    eapply conv; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTyEqPiCong : forall (Γ : context) (A B C D : term),
    FundTy Γ A ->
    FundTyEq Γ A B ->
    FundTyEq (Γ,, A) C D -> FundTyEq Γ (tProd A C) (tProd B D).
  Proof.
    intros * [] [] []; econstructor.
    - eapply PiValid. eapply irrelevanceLift; tea; irrValid.
    - eapply PiCong. 1: eapply irrelevanceLift; tea.
      all: irrValid.
    Unshelve. all: tea; irrValid.
  Qed.

  Lemma FundTyEqRefl : forall (Γ : context) (A : term),
    FundTy Γ A -> FundTyEq Γ A A.
  Proof.
    intros * []; unshelve econstructor; tea; now eapply reflValidTy.
  Qed.

  Lemma FundTyEqSym : forall (Γ : context) (A B : term),
    FundTyEq Γ A B -> FundTyEq Γ B A.
  Proof.
    intros * [];  unshelve econstructor; tea.
    now eapply symValidTyEq.
  Qed.

  Lemma FundTyEqTrans : forall (Γ : context) (A B C : term),
    FundTyEq Γ A B ->
    FundTyEq Γ B C ->
    FundTyEq Γ A C.
  Proof.
    intros * [] []; unshelve econstructor; tea. 1:irrValid.
    eapply transValidTyEq; irrValid.
    Unshelve. 2:tea.
  Qed.

  Lemma FundTyEqUniv : forall (Γ : context) (A B : term),
    FundTmEq Γ U A B -> FundTyEq Γ A B.
  Proof.
    intros * [?? VAB].
    pose proof (lreflValidTm _ VAB).
    pose proof (ureflValidTm VAB).
    unshelve econstructor; tea.
    1,2: now eapply univValid.
    now eapply univEqValid.
  Qed.

  Lemma FundTmEqBRed : forall (Γ : context) (a t A B : term),
    FundTy Γ A ->
    FundTm (Γ,, A) B t ->
    FundTm Γ A a -> FundTmEq Γ B[a..] (tApp (tLambda A t) a) t[a..].
  Proof.
    intros * [] [] []; econstructor.
    - unshelve epose (betaValid VA _ _ _). 2,5-7:irrValid.
      Unshelve. 1:tea. eapply substS; tea; irrValid.
  Qed.

  Lemma FundTmEqPiCong : forall (Γ : context) (A B C D : term),
    FundTm Γ U A ->
    FundTmEq Γ U A B ->
    FundTmEq (Γ,, A) U C D ->
    FundTmEq Γ U (tProd A C) (tProd B D).
  Proof.
    intros * [] [] [].
    assert (VA' : [Γ ||-v<one> A | VΓ]) by now eapply univValid.
    assert (VAB : [Γ ||-v<one> A ≅ B | VΓ | VA']) by (eapply univEqValid; irrValid).
    pose proof (ureflValidTy VAB).
    opector; tea.
    - eapply UValid.
    - unshelve epose (PiCongTm _ _ _ _ _ _ _ _ _ _ _).
      17: irrValid.
      2: tea.
      2,3,8: eapply irrelevanceTmEq; tea; first [now eapply lreflValidTm| now eapply ureflValidTm].
      all: try (irrValid + eapply irrelevanceTmEq ;now eapply ureflValidTm).
      + eapply UValid.
      + eapply irrelevanceTmLift; tea; now eapply irrelevanceTmEq, ureflValidTm.
      Unshelve.
      all: try irrValid.
  Qed.

  Lemma FundTmEqAppCong : forall (Γ : context) (a b f g A B : term),
    FundTmEq Γ (tProd A B) f g ->
    FundTmEq Γ A a b ->
    FundTmEq Γ B[a..] (tApp f a) (tApp g b).
  Proof.
    intros * [] []; econstructor.
    eapply appcongValid; first [irrValid | now eapply ureflValidTm].
    Unshelve. 1: irrValid. now eapply lreflValidTm.
  Qed.

  Lemma FundTmEqLambdaCong : forall (Γ : context) (t u A A' A'' B : term),
    FundTy Γ A ->
    FundTyEq Γ A A' ->
    FundTyEq Γ A A'' ->
    FundTmEq (Γ,, A) B t u -> FundTmEq Γ (tProd A B) (tLambda A' t) (tLambda A'' u).
  Proof.
    intros * [VΓ] [? ? VA'] [? ? VA''] [].
    econstructor.
    eapply conv.
    2:{ eapply lamCongValid; tea.
      + unshelve (eapply transValidTyEq; tea; eapply symValidTyEq); try irrValid.
      + now eapply convCtx1.
      + eapply convEqCtx1; tea; now eapply reflValidTy.
      + now eapply convTmEqCtx1.
    }
    unshelve (eapply PiCong; [|eapply symValidTyEq|eapply reflValidTy]; irrValid); try irrValid.
    Unshelve.
    5: tea.
    3: now eapply convCtx1.
    2: irrValid.
    unshelve eapply PiValid; irrValid.
  Qed.

  Lemma FundTmEqFunEta : forall (Γ : context) (f A B : term),
    FundTm Γ (tProd A B) f -> FundTmEq Γ (tProd A B) (tLambda A (tApp f⟨↑⟩ (tRel 0))) f.
  Proof.
  intros * [VΓ VΠ Vf]; econstructor.
  eapply etaValid; irrValid.
  Unshelve.
  + tea.
  + now eapply PiValidDom.
  + now eapply PiValidCod.
  Qed.

  (* Lemma FundTmEqFunExt : forall (Γ : context) (f g A B : term),
    FundTy Γ A ->
    FundTm Γ (tProd A B) f ->
    FundTm Γ (tProd A B) g ->
    FundTmEq (Γ,, A) B (tApp (f⟨↑⟩) (tRel 0)) (tApp (g⟨↑⟩) (tRel 0)) ->
    FundTmEq Γ (tProd A B) f g.
  Proof.
    intros * [] [VΓ0 VA0] [] [].
    assert [Γ ||-v< one > g : tProd A B | VΓ0 | VA0].
    1:{
      eapply conv.
      2: irrValid.
      eapply symValidTyEq. eapply PiCong.
      eapply irrelevanceLift.
      1,3,4: eapply reflValidTy.
      irrValid.
    }
    econstructor.
    3: eapply etaeqValid.
    5: do 2 rewrite wk1_ren_on.
    Unshelve. all: irrValid.
  Qed. *)

  Lemma FundTmEqRefl : forall (Γ : context) (t A : term),
    FundTm Γ A t ->
    FundTmEq Γ A t t.
  Proof.
    intros * []; econstructor; tea; now eapply reflValidTm.
  Qed.

  Lemma FundTmEqSym : forall (Γ : context) (t t' A : term),
    FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t.
  Proof.
    intros * []; econstructor; tea; now eapply symValidTmEq.
  Qed.

  Lemma FundTmEqTrans : forall (Γ : context) (t t' t'' A : term),
    FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t'' ->
    FundTmEq Γ A t t''.
  Proof.
    intros * [] []; econstructor; tea.
    eapply transValidTmEq; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTmEqConv : forall (Γ : context) (t t' A B : term),
    FundTmEq Γ A t t' ->
    FundTyEq Γ A B ->
    FundTmEq Γ B t t'.
  Proof.
    intros * [] []; econstructor.
    eapply conv; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyNat : forall Γ : context, FundCon Γ -> FundTy Γ tNat.
  Proof.
    intros ??; unshelve econstructor; tea;  eapply natValid.
  Qed.

  Lemma FundTmNat : forall Γ : context, FundCon Γ -> FundTm Γ U tNat.
  Proof.
    intros ??; unshelve econstructor; tea.
    2: eapply natTermValid.
  Qed.

  Lemma FundTmZero : forall Γ : context, FundCon Γ -> FundTm Γ tNat tZero.
  Proof.
    intros; unshelve econstructor; tea.
    2:eapply zeroValid.
  Qed.

  Lemma FundTmSucc : forall (Γ : context) (n : term),
    FundTm Γ tNat n -> FundTm Γ tNat (tSucc n).
  Proof.
    intros * []; unshelve econstructor; tea.
    eapply irrelevanceTm; eapply succValid; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTmNatElim : forall (Γ : context) (P hz hs n : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTm Γ tNat n -> FundTm Γ P[n..] (tNatElim P hz hs n).
  Proof.
    intros * [] [] [] []; unshelve econstructor; tea.
    2: eapply natElimValid; irrValid.
    Unshelve.
    2,3: irrValid.
  Qed.

  Lemma FundTyEmpty : forall Γ : context, FundCon Γ -> FundTy Γ tEmpty.
  Proof.
    intros ??; unshelve econstructor; tea;  eapply emptyValid.
  Qed.

  Lemma FundTmEmpty : forall Γ : context, FundCon Γ -> FundTm Γ U tEmpty.
  Proof.
    intros ??; unshelve econstructor; tea.
    2: eapply emptyTermValid.
  Qed.

  Lemma FundTmEmptyElim : forall (Γ : context) (P n : term),
    FundTy (Γ,, tEmpty) P ->
    FundTm Γ tEmpty n -> FundTm Γ P[n..] (tEmptyElim P n).
  Proof.
    intros * [] []; unshelve econstructor; tea.
    2: eapply emptyElimValid; irrValid.
    Unshelve. 2,3: irrValid.
  Qed.

  Lemma FundTmEqSuccCong : forall (Γ : context) (n n' : term),
    FundTmEq Γ tNat n n' -> FundTmEq Γ tNat (tSucc n) (tSucc n').
  Proof.
    intros * []; unshelve econstructor; tea.
    eapply irrelevanceTmEq; eapply succcongValid; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTmEqNatElimCong : forall (Γ : context)
      (P P' hz hz' hs hs' n n' : term),
    FundTyEq (Γ,, tNat) P P' ->
    FundTmEq Γ P[tZero..] hz hz' ->
    FundTmEq Γ (elimSuccHypTy P) hs hs' ->
    FundTmEq Γ tNat n n' ->
    FundTmEq Γ P[n..] (tNatElim P hz hs n) (tNatElim P' hz' hs' n').
  Proof.
    intros * [? VP0 VP0'] [VΓ0] [] []; unshelve econstructor.
    3:eapply natElimCongValid; try irrValid.
    tea.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqNatElimZero : forall (Γ : context) (P hz hs : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTmEq Γ P[tZero..] (tNatElim P hz hs tZero) hz.
  Proof.
    intros * [] [] []; unshelve econstructor; tea.
    2: eapply natElimZeroValid; try irrValid.
    now eapply reflValidTy.
    Unshelve. irrValid.
  Qed.

  Lemma FundTmEqNatElimSucc : forall (Γ : context) (P hz hs n : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTm Γ tNat n ->
    FundTmEq Γ P[(tSucc n)..] (tNatElim P hz hs (tSucc n))
      (tApp (tApp hs n) (tNatElim P hz hs n)).
  Proof.
    intros * [] [] [] []; unshelve econstructor; tea.
    2: eapply natElimSuccValid; try irrValid.
    now eapply reflValidTy.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqEmptyElimCong : forall (Γ : context)
      (P P' n n' : term),
    FundTyEq (Γ,, tEmpty) P P' ->
    FundTmEq Γ tEmpty n n' ->
    FundTmEq Γ P[n..] (tEmptyElim P n) (tEmptyElim P' n').
  Proof.
    intros * [? VP0 VP0'] [VΓ0]; unshelve econstructor; tea.
    2: eapply emptyElimCongValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTySig : forall (Γ : context) (A B : term),
  FundTy Γ A -> FundTy (Γ,, A) B -> FundTy Γ (tSig A B).
  Proof.
    intros * [] []; unshelve econstructor; tea.
    unshelve eapply SigValid; tea; irrValid.
  Qed.

  Lemma FundTmSig : forall (Γ : context) (A B : term),
    FundTm Γ U A ->
    FundTm (Γ,, A) U B -> FundTm Γ U (tSig A B).
  Proof.
    intros * [] []; unshelve econstructor; tea.
    unshelve epose (SigCongValidU (F:=A) (G:=B) _ _ ).
    6,7,8: irrValid.
    + tea.
    + now eapply univValid.
    + irrValid.
  Qed.

  Lemma FundTmPair : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b -> FundTm Γ (tSig A B) (tPair A B a b).
  Proof.
    intros * [] [] [] []; unshelve econstructor.
    3: unshelve eapply pairValid; irrValid.
    tea.
  Qed.

  Lemma FundTmFst : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTm Γ A (tFst p).
  Proof.
    intros * []; unshelve econstructor.
    3: unshelve eapply fstValid.
    5: irrValid.
    2: now eapply domSigValid.
    now eapply codSigValid.
  Qed.

  Lemma FundTmSnd : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTm Γ B[(tFst p)..] (tSnd p).
  Proof.
    intros * []; unshelve econstructor.
    3: unshelve eapply sndValid.
    5: irrValid.
    2: now eapply domSigValid.
    now eapply codSigValid.
  Qed.

  Lemma FundTyEqSigCong : forall (Γ : context) (A B C D : term),
    FundTy Γ A ->
    FundTyEq Γ A B ->
    FundTyEq (Γ,, A) C D -> FundTyEq Γ (tSig A C) (tSig B D).
  Proof.
    intros * [] [] [].
    unshelve econstructor.
    4: eapply SigCong; tea; try irrValid.
    2: eapply irrelevanceLift; irrValid.
    eapply SigValid; eapply irrelevanceLift; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqSigCong :forall (Γ : context) (A A' B B' : term),
    FundTm Γ U A ->
    FundTmEq Γ U A A' ->
    FundTmEq (Γ,, A) U B B' -> FundTmEq Γ U (tSig A B) (tSig A' B').
  Proof.
    intros * [] [] []; unshelve econstructor.
    3: eapply SigCongValidU ; tea; try irrValid.
    1: tea.
    Unshelve.
    + unshelve (eapply univValid; irrValid); irrValid.
    + irrValid.
  Qed.

  Lemma FundTmEqPairCong : forall (Γ : context) (A A' A'' B B' B'' a a' b b' : term),
    FundTy Γ A ->
    FundTyEq Γ A A' ->
    FundTyEq Γ A A'' ->
    FundTyEq (Γ,, A) B B' ->
    FundTyEq (Γ,, A) B B'' ->
    FundTmEq Γ A a a' ->
    FundTmEq Γ B[a..] b b' -> FundTmEq Γ (tSig A B) (tPair A' B' a b) (tPair A'' B'' a' b').
  Proof.
    intros * [VΓ VA] [?? VA'] [] [] [] [] [].
    assert [Γ ,, A' ||-v<one> B' | validSnoc _ VA'].
    1:{ eapply convCtx1; tea. }
    econstructor.
    eapply conv; cycle 1.
    - eapply pairCongValid.
      + eapply transValidTyEq; tea; eapply symValidTyEq; irrValid.
      + eapply convEqCtx1; tea; eapply transValidTyEq; tea.
        eapply symValidTyEq; irrValid.
      + eapply conv; [eapply substSEq; tea|]; irrValid.
    - eapply symValidTyEq; eapply SigCong; try irrValid.
    Unshelve.
      all: try irrValid.
      + unshelve eapply SigValid; irrValid.
      + unshelve (eapply conv; tea; irrValid); irrValid.
      + eapply lreflValidTm; irrValid.
  Qed.

  Lemma FundTmEqSigEta : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTmEq Γ (tSig A B) (tPair A B (tFst p) (tSnd p)) p.
  Proof.
  intros * [VΓ VΣ Vp]; econstructor.
  eapply sigEtaValid; irrValid.
  Unshelve.
  + tea.
  + now eapply domSigValid.
  + now eapply codSigValid.
  Qed.

  Lemma FundTmEqFstCong : forall (Γ : context) (A B p p' : term),
    FundTmEq Γ (tSig A B) p p' -> FundTmEq Γ A (tFst p) (tFst p').
  Proof.
    intros * []; unshelve econstructor.
    3: eapply fstValid; irrValid.
    2: now eapply domSigValid.
    Unshelve. all: now eapply codSigValid.
  Qed.

  Lemma FundTmEqFstBeta : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b -> FundTmEq Γ A (tFst (tPair A B a b)) a.
  Proof.
    intros * [] [] [] [].
    unshelve econstructor.
    3: eapply pairFstValid; irrValid.
    2: irrValid.
    tea.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqSndCong : forall (Γ : context) (A B p p' : term),
    FundTmEq Γ (tSig A B) p p' -> FundTmEq Γ B[(tFst p)..] (tSnd p) (tSnd p').
  Proof.
    intros * []; unshelve econstructor.
    3: eapply sndValid; irrValid.
    1: tea.
    Unshelve.
      2: now eapply domSigValid.
      1: now eapply codSigValid.
      irrValid.
  Qed.

  Lemma FundTmEqSndBeta : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b ->
    FundTmEq Γ B[(tFst (tPair A B a b))..] (tSnd (tPair A B a b)) b.
  Proof.
    intros * [] [] [] []; unshelve econstructor.
    3: eapply pairSndValid.
    1: tea.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyId : forall (Γ : context) (A x y : term),
    FundTy Γ A -> FundTm Γ A x -> FundTm Γ A y -> FundTy Γ (tId A x y).
  Proof.
    intros * [] [] [].
    unshelve econstructor; tea.
    unshelve eapply IdValid; try irrValid.
  Qed.


  Lemma FundTmId : forall (Γ : context) (A x y : term),
    FundTm Γ U A -> FundTm Γ A x -> FundTm Γ A y -> FundTm Γ U (tId A x y).
  Proof.
      intros * [] [] [].
      unshelve econstructor; tea.
      1: eapply UValid.
      unshelve eapply IdTmValid; cycle 1; try irrValid; tea.
  Qed.

  Lemma FundTmRefl : forall (Γ : context) (A x : term),
    FundTy Γ A -> FundTm Γ A x -> FundTm Γ (tId A x x) (tRefl A x).
  Proof.
    intros * [] []; unshelve econstructor.
    3: now eapply reflValid.
    now eapply IdValid.
  Qed.

  Lemma FundTmIdElim : forall (Γ : context) (A x P hr y e : term),
    FundTy Γ A ->
    FundTm Γ A x ->
    FundTy ((Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) P ->
    FundTm Γ P[tRefl A x .: x..] hr ->
    FundTm Γ A y -> FundTm Γ (tId A x y) e -> FundTm Γ P[e .: y..] (tIdElim A x P hr y e).
  Proof.
    intros * [] [] [] [] [] []; unshelve econstructor.
    3: unshelve eapply IdElimValid; try irrValid.
    2,3: eapply reflValidTy.
    tea.
  Qed.

  Lemma FundTyEqId : forall (Γ : context) (A A' x x' y y' : term),
    FundTyEq Γ A A' ->
    FundTmEq Γ A x x' -> FundTmEq Γ A y y' -> FundTyEq Γ (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] [].
    unshelve econstructor; tea.
    3: eapply IdCongValid; irrValid.
    1,2: eapply IdValid; try irrValid.
    1,2: eapply ureflValidTm, conv; tea; try irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqIdCong : forall (Γ : context) (A A' x x' y y' : term),
    FundTmEq Γ U A A' ->
    FundTmEq Γ A x x' -> FundTmEq Γ A y y' -> FundTmEq Γ U (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] []; unshelve econstructor.
    3: eapply IdTmCongValid; try irrValid; tea.
    1: tea.
    Unshelve. all: first [eapply UValid| irrValid | tea].
  Qed.

  Lemma FundTmEqReflCong : forall (Γ : context) (A A' x x' : term),
    FundTyEq Γ A A' -> FundTmEq Γ A x x' -> FundTmEq Γ (tId A x x) (tRefl A x) (tRefl A' x').
  Proof.
    intros * [] []; unshelve econstructor.
    3: eapply reflCongValid; tea; irrValid.
    eapply IdValid; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTmEqIdElimCong : forall (Γ : context) (A A' x x' P P' hr hr' y y' e e' : term),
    FundTy Γ A ->
    FundTm Γ A x ->
    FundTyEq Γ A A' ->
    FundTmEq Γ A x x' ->
    FundTyEq ((Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) P P' ->
    FundTmEq Γ P[tRefl A x .: x..] hr hr' ->
    FundTmEq Γ A y y' ->
    FundTmEq Γ (tId A x y) e e' -> FundTmEq Γ P[e .: y..] (tIdElim A x P hr y e) (tIdElim A' x' P' hr' y' e').
  Proof.
    intros * [] [] [] [] [] [] [] [].
    econstructor.
    eapply IdElimValid; tea; irrValid.
    Unshelve.
    3: unshelve (eapply IdValid; irrValid); irrValid.
    all: irrValid.
  Qed.

  Lemma FundTmEqIdElimRefl : forall (Γ : context) (A x P hr y A' z : term),
    FundTy Γ A ->
    FundTm Γ A x ->
    FundTy ((Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A ⟩ (tRel 0)) P ->
    FundTm Γ P[tRefl A x .: x..] hr ->
    FundTm Γ A y ->
    FundTy Γ A' ->
    FundTm Γ A z ->
    FundTyEq Γ A A' ->
    FundTmEq Γ A x y ->
    FundTmEq Γ A x z -> FundTmEq Γ P[tRefl A' z .: y..] (tIdElim A x P hr y (tRefl A' z)) hr.
  Proof.
    intros * [] [] [] [] [] [] [] [] [] [].
    econstructor.
    eapply IdElimReflValid; tea; try irrValid.
    Unshelve. all: try irrValid.
      + unshelve (eapply IdValid; irrValid); irrValid.
      + assert (VId : [Γ ||-v<one> tId A x y | VΓ]) by (unshelve (eapply IdValid; irrValid); irrValid).
        assert [_ ||-v<one> y ≅ z : _ | _ | VA].
        1: eapply transValidTmEq; [eapply symValidTmEq|]; irrValid.
        assert [Γ ||-v<one> tId A x y ≅ tId A' z z | _ | VId ].
        1: eapply IdCongValid; irrValid.
        eapply conv; [|eapply reflValid, ureflValidTm, conv; irrValid].
        eapply symValidTyEq; irrValid.
        Unshelve.
          2: unshelve eapply ureflValidTy.
          all: try irrValid.
  Qed.


Lemma Fundamental : (forall Γ : context, [ |-[ de ] Γ ] -> FundCon (ta := ta) Γ)
    × (forall (Γ : context) (A : term), [Γ |-[ de ] A] -> FundTy (ta := ta) Γ A)
    × (forall (Γ : context) (A t : term), [Γ |-[ de ] t : A] -> FundTm (ta := ta) Γ A t)
    × (forall (Γ : context) (A B : term), [Γ |-[ de ] A ≅ B] -> FundTyEq (ta := ta) Γ A B)
    × (forall (Γ : context) (A t u : term), [Γ |-[ de ] t ≅ u : A] -> FundTmEq (ta := ta) Γ A t u).
  Proof.
  apply WfDeclInduction.
  + intros; now apply FundConNil.
  + intros; now apply FundConCons.
  + intros; now apply FundTyU.
  + intros; now apply FundTyPi.
  + intros; now apply FundTyNat.
  + intros; now apply FundTyEmpty.
  + intros; now apply FundTySig.
  + intros; now apply FundTyId.
  + intros; now apply FundTyUniv.
  + intros; now apply FundTmVar.
  + intros; now apply FundTmProd.
  + intros; now apply FundTmLambda.
  + intros; now eapply FundTmApp.
  + intros; now apply FundTmNat.
  + intros; now apply FundTmZero.
  + intros; now apply FundTmSucc.
  + intros; now apply FundTmNatElim.
  + intros; now apply FundTmEmpty.
  + intros; now apply FundTmEmptyElim.
  + intros; now apply FundTmSig.
  + intros; now apply FundTmPair.
  + intros; now eapply FundTmFst.
  + intros; now eapply FundTmSnd.
  + intros; now eapply FundTmId.
  + intros; now eapply FundTmRefl.
  + intros; now eapply FundTmIdElim.
  + intros; now eapply FundTmConv.
  + intros; now apply FundTyEqPiCong.
  + intros; now apply FundTyEqSigCong.
  + intros; now eapply FundTyEqId.
  + intros; now apply FundTyEqRefl.
  + intros; now apply FundTyEqUniv.
  + intros; now apply FundTyEqSym.
  + intros; now eapply FundTyEqTrans.
  + intros; now apply FundTmEqBRed.
  + intros; now apply FundTmEqPiCong.
  + intros; now eapply FundTmEqAppCong.
  + intros; now apply FundTmEqLambdaCong.
  + intros; now apply FundTmEqFunEta.
  + intros; now apply FundTmEqSuccCong.
  + intros; now apply FundTmEqNatElimCong.
  + intros; now apply FundTmEqNatElimZero.
  + intros; now apply FundTmEqNatElimSucc.
  + intros; now apply FundTmEqEmptyElimCong.
  + intros; now apply FundTmEqSigCong.
  + intros; now apply FundTmEqPairCong.
  + intros; now apply FundTmEqSigEta.
  + intros; now eapply FundTmEqFstCong.
  + intros; now apply FundTmEqFstBeta.
  + intros; now eapply FundTmEqSndCong.
  + intros; now apply FundTmEqSndBeta.
  + intros; now apply FundTmEqIdCong.
  + intros; now apply FundTmEqReflCong.
  + intros; now apply FundTmEqIdElimCong.
  + intros; now apply FundTmEqIdElimRefl.
  + intros; now apply FundTmEqRefl.
  + intros; now eapply FundTmEqConv.
  + intros; now apply FundTmEqSym.
  + intros; now eapply FundTmEqTrans.
  Qed.

(** ** Well-typed substitutions are also valid *)

  Corollary Fundamental_subst Γ Δ σ (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ : Δ] ->
    FundSubst Γ Δ wfΓ σ.
  Proof.
    intros HΔ.
    induction 1 as [|σ Δ A Hσ IH Hσ0].
    - exists validEmpty.
      now constructor.
    - inversion HΔ as [|?? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [?? Hσ0].
      cbn in *.
      eapply reducibleTmEq in Hσ0.
      eapply Fundamental in HA as [].
      unshelve econstructor.
      1: now eapply validSnoc.
      unshelve econstructor.
      + now eapply irrelevanceSubst.
      + cbn; irrelevance0.
        2: eassumption.
        reflexivity.
  Qed.

  Corollary Fundamental_subst_conv Γ Δ σ σ' (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ ≅ σ' : Δ] ->
    FundSubstConv Γ Δ wfΓ σ σ'.
  Proof.
    intros HΔ.
    induction 1 as [|σ τ Δ A Hσ IH Hσ0].
    - unshelve econstructor.
      1: eapply validEmpty.
      all: now econstructor.
    - inversion HΔ as [|?? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [?? Ηστ] ; cbn in *.
      eapply Fundamental in HA as [? HA].
      unshelve econstructor.
      + now eapply validSnoc.
      + unshelve econstructor.
        1: now irrValid.
        cbn.
        irrelevanceRefl.
        now eapply reducibleTmEq.
  Qed.

End Fundamental.
