(** * LogRel.Fundamental: declarative typing implies the logical relation for any generic instance. *)
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity Irrelevance Properties ValidityTactics.
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

  Arguments FundTy {_ _ _ _ _ _ _ _ _ _}.
End FundTy.

Export FundTy(FundTy,Build_FundTy).

Module FundTyEq.
  Record FundTyEq `{GenericTypingProperties}
    {Γ : context} {A B : term}
  : Type := {
    VΓ : [||-v Γ ];
    VAB : [ Γ ||-v< one > A ≅ B | VΓ ]
  }.
  Arguments FundTyEq {_ _ _ _ _ _ _ _ _ _}.
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
  Arguments FundTm {_ _ _ _ _ _ _ _ _ _}.
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
  Arguments FundTmEq {_ _ _ _ _ _ _ _ _ _}.
End FundTmEq.

Export FundTmEq(FundTmEq,Build_FundTmEq).


Module FundSubst.
  Record FundSubst `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ] ;
  }.
  Arguments FundSubst {_ _ _ _ _ _ _ _ _ _}.
End FundSubst.

Export FundSubst(FundSubst,Build_FundSubst).

Module FundSubstConv.
  Record FundSubstConv `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ σ' : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Veq : [VΔ | Γ ||-v σ ≅ σ' : Δ | wfΓ ] ;
  }.
  Arguments FundSubstConv {_ _ _ _ _ _ _ _ _ _}.
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
  Proof. eapply validEmpty. Qed.

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
    unshelve eapply (PiValid VΓ); irrValid.
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
    + pose proof (in_ctx_valid hin FΓ) as (?&?&?).
      now eapply lrefl, embValidTyOne.
    + now eapply varnValid.
  Qed.

  Lemma FundTmProd : forall (Γ : context) (A B : term),
    FundTm Γ U A ->
    FundTm (Γ,, A) U B -> FundTm Γ U (tProd A B).
  Proof.
    intros * [] []; econstructor.
    unshelve eapply PiValidU;
    first [now eapply UValid| now eapply univValid| irrValid | tea].
  Qed.

  Lemma FundTmLambda : forall (Γ : context) (A B t : term),
    FundTy Γ A ->
    FundTm (Γ,, A) B t -> FundTm Γ (tProd A B) (tLambda A t).
  Proof.
    intros * [] []; econstructor.
    unshelve (eapply lamValid; irrValid); irrValid.
    Unshelve. tea.
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
    irrValid.
    Unshelve. tea. irrValid.
  Qed.

  Lemma FundTyEqPiCong : forall (Γ : context) (A B C D : term),
    FundTy Γ A ->
    FundTyEq Γ A B ->
    FundTyEq (Γ,, A) C D -> FundTyEq Γ (tProd A C) (tProd B D).
  Proof.
    intros * [] [] []; econstructor.
    eapply PiValid. irrValid.
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
    irrValid.
  Qed.

  Lemma FundTyEqTrans : forall (Γ : context) (A B C : term),
    FundTyEq Γ A B ->
    FundTyEq Γ B C ->
    FundTyEq Γ A C.
  Proof.
    intros * [] []; unshelve econstructor; tea; irrValid.
  Qed.

  Lemma FundTyEqUniv : forall (Γ : context) (A B : term),
    FundTmEq Γ U A B -> FundTyEq Γ A B.
  Proof.
    intros * [?? VAB].
    unshelve econstructor; tea; now eapply univValid.
  Qed.

  Lemma FundTmEqBRed : forall (Γ : context) (a t A B : term),
    FundTy Γ A ->
    FundTm (Γ,, A) B t ->
    FundTm Γ A a -> FundTmEq Γ B[a..] (tApp (tLambda A t) a) t[a..].
  Proof.
    intros * [] [] []; econstructor.
    eapply betaValid; irrValid.
    Unshelve. all: cycle 2; irrValid.
  Qed.

  Lemma FundTmEqPiCong : forall (Γ : context) (A B C D : term),
    FundTm Γ U A ->
    FundTmEq Γ U A B ->
    FundTmEq (Γ,, A) U C D ->
    FundTmEq Γ U (tProd A C) (tProd B D).
  Proof.
    intros * [] [] [].
    (* assert (VA' : [Γ ||-v<one> A | VΓ]) by now eapply univValid. *)
    assert (VAB : [Γ ||-v<one> A ≅ B | VΓ ]) by now unshelve (eapply univValid; irrValid).
    econstructor. eapply PiValidU; tea; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqAppCong : forall (Γ : context) (a b f g A B : term),
    FundTmEq Γ (tProd A B) f g ->
    FundTmEq Γ A a b ->
    FundTmEq Γ B[a..] (tApp f a) (tApp g b).
  Proof.
    intros * [? VΠ] [?? Vab]; pose (VB := validΠcod VΠ).
    opector; tea.
    1: unshelve (eapply lrefl, substS; tea; irrValid); irrValid.
    unshelve epose proof (appcongValid (a:=a) (b:=b) Vtu _); [irrValid|].
    (* Completeness issue with irrValid... *)
    (* irrValid. *)
    eapply irrValidTm; tea.
  Qed.

  Lemma FundTmEqLambdaCong : forall (Γ : context) (t u A A' A'' B : term),
    FundTy Γ A ->
    FundTyEq Γ A A' ->
    FundTyEq Γ A A'' ->
    FundTmEq (Γ,, A) B t u -> FundTmEq Γ (tProd A B) (tLambda A' t) (tLambda A'' u).
  Proof.
    intros * [VΓ] [? VA'] [? VA''] [].
    assert (VAeq : [_ ||-v<one> A' ≅ A'' | VΓ]) by irrValid.
    pose proof (validSnoc _ VA'); pose proof (validSnoc _ VA'').
    assert (VB : [_ ||-v<one> B | validSnoc VΓ VAeq]) by irrValid.
    assert (Vteq : [_ ||-v<one> t ≅ u : _ | _ | VB]) by irrValid.
    pose proof (lamCongValid VAeq  VB Vteq).
    econstructor.
    eapply irrValidTm; tea; eapply PiValid; irrValid.
    Unshelve.  all: first [assumption|unshelve eapply PiValid; irrValid| irrValid].
  Qed.

  Lemma FundTmEqFunEta : forall (Γ : context) (f A B : term),
    FundTm Γ (tProd A B) f -> FundTmEq Γ (tProd A B) (tLambda A (tApp f⟨↑⟩ (tRel 0))) f.
  Proof.
  intros * [VΓ VΠ Vf]; econstructor.
  eapply etaValid; irrValid.
  Unshelve.
  + tea.
  + now eapply validΠdom.
  + now eapply validΠcod.
  Qed.

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
    intros * []; unshelve econstructor; tea; irrValid.
  Qed.

  Lemma FundTmEqTrans : forall (Γ : context) (t t' t'' A : term),
    FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t'' ->
    FundTmEq Γ A t t''.
  Proof.
    intros * [] []; unshelve econstructor; irrValid.
  Qed.

  Lemma FundTmEqConv : forall (Γ : context) (t t' A B : term),
    FundTmEq Γ A t t' ->
    FundTyEq Γ A B ->
    FundTmEq Γ B t t'.
  Proof.
    intros * [] []; unshelve econstructor; irrValid.
  Qed.

  Lemma FundTyNat : forall Γ : context, FundCon Γ -> FundTy Γ tNat.
  Proof.
    intros ??; unshelve econstructor; tea;  eapply natValid.
  Qed.

  Lemma FundTmNat : forall Γ : context, FundCon Γ -> FundTm Γ U tNat.
  Proof.
    intros ??; unshelve econstructor; tea.
    2: eapply natValidU.
  Qed.

  Lemma FundTmZero : forall Γ : context, FundCon Γ -> FundTm Γ tNat tZero.
  Proof.
    intros; unshelve econstructor; tea.
    2:eapply zeroValid.
  Qed.

  Lemma FundTmSucc : forall (Γ : context) (n : term),
    FundTm Γ tNat n -> FundTm Γ tNat (tSucc n).
  Proof.
    intros * []; unshelve econstructor; tea; now eapply succValid'.
  Qed.

  Lemma FundTmNatElim : forall (Γ : context) (P hz hs n : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTm Γ tNat n -> FundTm Γ P[n..] (tNatElim P hz hs n).
  Proof.
    intros * [] [] [] []; unshelve econstructor; tea.
    2: eapply natElimValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyEmpty : forall Γ : context, FundCon Γ -> FundTy Γ tEmpty.
  Proof.
    intros ??; unshelve econstructor; tea;  eapply emptyValid.
  Qed.

  Lemma FundTmEmpty : forall Γ : context, FundCon Γ -> FundTm Γ U tEmpty.
  Proof.
    intros ??; unshelve econstructor; tea.
    2: eapply emptyValidU.
  Qed.

  Lemma FundTmEmptyElim : forall (Γ : context) (P n : term),
    FundTy (Γ,, tEmpty) P ->
    FundTm Γ tEmpty n -> FundTm Γ P[n..] (tEmptyElim P n).
  Proof.
    intros * [] []; unshelve econstructor; tea.
    2: eapply emptyElimValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqSuccCong : forall (Γ : context) (n n' : term),
    FundTmEq Γ tNat n n' -> FundTmEq Γ tNat (tSucc n) (tSucc n').
  Proof.
    intros * []; unshelve econstructor; tea; now eapply succValid'.
  Qed.

  Lemma FundTmEqNatElimCong : forall (Γ : context)
      (P P' hz hz' hs hs' n n' : term),
    FundTyEq (Γ,, tNat) P P' ->
    FundTmEq Γ P[tZero..] hz hz' ->
    FundTmEq Γ (elimSuccHypTy P) hs hs' ->
    FundTmEq Γ tNat n n' ->
    FundTmEq Γ P[n..] (tNatElim P hz hs n) (tNatElim P' hz' hs' n').
  Proof.
    intros * [? VP0] [VΓ0] [] []; opector; tea.
    1: unshelve (eapply lrefl, substS; irrValid); eapply natValid.
    unshelve (eapply irrValidTm; [|eapply natElimCongValid]; irrValid); irrValid.
  Qed.

  Lemma FundTmEqNatElimZero : forall (Γ : context) (P hz hs : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTmEq Γ P[tZero..] (tNatElim P hz hs tZero) hz.
  Proof.
    intros * [] [] []; unshelve econstructor; tea.
    2: eapply natElimZeroValid; try irrValid.
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
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqEmptyElimCong : forall (Γ : context)
      (P P' n n' : term),
    FundTyEq (Γ,, tEmpty) P P' ->
    FundTmEq Γ tEmpty n n' ->
    FundTmEq Γ P[n..] (tEmptyElim P n) (tEmptyElim P' n').
  Proof.
    intros * [? VP0 ] [VΓ0]; opector; tea.
    1: unshelve (eapply lrefl, substS; irrValid); eapply emptyValid.
    eapply irrValidTm.
    2: eapply emptyElimCongValid; irrValid.
    tea.
    Unshelve.  all: first [exact Γ| exact one| eassumption| irrValid].
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
    intros * [] []; unshelve econstructor.
    3:eapply SigValidU; irrValid.
    tea.
    Unshelve. 1: now eapply univValid. irrValid.
  Qed.

  Lemma FundTmPair : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b -> FundTm Γ (tSig A B) (tPair A B a b).
  Proof.
    intros * [] [] [] []; unshelve econstructor.
    3: eapply pairValid; irrValid.
    tea.
    Unshelve. 2-4: irrValid.
  Qed.

  Lemma FundTmFst : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTm Γ A (tFst p).
  Proof.
    intros * []; unshelve econstructor.
    3: eapply fstValid; try irrValid.
    2: now eapply validΣdom.
    Unshelve. 2: eapply validΣcod.
  Qed.

  Lemma FundTmSnd : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTm Γ B[(tFst p)..] (tSnd p).
  Proof.
    intros * []; econstructor.
    unshelve eapply sndValid; cycle 2;
    try first [now eapply validΣdom | now eapply validΣcod| irrValid].
  Qed.

  Lemma FundTyEqSigCong : forall (Γ : context) (A B C D : term),
    FundTy Γ A ->
    FundTyEq Γ A B ->
    FundTyEq (Γ,, A) C D -> FundTyEq Γ (tSig A C) (tSig B D).
  Proof.
    intros * [] [] [].
    unshelve econstructor.
    2: eapply SigValid; tea; try irrValid.
    tea. Unshelve. tea.
  Qed.

  Lemma FundTmEqSigCong :forall (Γ : context) (A A' B B' : term),
    FundTm Γ U A ->
    FundTmEq Γ U A A' ->
    FundTmEq (Γ,, A) U B B' -> FundTmEq Γ U (tSig A B) (tSig A' B').
  Proof.
    intros * [] [] []; unshelve econstructor.
    3: eapply SigValidU ; tea; try irrValid.
    tea.
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
    intros * [VΓ VA] [? VA'] [? VA''] [? VB] [? VB''] [?? Va] [?? Vb].
    assert (VAeq : [_ ||-v<one> A' ≅ A'' | VΓ]) by irrValid.
    pose proof (validSnoc _ VA'); pose proof (validSnoc _ VA'').
    assert (VBeq0 : [_ ||-v<one> B ≅ B' | validSnoc VΓ VAeq]) by irrValid.
    assert (VBeq1 : [_ ||-v<one> B ≅ B'' | validSnoc VΓ VAeq]) by irrValid.
    assert (VBeq2 : [_ ||-v<one> B' ≅ B'' | validSnoc VΓ VAeq]) by irrValid.
    assert (Vaeq : [_ ||-v<one> a ≅ a' : _ | _ | VAeq]) by irrValid.
    pose proof (substS VBeq0 Vaeq).
    pose proof (substS VBeq1 Vaeq).
    pose (VBaeq := substS VBeq2 Vaeq).
    assert (Vbeq : [_ ||-v<one> b ≅ b' : _ | _ | VBaeq]) by irrValid.
    epose (pairCongValid _ _ _ Vaeq Vbeq).
    econstructor.
    eapply irrValidTm; tea; unshelve eapply SigValid; irrValid.
    Unshelve. 1,3: tea. unshelve eapply SigValid; irrValid.
  Qed.

  Lemma FundTmEqSigEta : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTmEq Γ (tSig A B) (tPair A B (tFst p) (tSnd p)) p.
  Proof.
  intros * [VΓ VΣ Vp]; econstructor.
  eapply sigEtaValid; irrValid.
  Unshelve.
  + tea.
  + now eapply validΣdom.
  + now eapply validΣcod.
  Qed.

  Lemma FundTmEqFstCong : forall (Γ : context) (A B p p' : term),
    FundTmEq Γ (tSig A B) p p' -> FundTmEq Γ A (tFst p) (tFst p').
  Proof.
    intros * []; unshelve econstructor.
    3: eapply fstValid; irrValid.
    2: now eapply validΣdom.
    Unshelve. 2: eapply validΣcod.
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
    intros * [? VΣ].
    assert (Vp : [_ ||-v<one> p ≅ p' : _ | _ | SigValid _ (validΣdom VΣ) (validΣcod VΣ)]) by irrValid.
    pose (t := sndValid _ _ _ Vp); set (VBfst := substS _ _) in t.
    econstructor. eapply irrValidTm; tea; irrValid.
    Unshelve. all: first [eassumption| irrValid].
  Qed.


  Lemma FundTmEqSndBeta : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b ->
    FundTmEq Γ B[(tFst (tPair A B a b))..] (tSnd (tPair A B a b)) b.
  Proof.
    intros * [] [] [] [].
    unshelve epose (Vsnd := pairSndValid (B:=B) (a:=a) (b:=b) _ VA _ _ _).
    1-3: irrValid.
    ltac2:(HoistLetIn.hoist_let_in @Vsnd).
    unshelve econstructor; [tea| irrValid|].
    unshelve eapply irrValidTm, pairSndValid.
    9: tea. 2: tea. 2-4: irrValid.
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
      unshelve eapply IdValidU ; cycle 1; first [exact one| irrValid].
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
    intros * [] [?? Vx] [? VP] [?? Vhr] [?? Vy] [?? Ve].
    unshelve epose proof (Velim := IdElimValid (hr:=hr) (hr':=hr) _ _ _ _ VP _ _ _ Ve).
    1-4: irrValid.
    ltac2:(HoistLetIn.hoist_let_in @Velim).
    now unshelve econstructor.
  Qed.

  Lemma FundTyEqId : forall (Γ : context) (A A' x x' y y' : term),
    FundTyEq Γ A A' ->
    FundTmEq Γ A x x' -> FundTmEq Γ A y y' -> FundTyEq Γ (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] [].
    unshelve econstructor; tea.
    eapply IdValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqIdCong : forall (Γ : context) (A A' x x' y y' : term),
    FundTmEq Γ U A A' ->
    FundTmEq Γ A x x' -> FundTmEq Γ A y y' -> FundTmEq Γ U (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] []; unshelve econstructor.
    3: unshelve (eapply IdValidU; first [irrValid | tea]).
    all: first [exact one | eassumption | irrValid].
  Qed.

  Lemma FundTmEqReflCong : forall (Γ : context) (A A' x x' : term),
    FundTyEq Γ A A' -> FundTmEq Γ A x x' -> FundTmEq Γ (tId A x x) (tRefl A x) (tRefl A' x').
  Proof.
    intros * [] []; unshelve econstructor; tea.
    2: eapply reflValid; try irrValid.
    eapply IdValid; irrValid.
    Unshelve. all: irrValid.
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
    intros * [] [?? Vx] [? VA'] [?? Vx'] [? VP] [?? Vhr] [?? Vy] [?? Ve].
    unshelve epose proof (VΓext :=idElimMotiveCtxEq (x:=x) (x':=x') _ VA' _); [irrValid|].
    unfold idElimMotiveCtxEqStmt in *.
    assert (VPext : [ _ ||-v<one> P ≅ P' | VΓext]) by irrValid.
    unshelve epose proof (VId := IdValid (x:=x) (x':=x') (y:=y) (y':=y') _ VA' _ _).
    1-2: irrValid.
    assert (Ve' : [_ ||-v<one> e ≅ e' : _ | _ | VId]) by irrValid.
    unshelve epose proof (Velim := IdElimValid (hr:=hr) (hr':=hr') _ _ _ _ VPext _ _ VId Ve').
    1-4: irrValid.
    ltac2:(HoistLetIn.hoist_let_in @Velim).
    unshelve econstructor; tea.
    1: irrValid.
    eapply irrValidTm; tea.
    irrValid.
    Unshelve. tea.
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
    intros * [] [] [] [] [] [] [] [? VAA'] [] [].
    pose (VA' := urefl VAA').
    assert [_ ||-v<one> x ≅ z : _ | _ | VA'] by irrValid.
    assert [_ ||-v<one> y ≅ z : _ | _ | VA'] by irrValid.
    econstructor.
    eapply IdElimReflValid; irrValid.
    Unshelve.
      1: tea. 1,2: irrValid.
      + unshelve eapply idElimMotiveCtxEq; tea; first [exact one |irrValid].
      + irrValid.
      + unshelve (eapply IdValid; irrValid); irrValid.
      + eapply irrValidTm.
        2: eapply reflValid, urefl; tea.
        1: eapply IdValid; irrValid.
        exact one.
    Unshelve.
      2: tea. 3: irrValid.
      2:eapply IdValid; now symmetry.
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
      eapply Fundamental in HA as [].
      unshelve econstructor.
      1: now eapply validSnoc.
      unshelve econstructor.
      + now eapply irrelevanceSubst.
      + now eapply redValidTm'.
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
      apply Fundamental in Hσ0 as [?? Hστ] ; cbn in *.
      eapply Fundamental in HA as [? HA].
      unshelve econstructor.
      + now eapply validSnoc.
      + unshelve econstructor.
        1: now eapply irrelevanceSubst.
        eapply irrLREq; [reflexivity| now eapply redValidTm].
  Qed.

End Fundamental.
