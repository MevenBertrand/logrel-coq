From Coq Require Import ssreflect.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils Context Weakening.

Unset Automatic Proposition Inductives.

Inductive nftykind : Type :=
  | nfPi
  | nfNat.

Reserved Notation "[ |- Γ ≡ Γ' ]".
Reserved Notation "[ Γ ≡ Γ' |- A ≡ B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡nf t' '#Π' Dom , Cod ≡ Dom' , Cod' ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡nf t' '#Nat' ]".
Reserved Notation "[ Γ ≡ Γ' |- A ≡ne B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ]".
Reserved Notation "[ Γ |- A ~> B ]".
Reserved Notation "[ Γ |- A ~* B ]".
Reserved Notation "[ Γ |- t ~>tm u ]".
Reserved Notation "[ Γ |- t ~*tm u ]".

Unset Elimination Schemes.

Inductive ConvCont : context -> context -> Type :=
  | connil :
      [ |- ε ≡ ε ]
  | concons {Γ Γ' A B} :
      [ Γ ≡ Γ' |- A ≡ B]
   -> [ |- Γ ,, A ≡ Γ' ,, B]
with ConvTy : forall (_ _ : context) (_ _ : term), Type :=
  | tyNat {Γ Γ' A B} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- A ~* tNat ]
   -> [ Γ' |- B ~* tNat ]
   -> [ Γ ≡ Γ' |- A ≡ B ]
  | tyProd {Γ Γ' A B Dom Dom' Cod Cod'} :
      [ Γ |- A ~* tProd Dom Cod ]
   -> [ Γ' |- B ~* tProd Dom' Cod' ]
   -> [ Γ ≡ Γ' |- Dom ≡ Dom' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ]
   -> [ Γ ≡ Γ' |- A ≡ B ]
with ConvNeTy : forall (_ _ : context) (_ _ : term), Type :=
with ConvNfProd : forall (_ _ : context) (_ _ _ _ : term) (_ _ : term), Type :=
  | nfFun {Γ Γ' Dom Dom' Cod Cod' t t'} :
      [ Γ ≡ Γ' |- Dom ≡ Dom' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- tApp (t ⟨↑⟩) (tRel 0) ≡ tApp (t' ⟨↑⟩) (tRel 0) # Cod ≡ Cod' ]
   -> [ Γ ≡ Γ' |- t ≡nf t' #Π Dom , Cod ≡ Dom' , Cod' ]
with ConvNfNat : forall (_ _ : context) (_ _ : term), Type :=
  | tmZero {Γ Γ' t t'} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- t ~* tZero ]
   -> [ Γ' |- t' ~* tZero ]
   -> [ Γ ≡ Γ' |- t ≡nf t' #Nat ]
  | tmSucc {Γ Γ' t t' u u'} :
      [ Γ |- t ~* tSucc u ]
   -> [ Γ' |- t' ~* tSucc u' ]
   -> [ Γ ≡ Γ' |- u ≡nf u' #Nat ]
   -> [ Γ ≡ Γ' |- t ≡nf t' #Nat ]
  | tmNeNat {Γ Γ' A B t t' n n'} :
      [ Γ |- A ~* tNat ]
   -> [ Γ' |- B ~* tNat ]
   -> [ Γ |- t ~* n ]
   -> [ Γ' |- t' ~* n' ]
   -> [ Γ ≡ Γ' |- n ≡ne n' # A ≡ B ]
   -> [ Γ ≡ Γ' |- t ≡nf t' #Nat ]
with ConvTm : forall (_ _ : context) (_ _ : term) (_ _ : term), Type :=
  | tmNat {Γ Γ' A B t t'} :
      [ Γ |- A ~* tNat ]
   -> [ Γ' |- B ~* tNat ]
   -> [ Γ ≡ Γ' |- t ≡nf t' #Nat ]
   -> [ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]
  | tmPi {Γ Γ' A B Dom Dom' Cod Cod' t t'} :
      [ Γ |- A ~* tProd Dom Cod ]
   -> [ Γ' |- B ~* tProd Dom' Cod' ]
   -> [ Γ ≡ Γ' |- t ≡nf t' #Π Dom , Cod ≡ Dom' , Cod' ]
   -> [ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]
with ConvNeTm : forall (_ _ : context) (_ _ : term) (_ _ : term), Type :=
  | tmNeVar {Γ Γ' A B n} :
      [ |- Γ ≡ Γ' ]
   -> in_ctx Γ n A
   -> in_ctx Γ' n B
   -> [ Γ ≡ Γ' |- tRel n ≡ne tRel n # A ≡ B ]
  | tmNeApp {Γ Γ' A B Dom Dom' Cod Cod' t t' u u'} :
      [ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ]
   -> [ Γ |- A ~* tProd Dom Cod ]
   -> [ Γ' |- B ~* tProd Dom' Cod' ]
   -> [ Γ ≡ Γ' |- Dom ≡ Dom' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ]
   -> [ Γ ≡ Γ' |- u ≡ u' # Dom ≡ Dom' ]
   -> [ Γ ≡ Γ' |- Cod[u..] ≡ Cod'[u'..] ]
   -> [ Γ ≡ Γ' |- tApp t u  ≡ne tApp t' u' # Cod[u..] ≡ Cod'[u'..] ]
with RedTyStep : forall (_ : context) (_ _ : term), Type :=
with RedTy : forall (_ : context) (_ _ : term), Type :=
  | redTyDone {Γ A} :
      [ Γ |- A ~* A ]
  | redTyStep {Γ A B C} :
      [ Γ |- A ~> B ]
   -> [ Γ |- B ~* C ]
   -> [ Γ |- A ~* C ]
with RedTmStep : forall (_ : context) (_ _ : term), Type :=
  | redBeta {Γ A B t u} :
      [ Γ ≡ Γ |- A ≡ A ]
   -> [ Γ ,, A ≡ Γ ,, A |- B ≡ B ]
   -> [ Γ ,, A ≡ Γ ,, A |- t ≡ t # B ≡ B ]
   -> [ Γ ≡ Γ |- u ≡ u # A ≡ A ]
   -> [ Γ |- tApp (tLambda A t) u ~>tm t[u..] ]
  | redAppHead {Γ A B t t' u} :
      [ Γ ≡ Γ |- A ≡ A ]
   -> [ Γ ,, A ≡ Γ ,, A |- B ≡ B ]
   -> [ Γ ≡ Γ |- t' ≡ t' # tProd A B ≡ tProd A B ]
   -> [ Γ |- t ~>tm t' ]
   -> [ Γ |- tApp t u ~>tm tApp t' u ]
with RedTm : forall (_ : context) (_ _ : term), Type :=
  | redTmDone {Γ t} :
      [ Γ |- t ~*tm t ]
  | redTmStep {Γ t t' t''} :
      [ Γ |- t ~>tm t' ]
   -> [ Γ |- t' ~*tm t'' ]
   -> [ Γ |- t ~*tm t'' ]
  where "[ |- Γ ≡ Γ' ]" := (ConvCont Γ Γ')
    and "[ Γ ≡ Γ' |- A ≡ B ]" := (ConvTy Γ Γ' A B)
    and "[ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]" := (ConvTm Γ Γ' A B t t')
    and "[ Γ ≡ Γ' |- t ≡nf t' '#Π' Dom , Cod ≡ Dom' , Cod' ]" := (ConvNfProd Γ Γ' Dom Cod Dom' Cod' t t')
    and "[ Γ ≡ Γ' |- t ≡nf t' '#Nat' ]" := (ConvNfNat Γ Γ' t t')
    and "[ Γ ≡ Γ' |- A ≡ne B ]" := (ConvNeTy Γ Γ' A B)
    and "[ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ]" := (ConvNeTm Γ Γ' A B t t')
    and "[ Γ |- A ~> B ]" := (RedTyStep Γ A B)
    and "[ Γ |- A ~* B ]" := (RedTy Γ A B)
    and "[ Γ |- t ~>tm u ]" := (RedTmStep Γ t u)
    and "[ Γ |- t ~*tm u ]" := (RedTm Γ t u).

(* Maybe try with a specific conversion relation at each whnf type *)
(* Also separate reduction and conversion more cleanly *)

Derive Signature for ConvCont.
Derive Signature for ConvTy.
Derive Signature for ConvTm.
Derive Signature for ConvNfNat.
Derive Signature for ConvNfProd.
Derive Signature for ConvNeTm.
Derive Signature for RedTy.
Derive Signature for RedTyStep.
Derive Signature for RedTmStep.
Derive Signature for RedTm.

Scheme ConvCont_rect_nodep := Minimality for ConvCont Sort Type
  with ConvTy_rect_nodep := Minimality for ConvTy Sort Type
  with ConvTm_rect_nodep := Minimality for ConvTm Sort Type
  with ConvNfNat_rect_nodep := Minimality for ConvNfNat Sort Type
  with ConvNfProd_rect_nodep := Minimality for ConvNfProd Sort Type
  with ConvNeTm_rect_nodep := Minimality for ConvNeTm Sort Type
  with RedTy_rect_nodep := Minimality for RedTy Sort Type
  with RedTmStep_rect_nodep := Minimality for RedTmStep Sort Type
  with RedTm_rect_nodep := Minimality for RedTm Sort Type.

Combined Scheme _Syntax_rect_nodep from
ConvCont_rect_nodep,
ConvTy_rect_nodep,
ConvTm_rect_nodep,
ConvNfNat_rect_nodep,
ConvNfProd_rect_nodep,
ConvNeTm_rect_nodep,
RedTy_rect_nodep,
RedTmStep_rect_nodep,
RedTm_rect_nodep.

Definition _SyntaxInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _Syntax_rect_nodep);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Definition SyntaxInductionType :=
  ltac: (let ind := eval cbv delta [_SyntaxInductionType] zeta
    in _SyntaxInductionType in
    let ind' := polymorphise ind in
  exact ind').

Definition SyntaxInduction : SyntaxInductionType.
Proof.
  intros P1 P2 P3 P4 P5 P6 P7 P8 P9 **.
  assert (H : _) by (apply (_Syntax_rect_nodep P1 P2 P3 P4 P5 P6 P7 P8 P9); assumption).
  repeat econstructor; apply H.
Defined.

Definition SyntaxInductionConcl := ltac:(let t := eval cbv delta [SyntaxInductionType] beta in SyntaxInductionType in let t' := remove_steps t in exact t').
Print SyntaxInductionConcl.

Lemma Conv_ConvCont : SyntaxInductionConcl
  (fun _ _ => unit)
  (fun Γ Γ' _ _ => [ |- Γ ≡ Γ' ])
  (fun Γ Γ' _ _ _ _ => [ |- Γ ≡ Γ' ])
  (fun Γ Γ' _ _ => [ |- Γ ≡ Γ' ])
  (fun Γ Γ' _ _ _ _ _ _ => [ |- Γ ≡ Γ' ])
  (fun Γ Γ' _ _ _ _ => [ |- Γ ≡ Γ' ])
  (fun Γ _ _ => unit)
  (fun Γ _ _ => unit)
  (fun Γ _ _ => unit).
Proof.
  eapply SyntaxInduction; easy.
Defined.

Lemma Conv_Symm : SyntaxInductionConcl
  (fun Γ Γ' => [ |- Γ' ≡ Γ ])
  (fun Γ Γ' A B => [ Γ' ≡ Γ |- B ≡ A ])
  (fun Γ Γ' A B t u => [ Γ' ≡ Γ |- u ≡ t # B ≡ A ])
  (fun Γ Γ' t u => [ Γ' ≡ Γ |- u ≡nf t #Nat ])
  (fun Γ Γ' Dom Cod Dom' Cod' t u => [ Γ' ≡ Γ |- u ≡nf t #Π Dom' , Cod' ≡ Dom , Cod ])
  (fun Γ Γ' A B t u => [ Γ' ≡ Γ |- u ≡ne t # B ≡ A ] )
  (fun _ _ _ => unit)
  (fun _ _ _ => unit)
  (fun _ _ _ => unit).
Proof.
  eapply SyntaxInduction; now econstructor.
Defined.

Fixpoint redStepDet {Γ A B C}
  (H1 : [ Γ |- A ~> B ])
  (H2 : [ Γ |- A ~> C ])  :
   B = C.
Proof.
  depelim H1.
Defined.

Derive NoConfusion for term.

Fixpoint redTmStepDet {Γ t u u'}
  (H1 : [ Γ |- t ~>tm u ])
  (H2 : [ Γ |- t ~>tm u' ])  :
   u = u'.
Proof.
  depelim H1; depelim H2.
  - reflexivity.
  - depelim H2.
  - depelim H1.
  - now f_equal.
Defined.

Definition whnfTyb (t : term) := match t with | tProd _ _ => true | tNat => true | _ => false end.

Fixpoint redDet {Γ A B C}
  (H1 : [ Γ |- A ~* B ])
  (H2 : [ Γ |- A ~* C ])
  (Bwhnf : whnfTyb B = true)
  (Cwhnf : whnfTyb C = true) :
   B = C.
Proof.
  depelim H1; depelim H2.
  - reflexivity.
  - depelim A; noconf Bwhnf; depelim r.
  - depelim A; noconf Cwhnf; depelim r.
  - assert (H : B = B0) by now eapply redStepDet. subst. now eapply redDet.
Defined.


Lemma Conv_Trans : SyntaxInductionConcl
  (fun Γ Γ' => forall Γ'', [ |- Γ' ≡ Γ'' ] -> [ |- Γ ≡ Γ'' ])
  (fun Γ Γ' A B => forall Γ'' C, [ Γ' ≡ Γ'' |- B ≡ C ] -> [ Γ ≡ Γ'' |- A ≡ C ])
  (fun Γ Γ' A B t u => forall Γ'' C v, [ Γ' ≡ Γ'' |- u ≡ v # B ≡ C ] -> [ Γ ≡ Γ'' |- t ≡ v # A ≡ C ])
  (fun Γ Γ' t u => forall Γ'' v, [ Γ' ≡ Γ'' |- u ≡nf v #Nat ] -> [ Γ ≡ Γ'' |- t ≡nf v #Nat ])
  (fun Γ Γ' Dom Cod Dom' Cod' t u => forall Γ'' Dom'' Cod'' v,
    [ Γ' ≡ Γ'' |- u ≡nf v #Π Dom' , Cod' ≡ Dom'' , Cod'' ]
    -> [ Γ ≡ Γ'' |- t ≡nf v #Π Dom , Cod ≡ Dom'' , Cod'' ])
  (fun Γ Γ' A B t u => forall Γ'' C v, [ Γ' ≡ Γ'' |- u ≡ne v # B ≡ C ] -> [ Γ ≡ Γ'' |- t ≡ne v # A ≡ C ] )
  (fun _ _ _ => unit)
  (fun _ _ _ => unit)
  (fun _ _ _ => unit).
Proof.
  eapply SyntaxInduction; intros *; repeat first [ intros ? ? * | try rename H into H'; intros H ].
  all: try lazymatch goal with [|- unit] => constructor end.
  all: depelim H.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - assert (conf : tNat = tProd Dom Cod) by (eapply redDet; easy). noconf conf.
  - eassert (conf : tNat = tProd _ _) by (eapply (redDet (A := A0)); easy).
    noconf conf.
  - assert (noconf : tProd Dom' Cod' = tProd Dom0 Cod0) by (eapply redDet; easy).
    noconf noconf.
    eapply tyProd; easy.
  -
Defined.

Fixpoint ConvTm_ConvTy {Γ Γ' t t' A B}
  (H : [ Γ ≡ Γ' |- t ≡ t' # A ≡ B ])
  : [ Γ ≡ Γ' |- A ≡ B ]
  with ConvNfProd_ConvTy {Γ Γ' t t' Dom Dom' Cod Cod'}
  (H : [ Γ ≡ Γ' |- t ≡nf t' ]).
Proof.
  depelim H.
  - eapply tyNat; [eapply ConvNfNat_ConvCont|..]; eassumption.
  - depelim c. eapply tyProd; [eapply ConvNfProd_ConvCont|..]; eassumption.
Defined.

Fixpoint ConvNeTm_ConvTy {Γ Γ' t t' A B}
  (H : [ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ])
  : [ Γ ≡ Γ' |- A ≡ B ].
Proof.
Defined.

Lemma reflNat {Γ Γ'}
  (H : [ |- Γ ≡ Γ' ])
  : [ Γ ≡ Γ' |- tNat ≡ tNat ].
Proof.
  apply tyNat.
  - assumption.
  - apply redTyDone.
  - apply redTyDone.
Defined.

Fixpoint norm {Γ Γ' t t' A A'}
  (H : [ Γ ≡ Γ' |- t ≡ t' # A ≡ A' ]) {struct H}:
  term
  with normNe {Γ Γ' t t' A A'}
  (H : [ Γ ≡ Γ' |- t ≡ne t' # A ≡ A' ]) {struct H} : term
  with normTy {Γ Γ' A A'}
  (H : [ Γ ≡ Γ' |- A ≡ A' ]) {struct H} : term.
Proof.
  - inversion H.
    + exact tZero.
    + refine (tSucc _). eapply norm; exact X3.
    + eapply normNe; exact X1.
    + refine (tProd _ _).
      * eapply normTy; exact X1.
      * eapply norm; exact X3.
  - inversion H.
    + exact (tRel n).
    + refine (tApp _ _).
      * eapply normNe; exact X.
      * eapply norm; exact X4.
  - inversion H.
    + exact tNat.
    + refine (tProd _ _).
      * eapply normTy; exact X1.
      * eapply normTy; exact X2.
Defined.

Fixpoint normCtx {Γ Γ'}
  (H : [ |- Γ ≡ Γ' ]) {struct Γ}
  : context.
Proof.
  revert H. destruct Γ; inversion 1.
  - exact ε.
  - refine (_,,_).
    + eapply normTy; exact X.
    + eapply normCtx; eapply ConvTy_ConvCont; eassumption.
Defined.

Fixpoint normCorrect {Γ Γ' t t' A A'}
  (H : [ Γ ≡ Γ' |- t ≡ t' # A ≡ A' ])
  : ([ normCtx (ConvTm_ConvCont H) ≡ Γ' |- norm H ≡ t' # normTy (ConvTm_ConvTy H) ≡ A' ])
  with normNeCorrect {Γ Γ' t t' A A'}
  (H : [ Γ ≡ Γ' |- t ≡ne t' # A ≡ A' ])
  : [ normCtx (ConvNeTm_ConvCont H) ≡ Γ' |- normNe H ≡ne t' # normTy (ConvNeTm_ConvTy H) ≡ A' ]
  with normTyCorrect {Γ Γ' A A'}
  (H : [ Γ ≡ Γ' |- A ≡ A' ]) :
  term.


Example id (t := tLambda tNat (tRel 0)) (A := tProd tNat tNat) :
  [ ε ≡ ε |- t ≡ t # A ≡ A ].
Proof.
  assert ([ |- ε ,, tNat ≡ ε ,, tNat ]).
  { apply concons; apply reflNat ; apply connil. }
  eapply tmFun.
  - apply redTyDone.
  - apply redTyDone.
  - apply reflNat; apply connil.
  - apply reflNat; assumption.
  - assert [ε,, tNat |- tApp t⟨↑⟩ (tRel 0) ~* tRel 0 # tNat].
    { eapply redTmStep; [|apply redTmDone].
      cbn.
      eapply (redBeta (t := tRel 0) (B := tNat)).
      * apply reflNat; assumption.
      * apply reflNat; apply concons; apply reflNat; assumption.
      * eapply tmNeNat.
        -- apply redTmDone.
        -- apply redTmDone.
        -- apply tmNeVar;[ | apply in_here | apply in_here].
           apply concons; apply reflNat; assumption.
        -- apply redTyDone.
        -- apply redTyDone.
      * eapply tmNeNat.
        -- apply redTmDone.
        -- apply redTmDone.
        -- apply tmNeVar;[ | apply in_here | apply in_here].
           assumption.
        -- apply redTyDone.
        -- apply redTyDone. }
    eapply tmNeNat.
    + eassumption.
    + eassumption.
    + eapply tmNeVar.
      * assumption.
      * apply in_here.
      * apply in_here.
    + eapply redTyDone.
    + eapply redTyDone.
Defined.
