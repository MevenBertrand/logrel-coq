From Coq Require Import ssreflect.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils Context Weakening.

Unset Automatic Proposition Inductives.

Inductive nftykind : Type :=
  | nfPi
  | nfNat.

Reserved Notation "[ |- Γ ≡ Γ' ]".
Reserved Notation "[ Γ ≡ Γ' |- A ≡ B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]".
Reserved Notation "[ Γ ≡ Γ' |- A ≡ne B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ]".
Reserved Notation "[ Γ |- A ~> B ]".
Reserved Notation "[ Γ |- A ~* B ]".
Reserved Notation "[ Γ |- t ~> u # A ]".
Reserved Notation "[ Γ |- t ~* u # A ]".

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
with ConvTm : forall (_ _ : context) (_ _ : term) (_ _ : term), Type :=
  | tmZero {Γ Γ' A B t t'} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- A ~* tNat ]
   -> [ Γ' |- B ~* tNat ]
   -> [ Γ |- t ~* tZero # tNat ]
   -> [ Γ' |- t' ~* tZero # tNat ]
   -> [ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]
  | tmSucc {Γ Γ' A B t t' u u'} :
      [ Γ |- A ~* tNat ]
   -> [ Γ' |- B ~* tNat ]
   -> [ Γ |- t ~* tSucc u # tNat ]
   -> [ Γ' |- t' ~* tSucc u' # tNat ]
   -> [ Γ ≡ Γ' |- u ≡ u' # tNat ≡ tNat ]
   -> [ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]
  | tmNeNat {Γ Γ' A A' B B' t t' n n'} :
      [ Γ |- t ~* n # tNat ]
   -> [ Γ' |- t' ~* n' # tNat ]
   -> [ Γ ≡ Γ' |- n ≡ne n' # A ≡ B ]
   -> [ Γ |- A' ~* tNat ]
   -> [ Γ' |- B' ~* tNat ]
   -> [ Γ ≡ Γ' |- t ≡ t' # A' ≡ B' ]
  | tmFun {Γ Γ' A B Dom Dom' Cod Cod' t t'} :
      [ Γ |- A ~* tProd Dom Cod ]
   -> [ Γ' |- B ~* tProd Dom' Cod' ]
   -> [ Γ ≡ Γ' |- Dom ≡ Dom' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- tApp (t ⟨↑⟩) (tRel 0) ≡ tApp (t' ⟨↑⟩) (tRel 0) # Cod ≡ Cod' ]
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
with RedTmStep : forall (_ : context) (_ _ _ : term), Type :=
  | redBeta {Γ A B t u out outTy} :
      [ Γ ≡ Γ |- A ≡ A ]
   -> [ Γ ,, A ≡ Γ ,, A |- B ≡ B ]
   -> [ Γ ,, A ≡ Γ ,, A |- t ≡ t # B ≡ B ]
   -> [ Γ ≡ Γ |- u ≡ u # A ≡ A ]
   -> out = t[u..]
   -> outTy = B[u..]
   -> [ Γ |- tApp (tLambda A t) u ~> out # outTy ]
  | redAppHead {Γ A B t t' u out outTy} :
      [ Γ ≡ Γ |- A ≡ A ]
   -> [ Γ ,, A ≡ Γ ,, A |- B ≡ B ]
   -> [ Γ ≡ Γ |- t' ≡ t' # tProd A B ≡ tProd A B ]
   -> [ Γ |- t ~> t' # tProd A B ]
   -> [ Γ ≡ Γ |- u ≡ u # A ≡ A ]
   -> out = tApp t' u
   -> outTy = B[u..]
   -> [ Γ |- tApp t u ~> out # outTy ]
with RedTm : forall (_ : context) (_ _ _ : term), Type :=
  | redTmDone {Γ A t} :
      [ Γ |- t ~* t # A ]
  | redTmStep {Γ A t t' t''} :
      [ Γ |- t ~> t' # A ]
   -> [ Γ |- t' ~* t'' # A ]
   -> [ Γ |- t ~* t'' # A ]
  where "[ |- Γ ≡ Γ' ]" := (ConvCont Γ Γ')
    and "[ Γ ≡ Γ' |- A ≡ B ]" := (ConvTy Γ Γ' A B)
    and "[ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]" := (ConvTm Γ Γ' A B t t')
    and "[ Γ ≡ Γ' |- A ≡ne B ]" := (ConvNeTy Γ Γ' A B)
    and "[ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ]" := (ConvNeTm Γ Γ' A B t t')
    and "[ Γ |- A ~> B ]" := (RedTyStep Γ A B)
    and "[ Γ |- A ~* B ]" := (RedTy Γ A B)
    and "[ Γ |- t ~> u # A ]" := (RedTmStep Γ A t u)
    and "[ Γ |- t ~* u # A ]" := (RedTm Γ A t u).

(* Maybe try with a specific conversion relation at each whnf type *)
(* Also separate reduction and conversion more cleanly *)

Scheme ConvCont_rect_nodep := Minimality for ConvCont Sort Type
  with ConvTy_rect_nodep := Minimality for ConvTy Sort Type
  with ConvTm_rect_nodep := Minimality for ConvTm Sort Type
  with ConvNeTy_rect_nodep := Minimality for ConvNeTy Sort Type
  with ConvNeTm_rect_nodep := Minimality for ConvNeTm Sort Type
  with RedTyStep_rect_nodep := Minimality for RedTyStep Sort Type
  with RedTy_rect_nodep := Minimality for RedTy Sort Type
  with RedTmStep_rect_nodep := Minimality for RedTmStep Sort Type
  with RedTm_rect_nodep := Minimality for RedTm Sort Type.


Lemma ConvTy_ConvCont : forall {Γ Γ' A B}, [ Γ ≡ Γ' |- A ≡ B ] -> [ |- Γ ≡ Γ' ]
 with ConvTm_ConvCont : forall {Γ Γ' A B t u}, [ Γ ≡ Γ' |- t ≡ u # A ≡ B ] -> [ |- Γ ≡ Γ' ]
 with ConvNeTm_ConvCont : forall {Γ Γ' A B t u}, [ Γ ≡ Γ' |- t ≡ne u # A ≡ B ] -> [ |- Γ ≡ Γ' ].
Proof.
  - move=> ???? [].
    * tauto.
    * move=> *.
      eapply ConvTy_ConvCont; eassumption.
  - move=> ?????? [].
    * tauto.
    * move=> *.
      eapply ConvTm_ConvCont; eassumption.
    * move=> *.
      eapply ConvNeTm_ConvCont; eassumption.
    * move=> *.
      eapply ConvTy_ConvCont; eassumption.
  - move=> ?????? [].
    * tauto.
    * move=> *.
      eapply ConvNeTm_ConvCont; eassumption.
Defined.

Fixpoint ConvTm_ConvTy {Γ Γ' t t' A B}
  (H : [ Γ ≡ Γ' |- t ≡ t' # A ≡ B ])
  : [ Γ ≡ Γ' |- A ≡ B ].
Proof.
  inversion H.
  - eapply tyNat; eassumption.
  - eapply tyNat; [eapply ConvTm_ConvCont|..]; eassumption.
  - eapply tyNat; [eapply ConvNeTm_ConvCont|..]; eassumption.
  - eapply tyProd; eassumption.
Defined.

Fixpoint ConvCtx_wk {Γ Γ' Δ Δ'}
  (H : [ |- Γ ≡ Γ' ])
  (o ).

Fixpoint ConvNeTm_ConvTy {Γ Γ' t t' A B}
  (H : [ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ])
  : [ Γ ≡ Γ' |- A ≡ B ].
Proof.
  inversion H.
  - eapply tyNat; eassumption.
  - eapply tyNat; [eapply ConvTm_ConvCont|..]; eassumption.
  - eapply tyNat; [eapply ConvNeTm_ConvCont|..]; eassumption.
  - eapply tyProd; eassumption.
Defined.

Lemma reflNat {Γ Γ'} :
  [ |- Γ ≡ Γ' ]
  -> [ Γ ≡ Γ' |- tNat ≡ tNat ].
Proof.
  move=> ?.
  apply tyNat.
  - assumption.
  - apply redTyDone.
  - apply redTyDone.
Defined.

Fixpoint redDet {Γ t u u' A A'}
  (H1 : [ Γ |- t ~> u # A ])
  (H2 : [ Γ |- t ~> u' # A' ])  :
   u = u'.
Proof.
  inversion H1; inversion H2; subst.
    - inversion H11; subst. reflexivity.
    - inversion H11; subst. inversion X6.
    - inversion H11; subst. inversion X2.
    - inversion H11; subst. f_equal. eapply redDet; eassumption.
Defined.

Fixpoint norm {Γ Γ' t t' A A'}
  (H : [ Γ ≡ Γ' |- t ≡ t' # A ≡ A' ]) :
  term
  with normNe {Γ Γ' t t' A A'}
  (H : [ Γ ≡ Γ' |- t ≡ne t' # A ≡ A' ]) : term
  with normTy {Γ Γ' A A'}
  (H : [ Γ ≡ Γ' |- A ≡ A' ]) : term
  with normCtx {Γ Γ'}
  (H : [ |- Γ ≡ Γ' ]) : context.
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
  - inversion H.
    + exact ε.
    + refine (_ ,, _).
      * eapply normTy; exact X.
      * eapply normCtx; eapply ConvTy_ConvCont; exact X.
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
      eapply redBeta.
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
        -- apply redTyDone.
      * reflexivity.
      * reflexivity. }
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
