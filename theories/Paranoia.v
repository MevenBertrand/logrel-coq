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

Inductive ConvCont : context -> context -> Type :=
  | connil :
      [ |- ε ≡ ε ]
  | concons {Γ Γ' A B} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ ≡ Γ' |- A ≡ B]
   -> [ |- Γ ,, A ≡ Γ' ,, B]
with ConvTy : forall (_ _ : context) (_ _ : term), Type :=
  | tyNat {Γ Γ' A B} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- A ~* tNat ]
   -> [ Γ' |- B ~* tNat ]
   -> [ Γ ≡ Γ' |- A ≡ B ]
  | tyProd {Γ Γ' A B Dom Dom' Cod Cod'} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- A ~* tProd Dom Cod ]
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
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- A ~* tNat ]
   -> [ Γ |- B ~* tNat ]
   -> [ Γ |- t ~* tSucc u # tNat ]
   -> [ Γ' |- t' ~* tSucc u' # tNat ]
   -> [ Γ ≡ Γ' |- u ≡ u' # tNat ≡ tNat ]
   -> [ Γ ≡ Γ' |- t ≡ t' # A ≡ B ]
  | tmNeNat {Γ Γ' A A' B B' t t' n n'} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- t ~* n # tNat ]
   -> [ Γ |- t' ~* n' # tNat ]
   -> [ Γ ≡ Γ' |- n ≡ne n' # A ≡ B ]
   -> [ Γ |- A' ~* tNat ]
   -> [ Γ |- B' ~* tNat ]
   -> [ Γ ≡ Γ' |- t ≡ t' # A' ≡ B' ]
  | tmFun {Γ Γ' A B Dom Dom' Cod Cod' t t'} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ |- A ~* tProd Dom Cod ]
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
      [ |- Γ ≡ Γ' ]
   -> [ Γ ≡ Γ' |- t ≡ne t' # A ≡ B ]
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
  | redBeta {Γ A B C t u} :
      [ |- Γ ≡ Γ ]
   -> [ Γ ≡ Γ |- A ≡ A ]
   -> [ Γ ,, A ≡ Γ ,, A |- B ≡ B ]
   -> [ Γ ,, A ≡ Γ ,, A |- t ≡ t # B ≡ B ]
   -> [ Γ ≡ Γ |- u ≡ u # A ≡ A ]
   -> [ Γ ≡ Γ |- B[u..] ≡ C ]
   -> [ Γ |- tApp (tLambda A t) u ~> t[u..] # C ]
  | redAppHead {Γ A B C t t' u} :
      [ |- Γ ≡ Γ]
   -> [ Γ ≡ Γ |- A ≡ A ]
   -> [ Γ ,, A ≡ Γ ,, A |- B ≡ B ]
   -> [ Γ ≡ Γ |- t' ≡ t' # tProd A B ≡ tProd A B ]
   -> [ Γ |- t ~> t' # tProd A B ]
   -> [ Γ ≡ Γ |- u ≡ u # A ≡ A ]
   -> [ Γ ≡ Γ |- B[u..] ≡ C ]
   -> [ Γ |- tApp t u ~> tApp t' u # C ]
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

Example id (t := tLambda tNat (tRel 0)) (A := tProd tNat tNat) :
  [ ε ≡ ε |- t ≡ t # A ≡ A ].
Proof.
  assert ([ |- ε ,, tNat ≡ ε ,, tNat ]).
  { apply concons; [apply connil| apply reflNat ; apply connil]. }
  eapply tmFun.
  - apply connil.
  - apply redTyDone.
  - apply redTyDone.
  - apply reflNat; apply connil.
  - apply reflNat; assumption.
  - eapply tmNeNat.
    + assumption.
    + eapply redTmStep; [|apply redTmDone].
      eapply redBeta.
      * assumption.
      * apply reflNat; assumption.
      * apply reflNat; apply concons; [assumption| apply reflNat; assumption].
      * 
    + eapply redTmStep.
    + eapply (tmNeApp (Cod := tNat) (Cod' := tNat)).
