From Coq Require Import ssreflect.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import BasicAst Utils Context Weakening.

From Ltac2 Require Import Ltac2 Printf.
(* From Ltac2 Require Control Constr List Ltac1 Std Notations. *)

Unset Automatic Proposition Inductives.
Set Default Goal Selector "all".


Ltac2 depelim (i : ident) : unit := ltac1:(i |- depelim i) (Ltac1.of_ident i).
Ltac2 Notation "depelim" i(ident) := depelim i.

Ltac2 noconf (i : ident) : unit := ltac1:(i |- noconf i) (Ltac1.of_ident i).
Ltac2 Notation "noconf" i(ident) := noconf i.

Ltac2 eassumption0 := fun () => ltac1:(eassumption).
Ltac2 Notation "eassumption" := eassumption0 ().

Ltac2 Notation ">" c(thunk(tactic)) := Control.enter c.
Ltac2 Notation c1(thunk(self)) "+" c2(thunk(tactic)) := Control.plus c1 (fun _ => c2 ()).
Ltac2 Notation c1(thunk(self)) "||" c2(thunk(tactic)) := Notations.orelse c1 (fun _ => c2 ()).
Ltac2 Notation "[>" tacs(list0(thunk(self),"|")) "]" := Control.dispatch tacs.

Ltac2 Notation "only" startgoal(tactic) endgoal(opt(seq("-", tactic))) ":" tac(thunk(tactic)) :=
  Control.focus startgoal (Option.default startgoal endgoal) tac.

Set Equations With UIP.

Derive NoConfusion EqDec for sort term.
Derive NoConfusion for prod.

Instance prodEqDec A B : EqDec A -> EqDec B -> EqDec (A × B).
Proof.
  intros eqA eqB.
  intros p1 p2.
  destruct p1 as (a & b).
  destruct p2 as (a' & b').
  assert (deca : ({a = a'} + {a <> a'})) by (now apply eqA).
  assert (decb : ({b = b'} + {b <> b'})) by (now apply eqB).
  destruct deca as [aeq|anoteq].
  destruct decb as [beq|bnoteq].
  - left. now f_equal.
  - right. intro eq. noconf eq. apply bnoteq. reflexivity.
  - right. intro eq. noconf eq. apply anoteq. reflexivity.
  - right. intro eq. noconf eq. apply anoteq. reflexivity.
Defined.

Derive Signature NoConfusion for in_ctx.

Class HProp A := hProp : forall (a b : A), a = b.

Instance HProp_EqDec A (isHProp : HProp A) : EqDec A.
Proof.
  intros a b.
  left.
  apply isHProp.
Defined.

Instance in_ctx_HProp Γ n d : HProp (in_ctx Γ n d).
Proof.
  intros ctx.
  induction ctx.
  intros y.
  depelim y.
  - reflexivity.
  - assert (d0 = d) by (now eapply in_ctx_inj).
    subst.
    noconf e.
    cbn in H. noconf H.
    f_equal. now eapply IHctx.
Defined.

Inductive renames (Γ : context) : forall (ρ : nat -> nat) (Δ : context), Type :=
  | ren_empty {ρ} :
      renames Γ ρ ε
  | ren_tm {Δ A ρ} :
      renames Γ (↑ >> ρ) Δ
   -> in_ctx Γ (ρ 0) A⟨↑ >> ρ⟩
   -> renames Γ ρ (Δ ,, A).

Scheme renames_rect_nodep := Minimality for renames Sort Type.
Derive Signature for renames.

Lemma VarRen {Γ A n}
  (H : in_ctx Γ n A)
  : forall {Δ τ}
  (X : renames Δ τ Γ),
  in_ctx Δ (τ n) A⟨τ⟩.
Proof.
  induction H. intros **.
  depelim X.
  rewrite -> !renRen_term.
  ltac1:(change (τ (S ?n)) with ((↑ >> τ) n)).
  eauto.
Defined.

Lemma RenComp {Γ Δ ρ}
  (H : renames Γ ρ Δ)
  : forall {Ξ τ}
  (X : renames Ξ τ Γ),
  renames Ξ (ρ >> τ) Δ.
Proof.
  induction H.
  intros **.
  econstructor.
  - eauto.
  - change (↑ >> (ρ >> τ)) with ((↑ >> ρ) >> τ).
    rewrite <- !(renRen_term (↑ >> ρ)).
    change ((ρ >> τ) 0) with (τ (ρ 0)).
    eapply VarRen.
    eassumption.
Defined.

Fixpoint iter {A} (n : nat) (f : A -> A) : A -> A :=
  match n with
  | O => id
  | S n => iter n f >> f
  end.

Lemma iter_inside {A} (n : nat) (f : A -> A)
  : iter (S n) f = f >> iter n f.
Proof.
  revert f.
  induction n.
  - reflexivity.
  - intros ?.
    cbn delta [iter] iota.
    ltac1:(change ((?a >> ?b) >> ?c) with (a >> (b >> c))).
    apply (f_equal (fun g => g >> f)).
    apply IHn.
Defined.

Lemma VarWk {Γ A n}
  (H : in_ctx Γ n A) :
  forall {T},
  in_ctx (Γ ,,, T) (iter #|T| ↑ n) A⟨iter #|T| ↑⟩.
Proof.
  induction H.
  intros T.
  induction T.
  cbn.
  rewrite -> ?rinstId'_term, <- ?renRen_term.
  econstructor; eauto.
Defined.

Lemma RenWeakening {Γ Ξ ρ}
  (H : renames Γ ρ Ξ) :
  forall T,
  renames (Γ ,,, T) (ρ >> iter #|T| ↑) Ξ.
Proof.
  induction H.
  econstructor.
  ltac1:(change (↑ >> (iter #|T| ↑ >> ρ)) with ((↑ >> iter #|T| ↑) >> ρ)).
  - eapply IHrenames.
  - change (↑ >> (ρ >> iter #|T| ↑)) with ((↑ >> ρ) >> iter #|T| ↑).
    rewrite <- renRen_term.
    eapply VarWk; eassumption.
Defined.

Lemma RenWeakenOnce {Γ Ξ ρ}
  (H : renames Γ ρ Ξ) :
  forall {A},
  renames (Γ ,, A) (ρ >> ↑) Ξ.
Proof.
  intros A.
  apply (RenWeakening H (ε ,, A)).
Defined.

Lemma RenId Γ :
  renames Γ id Γ.
Proof.
  induction Γ.
  - econstructor.
  - econstructor.
    + now eapply RenWeakenOnce.
    + econstructor.
Defined.

(* Type system *)
Reserved Notation "[ |- Γ ≡ Γ' ]".
Reserved Notation "[ Γ ≡ Γ' |- A ≡ B ]".
Reserved Notation "[ Γ ≡ Γ' |- A ≡whnf B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ t' ◁ A ≡ B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡whnf t' ▷ A ≡whnf B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ t' ▷ A ≡whnf B ]".
Reserved Notation "[ Γ ≡ Γ' |- A ≡ne B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ne t' '▷red' A ≡ B ]".
Reserved Notation "[ Γ ≡ Γ' |- t ≡ne t' ▷ A ≡ B ]".
Reserved Notation "[ Γ |- A ~> B ]".
Reserved Notation "[ Γ |- A ~* B ]".
Reserved Notation "[ Γ |- t ↗ u ]".
Reserved Notation "[ Γ |- t ~>tm u ]".
Reserved Notation "[ Γ |- t ~*tm u ]".

Inductive judgement : Type :=
  | ConvCont
  | ConvTy
  | ConvWhnfTy
  | ConvNeTy
  | ConvCheckTm
  | ConvTm
  | ConvWhnfTm
  | ConvNeRedTm
  | ConvNeTm
  | RedTy
  | RedTmStep
  | ExpTmStep
  | RedTm.

Definition judgement_indices (j : judgement) : Type :=
  match j with
  | ConvCont => context × context
  | ConvTy | ConvWhnfTy | ConvNeTy
    => context × context × term × term
  | ConvCheckTm | ConvTm | ConvWhnfTm | ConvNeRedTm | ConvNeTm
    => context × context × term × term × term × term
  | RedTy | RedTmStep | ExpTmStep | RedTm
    => context × term × term
  end.

Instance judgement_indices_EqDec j : EqDec (judgement_indices j).
Proof.
  destruct j.
  simpl.
  ltac1:(typeclasses eauto).
Defined.

Derive NoConfusion EqDec for judgement.

Inductive Paranoia : forall (j : judgement) (i : judgement_indices j), Type :=
  | connil :
      [ |- ε ≡ ε ]
  | concons {Γ Γ' A B}
      (typeWf : [ Γ ≡ Γ' |- A ≡ B])
    : [ |- Γ ,, A ≡ Γ' ,, B]

  | normTy {Γ Γ' A B A' B'}
      (typeWhnf : [ Γ ≡ Γ' |- A' ≡whnf B' ])
      (typeRedL : [ Γ |- A ~* A' ])
      (typeRedR : [ Γ' |- B ~* B' ])
    : [ Γ ≡ Γ' |- A ≡ B ]

  | nfNat {Γ Γ'}
      (contWf : [ |- Γ ≡ Γ' ])
    : [ Γ ≡ Γ' |- tNat ≡whnf tNat ]
  | nfProd {Γ Γ' Dom Dom' Cod Cod'}
      (DomWf : [ Γ ≡ Γ' |- Dom ≡ Dom' ])
      (CodWf : [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ])
    : [ Γ ≡ Γ' |- tProd Dom Cod ≡whnf tProd Dom' Cod' ]

  | check {Γ Γ' A B A' B' t t'}
      (termInfer : [ Γ ≡ Γ' |- t ≡ t' ▷ A ≡whnf B ])
      (typeConvL : [ Γ ≡ Γ |- A' ≡ A ])
      (typeConvR : [ Γ' ≡ Γ' |- B' ≡ B ])
    : [ Γ ≡ Γ' |- t ≡ t' ◁ A' ≡ B' ]

  | norm {Γ Γ' A B t t' u u'}
      (termWhnfInfer : [ Γ ≡ Γ' |- t ≡whnf t' ▷ A ≡whnf B ])
      (termRedL : [ Γ |- u ~*tm t ])
      (termRedR : [ Γ' |- u' ~*tm t' ])
    : [ Γ ≡ Γ' |- u ≡ u' ▷ A ≡whnf B ]

  | nfZero {Γ Γ'}
      (contWf : [ |- Γ ≡ Γ' ])
    : [ Γ ≡ Γ' |- tZero ≡whnf tZero ▷ tNat ≡whnf tNat ]
  | nfSucc {Γ Γ' t t'}
      (termWf : [ Γ ≡ Γ' |- t ≡ t' ▷ tNat ≡whnf tNat ])
    : [ Γ ≡ Γ' |- tSucc t ≡whnf tSucc t' ▷ tNat ≡whnf tNat ]
  | nfLambda {Γ Γ' Dom Dom' Cod Cod' t t'}
      (domWf : [ Γ ≡ Γ' |- Dom ≡ Dom' ])
      (bodyWf : [ Γ ,, Dom ≡ Γ' ,, Dom' |- t ≡ t' ▷ Cod ≡whnf Cod' ])
    : [ Γ ≡ Γ' |- tLambda Dom t ≡whnf tLambda Dom' t' ▷ tProd Dom Cod ≡whnf tProd Dom' Cod' ]
  | nfNeNat {Γ Γ' n n'}
      (neNat : [ Γ ≡ Γ' |- n ≡ne n' ▷red tNat ≡ tNat ])
    : [ Γ ≡ Γ' |- n ≡whnf n' ▷ tNat ≡whnf tNat ]

  | neReduces {Γ Γ' n n' A B A' B'}
      (neInfer : [ Γ ≡ Γ' |- n ≡ne n' ▷ A ≡ B ])
      (typeRedL : [ Γ |- A ~* A' ])
      (typeRedR : [ Γ' |- B ~* B' ])
    : [ Γ ≡ Γ' |- n ≡ne n' ▷red A' ≡ B' ]

  | neVar {Γ Γ' A B n}
      (contWf : [ |- Γ ≡ Γ' ])
      (in_ctxL : in_ctx Γ n A)
      (in_ctxR : in_ctx Γ' n B)
    : [ Γ ≡ Γ' |- tRel n ≡ne tRel n ▷ A ≡ B ]
  | neApp {Γ Γ' Dom Dom' Cod Cod' t t' u u'}
      (headNe : [ Γ ≡ Γ' |- t ≡ne t' ▷red tProd Dom Cod ≡ tProd Dom' Cod' ])
      (argChecks : [ Γ ≡ Γ' |- u ≡ u' ◁ Dom ≡ Dom' ])
      (resTypeWf : [ Γ ≡ Γ' |- Cod[u..] ≡ Cod'[u'..] ])
    : [ Γ ≡ Γ' |- tApp t u ≡ne tApp t' u' ▷ Cod[u..] ≡ Cod'[u'..] ]
  | neNatElim {Γ Γ' P P' hz hz' hs hs' t t'}
      (scrutNe : [ Γ ≡ Γ' |- t ≡ne t' ▷red tNat ≡ tNat ])
      (predWf : [ Γ ,, tNat ≡ Γ' ,, tNat |- P ≡ P' ])
      (hzChecks : [ Γ ≡ Γ' |- hz ≡ hz' ◁ P[tZero..] ≡ P'[tZero..] ])
      (hsChecks : [ Γ ≡ Γ' |- hs ≡ hs' ◁ tProd tNat P[(tSucc (tRel 0))]⇑ ≡ tProd tNat P'[(tSucc (tRel 0))]⇑ ])
      (resTypeWf : [ Γ ≡ Γ' |- P[t..] ≡ P'[t'..] ])
    : [ Γ ≡ Γ' |- tNatElim P hz hs t ≡ne tNatElim P' hz' hs' t' ▷ P[t..] ≡ P'[t'..] ]

  | redTyFromTm {Γ A B}
      (redAsTm : [ Γ |- A ~*tm B ])
    : [ Γ |- A ~* B ]

  | redBeta {Γ A B t u}
      (bodyInfers : [ Γ ,, A ≡ Γ ,, A |- t ≡ t ▷ B ≡whnf B ])
      (argChecks : [ Γ ≡ Γ |- u ≡ u ◁ A ≡ A ])
    : [ Γ |- tApp (tLambda A t) u ~>tm t[u..] ]
  | redNatElimZero {Γ P hz hs}
      (predWf : [ Γ ,, tNat ≡ Γ ,, tNat |- P ≡ P ])
      (hsChecks : [ Γ ≡ Γ |- hs ≡ hs ◁ tProd tNat P[(tSucc (tRel 0))]⇑ ≡ tProd tNat P[(tSucc (tRel 0))]⇑ ])
    : [ Γ |- tNatElim P hz hs tZero ~>tm hz ]
  | redNatElimSuc {Γ P hz hs t}
      (contWf : [ |- Γ ≡ Γ ])
    : [ Γ |- tNatElim P hz hs (tSucc t) ~>tm tApp hs (tNatElim P hz hs t) ]
  | redAppHead {Γ t t' u}
      (headReds : [ Γ |- t ~>tm t' ])
    : [ Γ |- tApp t u ~>tm tApp t' u ]
  | redNatElimScrut {Γ P hz hs t t'}
      (scrutReds : [ Γ |- t ~>tm t' ])
    : [ Γ |- tNatElim P hz hs t ~>tm tNatElim P hz hs t' ]

  | expandPi {Γ n Dom Cod}
      (neuExp : [ Γ ≡ Γ |- n ≡ne n ▷red tProd Dom Cod ≡ tProd Dom Cod ])
    : [ Γ |- n ↗ tLambda Dom (tApp n⟨↑⟩ (tRel 0)) ]

  | redTmNoEta {Γ t}
      (contWf : [ |- Γ ≡ Γ])
    : [ Γ |- t ~*tm t ]
  | redTmEta {Γ t u}
      (contWf : [ |- Γ ≡ Γ])
      (etaStep : [ Γ |- t ↗ u ])
    : [ Γ |- t ~*tm u ]
  | redTmStep {Γ t t' t''}
      (redStep : [ Γ |- t ~>tm t' ])
      (restRed : [ Γ |- t' ~*tm t'' ])
    : [ Γ |- t ~*tm t'' ]
  where "[ |- Γ ≡ Γ' ]" := (Paranoia ConvCont (Γ , Γ'))
    and "[ Γ ≡ Γ' |- A ≡ B ]" := (Paranoia ConvTy (Γ , Γ' , A , B))
    and "[ Γ ≡ Γ' |- A ≡whnf B ]" := (Paranoia ConvWhnfTy (Γ , Γ' , A , B))
    and "[ Γ ≡ Γ' |- t ≡ t' ◁ A ≡ B ]" := (Paranoia ConvCheckTm (Γ , Γ' , A , B , t , t'))
    and "[ Γ ≡ Γ' |- t ≡ t' ▷ A ≡whnf B ]" := (Paranoia ConvTm (Γ , Γ' , A , B , t , t'))
    and "[ Γ ≡ Γ' |- t ≡whnf t' ▷ A ≡whnf B ]" := (Paranoia ConvWhnfTm (Γ , Γ' , A , B , t , t'))
    and "[ Γ ≡ Γ' |- A ≡ne B ]" := (Paranoia ConvNeTy (Γ , Γ' , A , B))
    and "[ Γ ≡ Γ' |- t ≡ne t' '▷red' A ≡ B ]" := (Paranoia ConvNeRedTm (Γ , Γ' , A , B , t , t'))
    and "[ Γ ≡ Γ' |- t ≡ne t' ▷ A ≡ B ]" := (Paranoia ConvNeTm (Γ , Γ' , A , B , t , t'))
    and "[ Γ |- A ~* B ]" := (Paranoia RedTy (Γ , A , B))
    and "[ Γ |- t ↗ u ]" := (Paranoia ExpTmStep (Γ , t , u))
    and "[ Γ |- t ~>tm u ]" := (Paranoia RedTmStep (Γ , t , u))
    and "[ Γ |- t ~*tm u ]" := (Paranoia RedTm (Γ , t , u)).

Inductive Paranoiaε (Pred : forall {j : judgement} {i : judgement_indices j}, Paranoia j i -> Type)
  : forall {j : judgement} {i : judgement_indices j}, Paranoia j i -> Type :=
  | connilε :
      Paranoiaε (@Pred) connil
  | conconsε {Γ Γ' A B}
      {typeWf : [ Γ ≡ Γ' |- A ≡ B]}
      (typeWfε : Paranoiaε (@Pred) typeWf)
      (typeWfP : Pred typeWf)
    : Paranoiaε (@Pred) (concons typeWf)

  | normTyε {Γ Γ' A B A' B'}
      {typeWhnf : [ Γ ≡ Γ' |- A' ≡whnf B' ]}
      (typeWhnfε : Paranoiaε (@Pred) typeWhnf)
      (typeWhnfP : Pred typeWhnf)
      {typeRedL : [ Γ |- A ~* A' ]}
      (typeRedLε : Paranoiaε (@Pred) typeRedL)
      (typeRedLP : Pred typeRedL)
      {typeRedR : [ Γ' |- B ~* B' ]}
      (typeRedRε : Paranoiaε (@Pred) typeRedR)
      (typeRedRP : Pred typeRedR)
    : Paranoiaε (@Pred) (normTy typeWhnf typeRedL typeRedR)

  | nfNatε {Γ Γ'}
      {contWf : [ |- Γ ≡ Γ' ]}
      (contWfε : Paranoiaε (@Pred) contWf)
      (contWfP : Pred contWf)
    : Paranoiaε (@Pred) (nfNat contWf)
  | nfProdε {Γ Γ' Dom Dom' Cod Cod'}
      {DomWf : [ Γ ≡ Γ' |- Dom ≡ Dom' ]}
      (DomWfε : Paranoiaε (@Pred) DomWf)
      (DomWfP : Pred DomWf)
      {CodWf : [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ]}
      (CodWfε : Paranoiaε (@Pred) CodWf)
      (CodWfP : Pred CodWf)
    : Paranoiaε (@Pred) (nfProd DomWf CodWf)

  | checkε {Γ Γ' A B A' B' t t'}
      {termInfer : [ Γ ≡ Γ' |- t ≡ t' ▷ A ≡whnf B ]}
      (termInferε : Paranoiaε (@Pred) termInfer)
      (termInferP : Pred termInfer)
      {typeConvL : [ Γ ≡ Γ |- A' ≡ A ]}
      (typeConvLε : Paranoiaε (@Pred) typeConvL)
      (typeConvLP : Pred typeConvL)
      {typeConvR : [ Γ' ≡ Γ' |- B' ≡ B ]}
      (typeConvRε : Paranoiaε (@Pred) typeConvR)
      (typeConvRP : Pred typeConvR)
    : Paranoiaε (@Pred) (check termInfer typeConvL typeConvR)

  | normε {Γ Γ' A B t t' u u'}
      {termWhnfInfer : [ Γ ≡ Γ' |- t ≡whnf t' ▷ A ≡whnf B ]}
      (termWhnfInferε : Paranoiaε (@Pred) termWhnfInfer)
      (termWhnfInferP : Pred termWhnfInfer)
      {termRedL : [ Γ |- u ~*tm t ]}
      (termRedLε : Paranoiaε (@Pred) termRedL)
      (termRedLP : Pred termRedL)
      {termRedR : [ Γ' |- u' ~*tm t' ]}
      (termRedRε : Paranoiaε (@Pred) termRedR)
      (termRedRP : Pred termRedR)
    : Paranoiaε (@Pred) (norm termWhnfInfer termRedL termRedR)

  | nfZeroε {Γ Γ'}
      {contWf : [ |- Γ ≡ Γ' ]}
      (contWfε : Paranoiaε (@Pred) contWf)
      (contWfP : Pred contWf)
    : Paranoiaε (@Pred) (nfZero contWf)
  | nfSuccε {Γ Γ' t t'}
      {termWf : [ Γ ≡ Γ' |- t ≡ t' ▷ tNat ≡whnf tNat ]}
      (termWfε : Paranoiaε (@Pred) termWf)
      (termWfP : Pred termWf)
    : Paranoiaε (@Pred) (nfSucc termWf)
  | nfLambdaε {Γ Γ' Dom Dom' Cod Cod' t t'}
      {domWf : [ Γ ≡ Γ' |- Dom ≡ Dom' ]}
      (domWfε : Paranoiaε (@Pred) domWf)
      (domWfP : Pred domWf)
      {bodyWf : [ Γ ,, Dom ≡ Γ' ,, Dom' |- t ≡ t' ▷ Cod ≡whnf Cod' ]}
      (bodyWfε : Paranoiaε (@Pred) bodyWf)
      (bodyWfP : Pred bodyWf)
    : Paranoiaε (@Pred) (nfLambda domWf bodyWf)
  | nfNeNatε {Γ Γ' n n'}
      {neNat : [ Γ ≡ Γ' |- n ≡ne n' ▷red tNat ≡ tNat ]}
      (neNatε : Paranoiaε (@Pred) neNat)
      (neNatP : Pred neNat)
    : Paranoiaε (@Pred) (nfNeNat neNat)

  | neReducesε {Γ Γ' n n' A B A' B'}
      {neInfer : [ Γ ≡ Γ' |- n ≡ne n' ▷ A ≡ B ]}
      (neInferε : Paranoiaε (@Pred) neInfer)
      (neInferP : Pred neInfer)
      {typeRedL : [ Γ |- A ~* A' ]}
      (typeRedLε : Paranoiaε (@Pred) typeRedL)
      (typeRedLP : Pred typeRedL)
      {typeRedR : [ Γ' |- B ~* B' ]}
      (typeRedRε : Paranoiaε (@Pred) typeRedR)
      (typeRedRP : Pred typeRedR)
    : Paranoiaε (@Pred) (neReduces neInfer typeRedL typeRedR)

  | neVarε {Γ Γ' A B n}
      {contWf : [ |- Γ ≡ Γ' ]}
      (contWfε : Paranoiaε (@Pred) contWf)
      (contWfP : Pred contWf)
      {in_ctxL : in_ctx Γ n A}
      {in_ctxR : in_ctx Γ' n B}
    : Paranoiaε (@Pred) (neVar contWf in_ctxL in_ctxR)
  | neAppε {Γ Γ' Dom Dom' Cod Cod' t t' u u'}
      {headNe : [ Γ ≡ Γ' |- t ≡ne t' ▷red tProd Dom Cod ≡ tProd Dom' Cod' ]}
      (headNeε : Paranoiaε (@Pred) headNe)
      (headNeP : Pred headNe)
      {argChecks : [ Γ ≡ Γ' |- u ≡ u' ◁ Dom ≡ Dom' ]}
      (argChecksε : Paranoiaε (@Pred) argChecks)
      (argChecksP : Pred argChecks)
      {resTypeWf : [ Γ ≡ Γ' |- Cod[u..] ≡ Cod'[u'..] ]}
      (resTypeWfε : Paranoiaε (@Pred) resTypeWf)
      (resTypeWfP : Pred resTypeWf)
    : Paranoiaε (@Pred) (neApp headNe argChecks resTypeWf)
  | neNatElimε {Γ Γ' P P' hz hz' hs hs' t t'}
      {scrutNe : [ Γ ≡ Γ' |- t ≡ne t' ▷red tNat ≡ tNat ]}
      (scrutNeε : Paranoiaε (@Pred) scrutNe)
      (scrutNeP : Pred scrutNe)
      {predWf : [ Γ ,, tNat ≡ Γ' ,, tNat |- P ≡ P' ]}
      (predWfε : Paranoiaε (@Pred) predWf)
      (predWfP : Pred predWf)
      {hzChecks : [ Γ ≡ Γ' |- hz ≡ hz' ◁ P[tZero..] ≡ P'[tZero..] ]}
      (hzChecksε : Paranoiaε (@Pred) hzChecks)
      (hzChecksP : Pred hzChecks)
      {hsChecks : [ Γ ≡ Γ' |- hs ≡ hs' ◁ tProd tNat P[(tSucc (tRel 0))]⇑ ≡ tProd tNat P'[(tSucc (tRel 0))]⇑ ]}
      (hsChecksε : Paranoiaε (@Pred) hsChecks)
      (hsChecksP : Pred hsChecks)
      {resTypeWf : [ Γ ≡ Γ' |- P[t..] ≡ P'[t'..] ]}
      (resTypeWfε : Paranoiaε (@Pred) resTypeWf)
      (resTypeWfP : Pred resTypeWf)
    : Paranoiaε (@Pred) (neNatElim scrutNe predWf hzChecks hsChecks resTypeWf)

  | redTyFromTmε {Γ A B}
      {redAsTm : [ Γ |- A ~*tm B ]}
      (redAsTmε : Paranoiaε (@Pred) redAsTm)
      (redAsTmP : Pred redAsTm)
    : Paranoiaε (@Pred) (redTyFromTm redAsTm)

  | redBetaε {Γ A B t u}
      {bodyInfers : [ Γ ,, A ≡ Γ ,, A |- t ≡ t ▷ B ≡whnf B ]}
      (bodyInfersε : Paranoiaε (@Pred) bodyInfers)
      (bodyInfersP : Pred bodyInfers)
      {argChecks : [ Γ ≡ Γ |- u ≡ u ◁ A ≡ A ]}
      (argChecksε : Paranoiaε (@Pred) argChecks)
      (argChecksP : Pred argChecks)
    : Paranoiaε (@Pred) (redBeta bodyInfers argChecks)
  | redNatElimZeroε {Γ P hz hs}
      {predWf : [ Γ ,, tNat ≡ Γ ,, tNat |- P ≡ P ]}
      (predWfε : Paranoiaε (@Pred) predWf)
      (predWfP : Pred predWf)
      {hsChecks : [ Γ ≡ Γ |- hs ≡ hs ◁ tProd tNat P[(tSucc (tRel 0))]⇑ ≡ tProd tNat P[(tSucc (tRel 0))]⇑ ]}
      (hsChecksε : Paranoiaε (@Pred) hsChecks)
      (hsChecksP : Pred hsChecks)
    : Paranoiaε (@Pred) (redNatElimZero (hz := hz) predWf hsChecks)
  | redNatElimSucε {Γ P hz hs t}
      {contWf : [ |- Γ ≡ Γ ]}
      (contWfε : Paranoiaε (@Pred) contWf)
      (contWfP : Pred contWf)
    : Paranoiaε (@Pred) (@redNatElimSuc Γ P hz hs t contWf)
  | redAppHeadε {Γ t t' u}
      {headReds : [ Γ |- t ~>tm t' ]}
      (headRedsε : Paranoiaε (@Pred) headReds)
      (headRedsP : Pred headReds)
    : Paranoiaε (@Pred) (redAppHead (u := u) headReds)
  | redNatElimScrutε {Γ P hz hs t t'}
      {scrutReds : [ Γ |- t ~>tm t' ]}
      (scrutRedsε : Paranoiaε (@Pred) scrutReds)
      (scrutRedsP : Pred scrutReds)
    : Paranoiaε (@Pred) (redNatElimScrut (P := P) (hz := hz) (hs := hs) scrutReds)

  | expandPiε {Γ n Dom Cod}
      {neuExp : [ Γ ≡ Γ |- n ≡ne n ▷red tProd Dom Cod ≡ tProd Dom Cod ]}
      (neuExpε : Paranoiaε (@Pred) neuExp)
      (neuExpP : Pred neuExp)
    : Paranoiaε (@Pred) (expandPi neuExp)

  | redTmNoEtaε {Γ t}
      {contWf : [ |- Γ ≡ Γ]}
      (contWfε : Paranoiaε (@Pred) contWf)
      (contWfP : Pred contWf)
    : Paranoiaε (@Pred) (redTmNoEta (t := t) contWf)
  | redTmEtaε {Γ t u}
      {contWf : [ |- Γ ≡ Γ]}
      (contWfε : Paranoiaε (@Pred) contWf)
      (contWfP : Pred contWf)
      {etaStep : [ Γ |- t ↗ u ]}
      (etaStepε : Paranoiaε (@Pred) etaStep)
      (etaStepP : Pred etaStep)
    : Paranoiaε (@Pred) (redTmEta contWf etaStep)
  | redTmStepε {Γ t t' t''}
      {redStep : [ Γ |- t ~>tm t' ]}
      (redStepε : Paranoiaε (@Pred) redStep)
      (redStepP : Pred redStep)
      {restRed : [ Γ |- t' ~*tm t'' ]}
      (restRedε : Paranoiaε (@Pred) restRed)
      (restRedP : Pred restRed)
    : Paranoiaε (@Pred) (redTmStep redStep restRed).

Derive Signature for Paranoia Paranoiaε.

Definition ParanoiaElim (P : forall {j : judgement} {i : judgement_indices j}, Paranoia j i -> Type)
  (H : forall {j i} {g : Paranoia j i}, Paranoiaε (@P) g -> P g)
  {j i}
  (g : Paranoia j i) : P g.
Proof.
  apply H.
  revert j i g.
  ltac1:(fix frel 3).
  intros.
  destruct g.
  all: econstructor.
  all: eauto.
Defined.

Definition ParanoiaToε {P : forall {j : judgement} {i : judgement_indices j}, Paranoia j i -> Type}
  (H : forall {j i} (g : Paranoia j i), P g)
  {j i} (g : Paranoia j i)
  : Paranoiaε (@P) g.
Proof.
  induction g.
  econstructor.
  eauto.
Defined.

Definition SwapIndices {j} : judgement_indices j -> judgement_indices j :=
  match j as j return (judgement_indices j -> judgement_indices j) with
  | ConvCont => fun '(Γ, Γ') => (Γ', Γ)
  | ConvTy | ConvWhnfTy | ConvNeTy
    => fun '(Γ, Γ', A, B) => (Γ', Γ, B, A)
  | ConvCheckTm | ConvTm | ConvWhnfTm | ConvNeRedTm | ConvNeTm
    => fun '(Γ, Γ', A, B, t, u) => (Γ', Γ, B, A, u, t)
  | RedTy | RedTmStep | ExpTmStep | RedTm
    => id
  end.

Definition ParanoiaSymmType j i : Type :=
  match j with
  | RedTy | RedTmStep | ExpTmStep | RedTm => unit
  | _ => Paranoia j (SwapIndices i)
  end.

Lemma ParanoiaSymm j i : Paranoia j i -> ParanoiaSymmType j i.
Proof.
  induction 1 using ParanoiaElim.
  depelim X; econstructor; eauto.
Defined.

Definition ProjLIndices {j} : judgement_indices j -> judgement_indices j :=
  match j as j return (judgement_indices j -> judgement_indices j) with
  | ConvCont => fun '(Γ, _) => (Γ, Γ)
  | ConvTy | ConvWhnfTy | ConvNeTy
    => fun '(Γ, _, A, _) => (Γ, Γ, A, A)
  | ConvCheckTm | ConvTm | ConvWhnfTm | ConvNeRedTm | ConvNeTm
    => fun '(Γ, _, A, _, t, _) => (Γ, Γ, A, A, t, t)
  | RedTy | RedTmStep | ExpTmStep | RedTm
    => id
  end.

Definition ParanoiaLeftType j i : Type :=
  match j with
  | RedTy | RedTmStep | ExpTmStep | RedTm => unit
  | _ => Paranoia j (ProjLIndices i)
  end.

Lemma ParanoiaLeft j i : Paranoia j i -> ParanoiaLeftType j i.
Proof.
  induction 1 using ParanoiaElim.
  depelim X; econstructor; eauto.
Defined.

Definition ParanoiaGetCont {j} (i : judgement_indices j) : context × context :=
  (match j as j return (judgement_indices j -> context × context) with
  | ConvCont => fun '(Γ, Γ') => (Γ , Γ')
  | ConvTy | ConvWhnfTy | ConvNeTy
    => fun '(Γ, Γ', A, B) => (Γ , Γ')
  | ConvCheckTm | ConvTm | ConvWhnfTm | ConvNeRedTm | ConvNeTm
    => fun '(Γ, Γ', A, B, t, u) => (Γ , Γ')
  | RedTy | RedTmStep | ExpTmStep | RedTm
    => fun '(Γ, _, _) => (Γ , Γ)
  end) i.

Definition ParanoiaConvContType (j : judgement) (i : judgement_indices j) : Type :=
  Paranoia ConvCont (ParanoiaGetCont i).

Lemma Conv_ConvCont j {i} : Paranoia j i -> ParanoiaConvContType j i.
Proof.
  induction 1 using ParanoiaElim.
  depelim X.
  repeat (assumption || constructor).
Defined.

Lemma Conv_ConvContε {P : forall {j i}, Paranoia j i -> Type} {j i}
  {H : Paranoia j i}
  (Hε : Paranoiaε (@P) H)
  (HP : P H)
  : Paranoiaε (@P) (Conv_ConvCont j H).
Proof.
  revert HP.
  induction Hε.
  intros HP.
  1-2: constructor.
  eauto.
Defined.

Lemma Conv_ConvContP {P : forall {j i}, Paranoia j i -> Type} {j i}
  {H : Paranoia j i}
  (Hε : Paranoiaε (@P) H)
  (HP : P H)
  : P (Conv_ConvCont j H).
Proof.
  revert HP.
  induction Hε.
  intros HP.
  eauto.
Defined.

Instance Ren_nat_nat : Ren1 (nat -> nat) nat nat := fun f n => f n.

Lemma substRen {t u ρ} : t[u..]⟨ρ⟩ = t⟨upRen_term_term ρ⟩[u⟨ρ⟩..].
Proof.
  ltac1:(asimpl).
  reflexivity.
Defined.

Lemma shiftScons {t : term} {n ρ} : t⟨↑⟩⟨n .: ρ⟩ = t⟨ρ⟩.
Proof.
  ltac1:(asimpl).
  reflexivity.
Defined.

Lemma substUp {t u ρ} : t⟨upRen_term_term ρ⟩[u⟨upRen_term_term ρ⟩]⇑ = t[u]⇑⟨upRen_term_term ρ⟩.
Proof.
  ltac1:(asimpl).
  reflexivity.
Defined.

Ltac2 myautosubst_tac () :=
  cbn delta [ren1 Ren_term ren_term Ren_nat_nat upRen_term_term up_ren scons] beta iota in *;
  rewrite <- ?shift_upRen, -> ?substRen, -> ?shiftScons in * |- *.

Ltac2 iter_hypo (f : ident -> unit) := match! goal with [ h : _ |- _] => f h end.

Definition RenStableIndices Δ Δ' (ρ : nat -> nat) {j} : judgement_indices j -> judgement_indices j :=
  match j as j return (judgement_indices j -> judgement_indices j) with
  | ConvCont => fun '(_, _) => (Δ, Δ')
  | ConvTy | ConvWhnfTy | ConvNeTy
    => fun '(_, _, A, B) => (Δ, Δ', A⟨ρ⟩, B⟨ρ⟩)
  | ConvCheckTm | ConvTm | ConvWhnfTm | ConvNeRedTm | ConvNeTm
    => fun '(_, _, A, B, t, u) => (Δ, Δ', A⟨ρ⟩, B⟨ρ⟩, t⟨ρ⟩, u⟨ρ⟩)
  | RedTy | RedTmStep | ExpTmStep | RedTm
    => fun '(_, t, u) => (Δ, t⟨ρ⟩, u⟨ρ⟩)
  end.

Definition RenStableType {j i} (_ : Paranoia j i) : Type :=
  match j with
  | ConvCont
  | ConvTy | ConvWhnfTy | ConvNeTy
  | ConvCheckTm | ConvTm | ConvWhnfTm | ConvNeRedTm | ConvNeTm
    => let '(Γ, Γ') := ParanoiaGetCont i in
      forall Δ Δ' ρ,
      [ |- Δ ≡ Δ' ] -> renames Δ ρ Γ -> renames Δ' ρ Γ'
      -> Paranoia j (RenStableIndices Δ Δ' ρ i)
  | RedTy | RedTmStep | ExpTmStep | RedTm
    => let '(Γ, _) := ParanoiaGetCont i in
      forall Δ ρ,
      [ |- Δ ≡ Δ ] -> renames Δ ρ Γ
      -> Paranoia j (RenStableIndices Δ Δ ρ i)
  end.

Ltac2 any (tacs : (unit -> unit) list) : unit :=
  List.fold_left (fun a t () => Control.plus a (fun _ => t ())) fail0 tacs ().

Ltac2 rec expandprodevars c :=
  lazy_match! c with
  | _ × ?b => let left := expandprodevars b in '((_ , $left ))
  | _ => '_
  end.

Ltac2 eapplyI0 (c : constr) : unit :=
  let s := Env.get [@LogRel; @Paranoia; @judgement] in
  let ref := match s with | Some (Std.IndRef i) => i | _ => Control.throw Assertion_failure end
  in
  let data := Ind.data ref
  in
  let instance := match Constr.Unsafe.kind (Env.instantiate (Std.IndRef ref)) with
    | Constr.Unsafe.Ind _ i => i
    | _ => Control.throw Assertion_failure end
  in
  let blocks := List.map (fun i => Ind.get_block data i) (List.init (Ind.nblocks data) (fun i => i))
  in
  let constructors :=
    List.concat
      (List.map (fun block => List.map (fun i => Ind.get_constructor block i) (List.init (Ind.nconstructors block) (fun i => i))) blocks)
  in
  let constrs := List.map (fun c => Constr.Unsafe.make (Constr.Unsafe.Constructor c instance)) constructors
  in
  let f constr :=
    let normty := eval cbn in (judgement_indices $constr)
    in
    let expanded := expandprodevars normty
    in
    let res := '($c $constr $expanded)
    in (eapply $res)
  in
  let tacs := List.map (fun constr () => f constr) constrs
  in (any (tacs)).

Ltac2 Notation "eapplyI" c(constr) := eapplyI0 c.

(* Lemmas *)
Lemma RenStable j {i} (p : Paranoia j i) : RenStableType p.
Proof.
  induction p using ParanoiaElim.
  depelim X.
  cbn delta [RenStableType RenStableIndices ParanoiaGetCont] iota beta in *.
  intros **.
  1-2: eassumption.

  myautosubst_tac ().

  (* Use resp. each constructor of the mind block  *)
  let s := Env.get [@LogRel; @Paranoia; @Paranoia] in
  let ref := match s with | Some (Std.IndRef i) => i | _ => Control.throw Assertion_failure end
  in
  let data := Ind.data ref
  in
  let instance := match Constr.Unsafe.kind (Env.instantiate (Std.IndRef ref)) with
    | Constr.Unsafe.Ind _ i => i
    | _ => Control.throw Assertion_failure end
  in
  let blocks := List.map (fun i => Ind.get_block data i) (List.init (Ind.nblocks data) (fun i => i))
  in
  let constructors :=
    List.concat
      (List.map (fun block => List.map (fun i => Ind.get_constructor block i) (List.init (Ind.nconstructors block) (fun i => i))) blocks)
  in
  let constrs := List.map (fun c => Constr.Unsafe.make (Constr.Unsafe.Constructor c instance)) constructors
  in
  let tacs := List.map (fun constr () => eapply $constr) constrs
  in Control.dispatch (List.skipn 2 tacs).
  > lazy_match! goal with
    | [ |- in_ctx _ _ _ ] => eauto using VarRen
    | [ |- _] => ()
    end.

  try (ltac1:(change (?a ⟨upRen_term_term ρ⟩[?b ..]) with (a ⟨upRen_term_term ρ⟩[b⟨ρ⟩ ..]))).
  try (ltac1:(change (?a ⟨upRen_term_term ρ⟩[?b]⇑) with (a ⟨upRen_term_term ρ⟩[b⟨upRen_term_term ρ⟩]⇑))).
  rewrite <- ?substRen, -> ?substUp.

  try (once (repeat (> iter_hypo (fun h => let h := Control.hyp h in eapply $h) || (eapplyI ParanoiaLeft; now (() + eapplyI ParanoiaSymm)) || econstructor || eapply RenWeakenOnce || (ltac1:(change (↑ >> upRen_term_term ?ρ) with (ρ >> ↑)); rewrite <- (renRen_term _ ↑)))); >fail).
  - apply bodyInfersP.
    + econstructor.
      (* XXX: Why would I need to manually add three metas here? *)
      assert (U : _) by (now eapply (argChecksP _ _ _)).
      depelim U.
      now eapplyI ParanoiaLeft.
    + econstructor.
      ltac1:(change (↑ >> upRen_term_term ?ρ) with (ρ >> ↑)).
      * now eapply RenWeakenOnce.
      * rewrite <- (renRen_term _ ↑). econstructor.
    + econstructor.
      ltac1:(change (↑ >> upRen_term_term ?ρ) with (ρ >> ↑)).
      * now eapply RenWeakenOnce.
      * rewrite <- (renRen_term _ ↑). econstructor.
Defined.

Definition GetVarTypedType (j : judgement) : judgement_indices j -> Type :=
  match j with
  | ConvCont => fun '(Γ, Γ') => forall n A B, in_ctx Γ n A -> in_ctx Γ' n B -> [ Γ ≡ Γ' |- A ≡ B ]
  | _ => fun _ => unit
  end.

Lemma GetVarTyped j {i} : Paranoia j i -> GetVarTypedType j i .
Proof.
  induction 1 using ParanoiaElim.
  depelim X.
  unfold GetVarTypedType.
  try (exact tt).
  1-2: intros ?**.
  - depelim H.
  - depelim H; depelim H0.
    + eapplyI RenStable > [eassumption | econstructor; eassumption | | ]; eapply RenWeakenOnce; eapply RenId.
    + assert (contP : _) by (now eapply (Conv_ConvContP X)).
      eapplyI RenStable > [now eapply contP | now econstructor | |].
      eapply RenWeakenOnce.
      eapply RenId.
Defined.

(* Definition ReductionPreservesWfType (j : judgement) : judgement_indices j -> Type :=
 *   match j with
 *   | RedTy => fun '(Γ , A , B) => [ Γ ≡ Γ |- A ≡ A ] -> [ Γ ≡ Γ |- B ≡ B ]
 *   | RedTm | RedTmStep | ExpTmStep => fun '(Γ , t , u) =>
 *     forall A, [ Γ ≡ Γ |- t ≡ t ▷ A ≡whnf A] -> [ Γ ≡ Γ |- u ≡ u ▷ A ≡whnf A]
 *   | _ => fun _ => unit
 *   end.
 * 
 * Lemma ReductionPreservesWf j {i} : Paranoia j i -> ReductionPreservesWfType j i.
 * Proof.
 *   induction 1 using ParanoiaElim.
 *   depelim X.
 *   unfold ReductionPreservesWfType.
 *   try (exact tt). *)


Definition WellTypedType (j : judgement) : judgement_indices j -> Type :=
  match j with
  | ConvTm | ConvWhnfTm => fun '(Γ, Γ', A, B, _, _) => [ Γ ≡ Γ' |- A ≡whnf B ]
  | ConvNeTm  => fun '(Γ, Γ', A, B, _, _) => [ Γ ≡ Γ' |- A ≡ B ]
  | _ => fun _ => unit
  end.

Lemma WellTyped j {i} : Paranoia j i -> WellTypedType j i.
Proof.
  induction 1 using ParanoiaElim.
  depelim X.
  unfold WellTypedType.
  try (exact tt).
  try eauto.
  - now econstructor.
  - (econstructor) > [ eassumption | ].
    (econstructor) > [eapply bodyWfP | | ].
    econstructor. econstructor. econstructor.
    + now eapplyI ParanoiaLeft.
    + eapplyI ParanoiaLeft; now eapplyI ParanoiaSymm.
  - econstructor.
    now eapplyI Conv_ConvCont.
  - now eapplyI GetVarTyped.
Defined.

Section Determinism.

Definition introTypeb (t : term) : bool :=
  match t with
  | tNat
  | tProd _ _ => true
  | _ => false
  end.

Definition introTermb (t : term) : bool :=
  match t with
  | tZero
  | tSucc _
  | tLambda _ _ => true
  | _ => false
  end.

Lemma introTyDoesntReduce {Γ A B} :
  introTypeb A = true
  -> [ Γ |- A ~* B ]
  -> A = B.
Proof.
  intros.
  destruct A.
  noconf H.
  depelim H0.
  depelim H0 > [reflexivity| depelim H0_0; depelim H0_0; depelim H0_0_1 | depelim H0_].
Defined.

Lemma introTmDoesntReduce {Γ t u} :
  introTermb t = true
  -> [ Γ |- t ~*tm u ]
  -> t = u.
Proof.
  intros.
  destruct t.
  noconf H.
  depelim H0 > [reflexivity| depelim H0_0; depelim H0_0; depelim H0_0_1 | depelim H0_].
Defined.

Lemma introTyToWhnf {Γ Γ' A B} :
  introTypeb A = true
  -> introTypeb B = true
  -> [ Γ ≡ Γ' |- A ≡ B ]
  -> [ Γ ≡ Γ' |- A ≡whnf B ].
Proof.
  intros ? ? wf.
  depelim wf.
  apply introTyDoesntReduce in wf2 > [| assumption ].
  apply introTyDoesntReduce in wf3 > [| assumption ].
  subst.
  assumption.
Defined.

Lemma introTmToWhnf {Γ Γ' t u A B} :
  introTermb t = true
  -> introTermb u = true
  -> [ Γ ≡ Γ' |- t ≡ u ▷ A ≡whnf B ]
  -> [ Γ ≡ Γ' |- t ≡whnf u ▷ A ≡whnf B ].
Proof.
  intros ? ? wf.
  depelim wf.
  apply introTmDoesntReduce in wf2 > [| assumption ].
  apply introTmDoesntReduce in wf3 > [| assumption ].
  subst.
  assumption.
Defined.

Lemma introTmNoNe {Γ Γ' t u A B} :
  introTermb t = true
  -> [ Γ ≡ Γ' |- t ≡ne u ▷ A ≡ B ]
  -> False.
Proof.
  intros isintro ne.
  depelim ne.
  noconf isintro.
Defined.


Definition NoConfRedType (j : judgement) : judgement_indices j -> Type :=
  match j with
  | RedTmStep => fun '(Γ , t , u) =>
    forall A, [ Γ ≡ Γ |- t ≡ne t ▷ A ≡ A ] -> False
  | _ => fun _ => unit
  end.

Lemma NoConfRed {Γ t u A} : [ Γ |- t ~>tm u ] -> [ Γ ≡ Γ |- t ≡ne t ▷ A ≡ A ] -> False.
Proof.
  intro H.
  revert A.
  change _ with (NoConfRedType RedTmStep (Γ , t , u)).
  induction H using ParanoiaElim.
  depelim X.
  ltac1:(simpl NoConfRedType in * ).
  try (exact tt).
  intros ? H.
  depelim H.
  depelim H.
  try (depelim H; > fail).
  eapply ParanoiaLeft in H.
  eauto.
Defined.

Definition RedStepDetType (j : judgement) : judgement_indices j -> Type :=
  match j with
  | RedTmStep => fun '(Γ , t , u) =>
    forall v, [ Γ |- t ~>tm v ] -> v = u
  | _ => fun _ => unit
  end.

Lemma RedStepDet {Γ t u v} : [ Γ |- t ~>tm u ] -> [ Γ |- t ~>tm v ] -> v = u.
Proof.
  intros H1.
  revert v.
  change _ with (RedStepDetType RedTmStep (Γ , t , u)).
  induction H1 using ParanoiaElim.
  depelim X.
  ltac1:(simpl RedStepDetType).
  try (exact tt).
  intros v H2.
  depelim H2.
  try (match! goal with | [ h : [ _ |- _ ~>tm _ ] |- _ ] => depelim $h; > fail end).
  f_equal.
  eauto.
Defined.

Definition DeterminismP j : forall (i : judgement_indices j), Paranoia j i -> Type :=
  match j with
  | ConvTm => fun '(Γ , Γ' , A , B , t , u) _ =>
    forall C, [ Γ ≡ Γ |- t ≡ t ▷ C ≡whnf C ] -> C = A
  | ConvWhnfTm => fun '(Γ , Γ' , A , B , t , u) _ =>
    (forall C, [ Γ ≡ Γ |- t ≡whnf t ▷ C ≡whnf C ] -> C = A)
  | ConvNeTm => fun '(Γ , Γ' , A , B , t , u) _ =>
    forall C, [ Γ ≡ Γ |- t ≡ne t ▷ C ≡ C ] -> C = A
  | RedTy => fun '(Γ , A , B) _ => forall C,
      [ Γ |- A ~* C ]
      -> [ Γ |- B ~* C ]
      + [ Γ |- C ~* B ]
  | _ => fun _ _ => unit
  end.

Definition redTmFactor_motive j : forall (i : judgement_indices j), Paranoia j i -> Type :=
  match j with
  | RedTm => fun '(Γ , t , u) _ =>
    forall v,  [ Γ |- t ~*tm v ]
  -> [ Γ |- u ~*tm v ]
  + ∑ (H' : [ Γ |- v ~*tm u ]), Paranoiaε DeterminismP H'
  | _ => fun _ _ => unit
  end.

Lemma redTmFactor_pre {Γ t u v} : forall (H : [ Γ |- t ~*tm u ]),
     Paranoiaε DeterminismP H
  -> [ Γ |- t ~*tm v ]
  -> [ Γ |- u ~*tm v ]
  + ∑ (H' : [ Γ |- v ~*tm u ]), Paranoiaε DeterminismP H'.
Proof.
  intros redu Hε.
  revert v.
  change _ with (redTmFactor_motive RedTm _ redu).
  induction Hε.
  ltac1:(simpl redTmFactor_motive in * ).
  try (exact tt).
  intros v redv.
  - now left.
  - depelim redv.
    * right. esplit. now econstructor.
    * depelim Hε2. cbn in H. noconf H.
      depelim Hε2. cbn in H. noconf H.
      depelim redv2. depelim redv2.
      apply ParanoiaLeft in redv2_1.
      rewrite (neInferP A0) in * by assumption.
      apply typeRedLP in redv2_2.
      destruct redv2_2 as [badred|badred].
      eapply introTyDoesntReduce in badred > [|reflexivity].
      noconf badred.
      right. esplit. now econstructor.
    * depelim etaStep. depelim etaStep.
      clear Hε2 etaStepP.
      apply ParanoiaLeft in etaStep1.
      now eapply NoConfRed in redv1.
  - depelim redv.
    * right. esplit. now econstructor.
    * depelim redv2. depelim redv2.
      apply ParanoiaLeft in redv2_1.
      clear Hε1 redStepP.
      now eapply NoConfRed in redStep.
    * rewrite (RedStepDet redStep redv1) in *.
      now apply IHHε2.
Defined.

Lemma redTyFactor_pre {Γ A B C} : forall (H : [ Γ |- A ~* B ]),
     Paranoiaε DeterminismP H
  -> [ Γ |- A ~* C ]
  -> [ Γ |- B ~* C ]
  + ∑ (H' : [ Γ |- C ~* B ]), Paranoiaε DeterminismP H'.
Proof.
  intros redB redBε redC.
  depelim redBε. cbn in H. noconf H.
  depelim redC.
  eapply redTmFactor_pre in redC > [|eassumption].
  destruct redC as [redC|(redC & redCε)].
  - left. now constructor.
  - right. esplit. now econstructor.
Defined.

Lemma whnfTyNoRed_pre {Γ Γ' A B C} :
    forall (H : [ Γ ≡ Γ' |- A ≡whnf B ]),
    Paranoiaε DeterminismP H
 -> [ Γ |- A ~* C ]
 -> C = A.
Proof.
  intros isWhnf isWhnfε redv.
  depelim isWhnfε. cbn in H. noconf H.
  try (exact tt).
  - depelim redv. depelim redv > [reflexivity| depelim redv2 |depelim redv1].
    depelim redv2. depelim redv2_1.
  - depelim redv. depelim redv > [reflexivity| depelim redv2 |depelim redv1].
    depelim redv2. depelim redv2_1.
Defined.

Lemma whnfTyNoRed2_pre {Γ Γ' A B} :
    forall (H : [ Γ |- A ~* B ]),
    Paranoiaε DeterminismP H
 -> [ Γ ≡ Γ' |- A ≡whnf B ]
 -> B = A.
Proof.
  intros redB redBε isWhnf.
  depelim isWhnf.
  try (exact tt).
  - depelim redBε. cbn in H. noconf H.
    (depelim redBε; cbn in H; noconf H) > [reflexivity| depelim redBε2; cbn in H; noconf H |depelim redBε1; cbn in H; noconf H].
  - depelim redBε. cbn in H. noconf H.
    (depelim redBε; cbn in H; noconf H) > [reflexivity| depelim redBε2; cbn in H; noconf H |depelim redBε1; cbn in H; noconf H].
Defined.

Lemma whnfTmNoRed_pre {Γ Γ' A B t u v} :
    forall (H : [ Γ ≡ Γ' |- t ≡whnf u ▷ A ≡whnf B ]),
    Paranoiaε DeterminismP H
 -> [ Γ |- t ~*tm v ]
 -> v = t.
Proof.
  intros isWhnf isWhnfε redv.
  depelim isWhnfε. cbn in H. noconf H.
  try (depelim redv > [reflexivity| | depelim redv1 ]; depelim redv2; depelim redv2; depelim redv2_1; > fail).
  depelim redv
  > [reflexivity| | depelim neNat; eapply NoConfRed in redv1 > [|now eapplyI ParanoiaLeft]; destruct redv1].
  depelim redv2.
  depelim isWhnfε. cbn in H. noconf H.
  depelim redv2.
  apply ParanoiaLeft in redv2_1.
  apply neInferP in redv2_1.
  noconf redv2_1.
  eapply redTyFactor_pre in redv2_2 > [|eassumption].
  destruct redv2_2 as [badred|(badred & badredε)].
  - depelim badred. depelim badred.
    * depelim badred2.
    * depelim badred1.
  - clear badredε.
    depelim badred.
    depelim badred.
    * depelim badred2.
    * depelim badred1.
Defined.

Lemma whnfTmNoRed2_pre {Γ Γ' A B t u v} :
    forall (H : [ Γ |- t ~*tm v ]),
    Paranoiaε DeterminismP H
 -> [ Γ ≡ Γ' |- t ≡whnf u ▷ A ≡whnf B ]
 -> v = t.
Proof.
  intros redv redvε isWhnf.
  depelim isWhnf.
  try (depelim redv > [reflexivity| | depelim redv1 ]; depelim redv2; depelim redv2; depelim redv2_1; > fail).
  (depelim redvε ; cbn in H ; noconf H)
  > [reflexivity| | clear redvε1 redStepP; depelim isWhnf; eapply NoConfRed in redStep > [|now eapplyI ParanoiaLeft]; destruct redStep].
  depelim redvε2. cbn in H. noconf H.
  depelim isWhnf.
  depelim redvε2. cbn in H. noconf H.
  apply ParanoiaLeft in isWhnf1.
  apply neInferP in isWhnf1.
  noconf isWhnf1.
  eapply redTyFactor_pre in isWhnf2 > [|eassumption].
  destruct isWhnf2 as [badred|(badred & badredε)].
  - depelim badred. depelim badred.
    * depelim badred2.
    * depelim badred1.
  - clear badredε.
    depelim badred.
    depelim badred.
    * depelim badred2.
    * depelim badred1.
Defined.

Lemma inferRedIntro {Γ Γ' A B C t u} :
    forall
      (H : [ Γ ≡ Γ' |- t ≡ne u ▷red A ≡ B ]),
    Paranoiaε DeterminismP H
 -> introTypeb A = true
 -> [ Γ ≡ Γ |- t ≡ne t ▷red C ≡ C ]
 -> ∑ (H' : [ Γ |- C ~* A ]), Paranoiaε DeterminismP H'.
 intros neRed neRedε discr neRed'.
 depelim neRedε. cbn in H. noconf H.
 depelim neRed'.
 apply ParanoiaLeft in neRed'1.
 apply neInferP in neRed'1.
 noconf neRed'1.
 eapply redTyFactor_pre in neRed'2 > [|eassumption].
 destruct neRed'2 as [reds|(reds & redsε)].
 - eapply introTyDoesntReduce in reds > [|assumption].
   noconf reds.
   esplit. (econstructor) > [ | econstructor ]. econstructor.
   1: now eapply (Conv_ConvContε neRedε2).
   1: now eapply (Conv_ConvContP neRedε2).
 - depelim redsε. cbn in H. noconf H.
   esplit. econstructor. eassumption.
Defined.


Lemma Determinism j {i} (p : Paranoia j i) : DeterminismP j i p.
Proof.
  induction p using ParanoiaElim.
  depelim X.
  ltac1:(simpl DeterminismP in * ).
  try (exact tt).
  intros **.
  - depelim H.
    apply termWhnfInferP.
    eapply redTmFactor_pre in H0 > [| eassumption].
    assert (t0eqt : t0 = t).
    {destruct H0 as [nored|(nored & noredε)].
      * eapply whnfTmNoRed_pre in nored > [|eassumption].
        assumption.
      * eapply whnfTmNoRed2_pre in noredε > [|eassumption].
        symmetry. assumption.
    }
    noconf t0eqt.
    apply ParanoiaLeft in H.
    assumption.
  - depelim H > [reflexivity|].
    depelim H. depelim H.
  - depelim H > [reflexivity|].
    depelim H. depelim H.
  - depelim H > [f_equal ; eauto|].
    depelim H. depelim H.
  - depelim X. cbn in H. noconf H.
    depelim H0.
    try (depelim neInfer; > fail).
    depelim H0.
    apply ParanoiaLeft in H0_.
    apply neInferP in H0_.
    noconf H0_.
    eapply redTyFactor_pre in H0_0 > [|eassumption].
    destruct H0_0 as [nored|(nored & noredε)].
    * eapply whnfTyNoRed_pre in nored > [|econstructor].
      2: now eapply (Conv_ConvContε X1).
      2: now eapply (Conv_ConvContP X1).
      assumption.
    * eapply whnfTyNoRed2_pre in noredε > [|econstructor; now eapplyI Conv_ConvCont].
      symmetry. assumption.
  - depelim H.
    now eapply in_ctx_inj.
  - depelim H.
    apply ParanoiaLeft in H.
    eapply inferRedIntro in H > [| eassumption | reflexivity].
    destruct H as (reds & _).
    eapply introTyDoesntReduce in reds > [|reflexivity].
    noconf reds. reflexivity.
  - depelim H.
    apply ParanoiaLeft in H.
    eapply inferRedIntro in H > [| eassumption | reflexivity].
    destruct H as (reds & _).
    eapply introTyDoesntReduce in reds > [|reflexivity].
    noconf reds. reflexivity.
  - eapply redTyFactor_pre in H > [| econstructor; eassumption].
    destruct H as [reds| (reds & _)].
    * left. assumption.
    * right. assumption.
Defined.

Definition CannotRed Γ t := forall u, ([ Γ |- t ~>tm u ] -> False) × ([ Γ |- t ↗ u ] -> False).

Lemma whnfTyNoRed {Γ Γ' A B} :
    [ Γ ≡ Γ' |- A ≡whnf B ]
 -> CannotRed Γ A.
Proof.
  intros H1 u.
  split.
  - intro H2.
    depelim H2.
    depelim H1.
  - intro H2.
    depelim H2.
    depelim H1.
    depelim H2. depelim H2_.
Defined.

Lemma introTyNoRed {Γ A} :
    introTypeb A = true
 -> CannotRed Γ A.
Proof.
  intros Aintro B.
  split.
  intros H.
  depelim A.
  noconf Aintro.
  depelim H.
  depelim H.
  depelim H.
Defined.

Lemma cannotRedTyEq {Γ A B} :
    CannotRed Γ A
 -> [ Γ |- A ~* B ]
 -> B = A.
Proof.
  intros cannot H.
  depelim H.
  depelim H.
  - reflexivity.
  - apply cannot in H0. destruct H0.
  - apply cannot in H. destruct H.
Defined.

Lemma redTyFactor {Γ A B C} :
     [Γ |- A ~* B ]
  -> [Γ |- A ~* C ]
  -> [Γ |- B ~* C ] + [ Γ |- C ~* B ].
Proof.
  intros H1 H2.
  assert (H1ε : Paranoiaε DeterminismP H1) by (apply ParanoiaToε ; apply Determinism).
  assert (res : _) by (now eapply redTyFactor_pre).
  destruct res as [res|(res & _)].
  - left. exact res.
  - right. exact res.
Defined.

Lemma redTyDet {Γ A} B C :
     [Γ |- A ~* B ]
  -> [Γ |- A ~* C ]
  -> CannotRed Γ B
  -> CannotRed Γ C
  -> C = B.
Proof.
  intros H1 H2 Bwhnf Cwhnf.
  assert (factor : [ Γ |- B ~* C ] + _) by (now eapply redTyFactor).
  destruct factor as [BredC|CredB] > [|symmetry].
  now eapply cannotRedTyEq.
Defined.


Lemma whnfTmNoRed {Γ Γ' A B t u} :
    [ Γ ≡ Γ' |- t ≡whnf u ▷ A ≡whnf B]
 -> CannotRed Γ t.
Proof.
  intros H1 v.
  split.
  intros H2.
  - depelim H1.
    try (depelim H2; >fail).
    depelim H1.
    apply ParanoiaLeft in H1_.
    now eapply NoConfRed.
  - depelim H1.
    depelim H2.
    try (depelim H2; depelim H2_; >fail).
    depelim H1.
    depelim H2.
    clear H1_1 H2_1.
    apply ParanoiaLeft in H2_.
    eapply (Determinism _ H1_) in H2_.
    noconf H2_.
    assert (eq : tProd Dom Cod = tNat) by (eapply redTyDet > [ eassumption | eassumption | ..]; eapply introTyNoRed; reflexivity).
    noconf eq.
Defined.

Lemma introTmNoRed {Γ t} :
    introTermb t = true
 -> CannotRed Γ t.
Proof.
  intros introt v.
  split.
  intros H.
  - depelim H. noconf introt.
  - depelim H. depelim H. depelim H. noconf introt.
Defined.

Lemma cannotRedTmEq {Γ t u} :
    CannotRed Γ t
 -> [ Γ |- t ~*tm u ]
 -> u = t.
Proof.
  intros cannot H.
  depelim H.
  - reflexivity.
  - apply cannot in H0. destruct H0.
  - apply cannot in H. destruct H.
Defined.

Lemma redTmFactor {Γ t u v} :
     [Γ |- t ~*tm u ]
  -> [Γ |- t ~*tm v ]
  -> [Γ |- u ~*tm v ] + [ Γ |- v ~*tm u ].
Proof.
  intros H1 H2.
  assert (H1ε : Paranoiaε DeterminismP H1) by (apply ParanoiaToε ; apply Determinism).
  assert (res : _) by (now eapply redTmFactor_pre).
  destruct res as [res|(res & _)].
  - left. exact res.
  - right. exact res.
Defined.

Lemma redTmDet {Γ t} u v:
     [Γ |- t ~*tm u ]
  -> [Γ |- t ~*tm v ]
  -> CannotRed Γ u
  -> CannotRed Γ v
  -> v = u.
Proof.
  intros H1 H2 uwhnf vwhnf.
  assert (factor : [ Γ |- u ~*tm v ] + _) by (now eapply redTmFactor).
  destruct factor as [uredv|vredu] > [|symmetry].
  now eapply cannotRedTmEq.
Defined.
End Determinism.


Definition TransP j : forall i, Paranoia j i -> Type :=
  match j with
  | ConvCont => fun '(Γ , Γ') _ =>
    forall Γ'', [ |- Γ' ≡ Γ'' ] -> [ |- Γ ≡ Γ'' ]
  | ConvTy as j | ConvWhnfTy as j => fun '(Γ , Γ' , A , B) _ =>
    forall Γ'' C, Paranoia j (Γ' , Γ'' , B , C) -> Paranoia j (Γ , Γ'' , A , C)
  | ConvCheckTm as j | ConvTm as j | ConvWhnfTm as j | ConvNeRedTm as j | ConvNeTm as j
    => fun '(Γ , Γ' , A , B , t , u) _ =>
    forall Γ'' C v, Paranoia j (Γ' , Γ''  , B , C , u , v)
      -> Paranoia j (Γ , Γ'' , A , C , t , v)
  | _ => fun _ _ => unit
  end.

Lemma ParanoiaTrans j {i} (p : Paranoia j i) : TransP j i p.
Proof.
  induction p.
  ltac1:(simpl TransP in * ).
  try (exact tt).
  intros * H.
  try (depelim H; econstructor; eauto; > fail).
  - depelim H.
    assert (B'nored : CannotRed Γ' B').
    { eapply whnfTyNoRed. now eapply ParanoiaSymm in p1. }
    assert (A'0nored : CannotRed Γ' A'0).
    { now eapply whnfTyNoRed. }
    assert (eq : A'0 = B') by (now eapply redTyDet).
    noconf eq.
    now econstructor.
  - depelim H.
    assert (eq : A0 = B) by (eapply (Determinism ConvTm (ParanoiaSymm _ _ p1)); now eapplyI ParanoiaLeft).
    noconf eq.
    econstructor. eauto.
  - depelim H.
    assert (t'nored : CannotRed Γ' t').
    { eapply whnfTmNoRed. now eapply ParanoiaSymm in p1. }
    assert (t0nored : CannotRed Γ' t0).
    { now eapply whnfTmNoRed. }
    assert (eq : t0 = t') by (now eapply redTmDet).
    noconf eq.
    econstructor. eauto.
  - depelim H > [|depelim H; eapply introTmNoNe in H > [|reflexivity]; destruct H].
    econstructor. eauto.
  - depelim H > [|depelim H; eapply introTmNoNe in H > [|reflexivity]; destruct H].
    econstructor. eauto.
  - depelim H > [.. | econstructor; eauto].
    depelim p. depelim p1.
  - depelim H.
    assert (eq : A0 = B) by (eapply (Determinism ConvNeTm (ParanoiaSymm _ _ p1)); now eapplyI ParanoiaLeft).
    noconf eq.
    econstructor. eauto.
  - depelim H.
    depelim p1. depelim H.
    assert (eq : A0 = B) by (eapply (Determinism ConvNeTm (ParanoiaSymm _ _ p1_1)); now eapplyI ParanoiaLeft).
    noconf eq.
    assert (fac : [ _ |- tProd Dom' Cod' ~* tProd Dom0 Cod0 ] + _) by (now eapply redTyFactor).
    assert (eq : tProd Dom' Cod' = tProd Dom0 Cod0).
    { destruct fac as [red|red] > [|symmetry].
      eapply introTyDoesntReduce in red > [|reflexivity].
      eassumption. }
    noconf eq.
    (econstructor) > [eapply IHp1; econstructor| ..].
    eauto.
Defined.

Definition ParanoiaHPropP j : forall i (p : Paranoia j i), Type :=
  match j as j return (forall i (p : Paranoia j i), Type) with
  | RedTy => fun '(Γ , A , B) p => forall (p2 : [ Γ |- A ~* B ]), CannotRed Γ B -> p2 = p
  | RedTm => fun '(Γ , t , u) p => forall (p2 : [ Γ |- t ~*tm u ]), CannotRed Γ u -> p2 = p
  | ConvNeRedTm => fun '(Γ , Γ' , A , B , t , u) p =>
    forall (p2 : [ Γ ≡ Γ' |- t ≡ne u ▷red A ≡ B ]),
    CannotRed Γ A -> CannotRed Γ' B -> p2 = p
  | j => fun i p => forall (p2 : Paranoia j i), p2 = p
  end.

Lemma ParanoiaHProp j i (p : Paranoia j i) : ParanoiaHPropP j i p.
Proof.
  induction p using ParanoiaElim.
  depelim X.
  ltac1:(simpl ParanoiaHPropP in * ).
  intros p2.
  depelim p2.
  try f_equal.
  try (eauto; > fail).
  - 1: enough (CannotRed Γ A').
    1: enough (CannotRed Γ A'0).
    1: enough (CannotRed Γ' B').
    1: enough (CannotRed Γ' B'0).
    1: assert (eq : A'0 = A') by (now eapply redTyDet).
    1: assert (eq2 : B'0 = B') by (now eapply redTyDet).
    1: subst.
    1: f_equal; eauto.
    eapply whnfTyNoRed.
    > (() + (once (eapplyI ParanoiaSymm)); eassumption).
  - assert (termInferL : [ Γ ≡ Γ |- t ≡ t ▷ A0 ≡whnf A0 ]) by (eapply (ParanoiaLeft _ _ p2_1)).
    assert (termInferR : _) by (eapply (ParanoiaLeft _ _ (ParanoiaSymm _ _ p2_1))).
    assert (eq : A0 = A) by (now eapplyI Determinism).
    noconf eq.
    assert (eq : B0 = B) by (now eapply (Determinism _ (ParanoiaSymm _ _ termInfer))).
    noconf eq.
    f_equal. eauto.
  - 1: enough (CannotRed Γ t).
    1: enough (CannotRed Γ t0).
    1: enough (CannotRed Γ' t').
    1: enough (CannotRed Γ' t'0).
    1: assert (t0 = t) by (now eapply redTmDet).
    1: assert (t'0 = t') by (now eapply redTmDet).
    1: subst.
    1: f_equal; eauto.
    eapply whnfTmNoRed.
    > (() + (once (eapplyI ParanoiaSymm)); eassumption).
  - depelim p2. depelim p2_1.
  - depelim p2. depelim p2_1.
  - depelim neNat. depelim neNat1.
  - depelim neNat. depelim neNat1.
  - apply neNatP.
    eapply introTyNoRed; reflexivity.
  - intros A'noRed B'noRed.
    assert (A0 = A) by (eapplyI Determinism; > (now eapplyI ParanoiaLeft)).
    assert (B0 = B) by (eapplyI Determinism; > (eapplyI ParanoiaLeft ; now eapplyI ParanoiaSymm)).
    subst.
    f_equal. eauto.
  - eapply hProp.
  - eapply hProp.
  - depelim headNe.
    depelim p2_1.
    assert (A0 = A) by (eapplyI Determinism; > (now eapplyI ParanoiaLeft)).
    assert (B0 = B) by (eapplyI Determinism; > (eapplyI ParanoiaLeft ; now eapplyI ParanoiaSymm)).
    subst.
    1: enough (CannotRed Γ (tProd Dom Cod)).
    1: enough (CannotRed Γ (tProd Dom0 Cod0)).
    1: enough (CannotRed Γ' (tProd Dom' Cod')).
    1: enough (CannotRed Γ' (tProd Dom'0 Cod'0)).
    1: assert (eq1 : tProd Dom Cod = tProd Dom0 Cod0) by (now eapply redTyDet).
    1: assert (eq2 : tProd Dom' Cod' = tProd Dom'0 Cod'0) by (now eapply redTyDet).
    1: noconf eq1; noconf eq2; noconf e'; noconf e'0.
    1: cbn in H; noconf H.
    1: f_equal; eauto.
    apply introTyNoRed; reflexivity.
  - noconf e'. noconf e'0. cbn in H. noconf H.
    f_equal. eauto.
    apply scrutNeP.
    apply introTyNoRed; reflexivity.
  - intro cantredB.
    f_equal. eauto.
  - assert (eq : B0 = B) by (now eapplyI Determinism).
    noconf eq.
    f_equal. eauto.
  - depelim p2.
  - depelim p2.
  - depelim headReds.
  - depelim scrutReds.
  - depelim neuExp.
    depelim p2.
    assert (A0 = A) by (eapplyI Determinism; > (now eapplyI ParanoiaLeft)).
    subst.
    1: enough (CannotRed Γ (tProd Dom Cod)).
    1: enough (CannotRed Γ (tProd Dom Cod0)).
    1: assert (eq1 : tProd Dom Cod0 = tProd Dom Cod).
       { (eapply (@redTyDet Γ A)). eassumption. }
    1: noconf eq1.
    1: f_equal; eauto.
    apply introTyNoRed; reflexivity.
  - intros ?.
    f_equal; eauto.
  - intros cantRed.
    apply cantRed in p2_2 as oops.
    destruct oops.
  - intro cantRed.
    apply cantRed in p2_1 as oops.
    destruct oops.
  - intros cantRed.
    apply cantRed in etaStep as oops.
    destruct oops.
  - intros ?.
    f_equal. eauto.
  - intros cantRed.
    depelim etaStep.
    depelim etaStep.
    eapply NoConfRed in p2_1 as oops > [| now (eapplyI ParanoiaLeft)].
    destruct oops.
  - intros cantRed.
    apply cantRed in redStep as oops.
    destruct oops.
  - intros _.
    depelim p2_2.
    depelim p2_2.
    eapply NoConfRed in redStep as oops > [| now (eapplyI ParanoiaLeft)].
    destruct oops.
  - intros ?.
    assert (t'0 = t').
    { now eapply RedStepDet. }
    subst.
    f_equal. eauto.
Defined.

Definition normalizeP j : forall i, Paranoia j i -> Type :=
  match j with
  | ConvCont => fun '(Γ , Γ') _ => forall n A B, in_ctx Γ n A -> in_ctx Γ' n B -> term
  | ConvTy | ConvWhnfTy | ConvCheckTm | ConvTm | ConvWhnfTm | ConvNeTm | ConvNeRedTm => fun _ _ => term
  | _ => fun _ _ => unit
  end.

Definition normalize j i (p : Paranoia j i) : normalizeP j i p.
Proof.
  set (p_rem := p).
  induction p using ParanoiaElim.
  depelim X.
  ltac1:(simpl normalizeP in * ).
  try (exact tt).
  - intros ??? oop.
    depelim oop.
  - intros n A' B' whereA' whereB'.
    depelim whereA'.
    depelim whereB'.
    + exact (typeWfP⟨↑⟩).
    + assert (contP : _) by (exact (Conv_ConvContP X typeWfP)).
      specialize (contP _ _ _ whereA' whereB').
      exact (contP⟨↑⟩).
  - exact typeWhnfP.
  - exact tNat.
  - exact (tProd DomWfP CodWfP).
  - exact termInferP.
  - exact termWhnfInferP.
  - exact tZero.
  - exact (tSucc termWfP).
  - exact (tLambda domWfP bodyWfP).
  - exact neNatP.
  - exact neInferP.
  - exact (contWfP _ _ _ in_ctxL in_ctxR).
  - exact (tApp headNeP argChecksP).
  - exact (tNatElim predWfP hzChecksP hsChecksP scrutNeP).
Defined.

Lemma test : [ ε ≡ ε |- tApp (tLambda tNat (tRel 0)) tZero ≡ tZero ◁ tNat ≡ tNat ].
Proof.
  econstructor.
  1: econstructor.
  2: eapply redTmStep.
  2: econstructor.
  2: econstructor.
  3-4: eapply redTmNoEta.
  2: econstructor; econstructor.
  3-4: econstructor; eapply redTmNoEta.
  2: econstructor.
  3-4: econstructor.
  7: econstructor.
  7: econstructor; econstructor.
  12-13: eapply redTmNoEta.
  1: econstructor.
  econstructor.
  1-5: econstructor.
  > lazy_match! goal with | [ |- [ _ |- tNat ~* _ ] ] => (econstructor; eapply redTmNoEta) | [ |- _ ] => () end.
  econstructor.
  econstructor.
Defined.

Compute (normalize _ _ test).

Goal forall {Γ}, [ Γ ≡ Γ |- tZero ≡ tSucc tZero ▷ tNat ≡whnf tNat ] -> False.
Proof.
  intros Γ H.
  depelim H.
  depelim H0 > [..|depelim H0_0;depelim H0_0;depelim H0_0_1|depelim H0_].
  depelim H1 > [..|depelim H1_0;depelim H1_0;depelim H1_0_1|depelim H1_].
  depelim H.
  depelim H.
  depelim H.
Defined.

Definition SemanticsTarget j i (p : Paranoia j i) : Type.
Proof.
  set (p_rem := p).
  induction p.
  - 

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
