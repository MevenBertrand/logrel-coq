From Coq Require Import ssreflect.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils Context Weakening.

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

Inductive renames (Γ : context) : forall (ρ : nat -> nat) (Δ : context), Type :=
  | ren_empty {ρ} :
      renames Γ ρ ε
  | ren_tm {Δ A ρ} :
      renames Γ (↑ >> ρ) Δ
   -> in_ctx Γ (ρ 0) A⟨↑ >> ρ⟩
   -> renames Γ ρ (Δ ,, A).

Scheme renames_rect_nodep := Minimality for renames Sort Type.
Derive Signature for in_ctx renames.

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

Derive NoConfusion for judgement term prod.

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
  | nfNeNat {Γ Γ' n n'}
      (neNat : [ Γ ≡ Γ' |- n ≡ne n' ▷red tNat ≡ tNat ])
    : [ Γ ≡ Γ' |- n ≡whnf n' ▷ tNat ≡whnf tNat ]
  | nfLambda {Γ Γ' Dom Dom' Cod Cod' t t'}
      (domWf : [ Γ ≡ Γ' |- Dom ≡ Dom' ])
      (bodyWf : [ Γ ,, Dom ≡ Γ' ,, Dom' |- t ≡ t' ▷ Cod ≡whnf Cod' ])
    : [ Γ ≡ Γ' |- tLambda Dom t ≡whnf tLambda Dom' t' ▷ tProd Dom Cod ≡whnf tProd Dom' Cod' ]

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
      (predWf : [ Γ ,, tNat ≡ Γ' ,, tNat |- P ≡ P' ])
      (hzChecks : [ Γ ≡ Γ' |- hz ≡ hz' ◁ P[tZero..] ≡ P'[tZero..] ])
      (hsChecks : [ Γ ≡ Γ' |- hs ≡ hs' ◁ tProd tNat P[(tSucc (tRel 0))]⇑ ≡ tProd tNat P'[(tSucc (tRel 0))]⇑ ])
      (scrutNe : [ Γ ≡ Γ' |- t ≡ne t' ▷red tNat ≡ tNat ])
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
      (neuFun : [ Γ ≡ Γ |- n ≡ne n ▷red tProd Dom Cod ≡ tProd Dom Cod ])
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
  | nfNeNatε {Γ Γ' n n'}
      {neNat : [ Γ ≡ Γ' |- n ≡ne n' ▷red tNat ≡ tNat ]}
      (neNatε : Paranoiaε (@Pred) neNat)
      (neNatP : Pred neNat)
    : Paranoiaε (@Pred) (nfNeNat neNat)
  | nfLambdaε {Γ Γ' Dom Dom' Cod Cod' t t'}
      {domWf : [ Γ ≡ Γ' |- Dom ≡ Dom' ]}
      (domWfε : Paranoiaε (@Pred) domWf)
      (domWfP : Pred domWf)
      {bodyWf : [ Γ ,, Dom ≡ Γ' ,, Dom' |- t ≡ t' ▷ Cod ≡whnf Cod' ]}
      (bodyWfε : Paranoiaε (@Pred) bodyWf)
      (bodyWfP : Pred bodyWf)
    : Paranoiaε (@Pred) (nfLambda domWf bodyWf)

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
      {predWf : [ Γ ,, tNat ≡ Γ' ,, tNat |- P ≡ P' ]}
      (predWfε : Paranoiaε (@Pred) predWf)
      (predWfP : Pred predWf)
      {hzChecks : [ Γ ≡ Γ' |- hz ≡ hz' ◁ P[tZero..] ≡ P'[tZero..] ]}
      (hzChecksε : Paranoiaε (@Pred) hzChecks)
      (hzChecksP : Pred hzChecks)
      {hsChecks : [ Γ ≡ Γ' |- hs ≡ hs' ◁ tProd tNat P[(tSucc (tRel 0))]⇑ ≡ tProd tNat P'[(tSucc (tRel 0))]⇑ ]}
      (hsChecksε : Paranoiaε (@Pred) hsChecks)
      (hsChecksP : Pred hsChecks)
      {scrutNe : [ Γ ≡ Γ' |- t ≡ne t' ▷red tNat ≡ tNat ]}
      (scrutNeε : Paranoiaε (@Pred) scrutNe)
      (scrutNeP : Pred scrutNe)
      {resTypeWf : [ Γ ≡ Γ' |- P[t..] ≡ P'[t'..] ]}
      (resTypeWfε : Paranoiaε (@Pred) resTypeWf)
      (resTypeWfP : Pred resTypeWf)
    : Paranoiaε (@Pred) (neNatElim predWf hzChecks hsChecks scrutNe resTypeWf)

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
      {neuFun : [ Γ ≡ Γ |- n ≡ne n ▷red tProd Dom Cod ≡ tProd Dom Cod ]}
      (neuFunε : Paranoiaε (@Pred) neuFun)
      (neuFunP : Pred neuFun)
    : Paranoiaε (@Pred) (expandPi neuFun)

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
      assert (U : _) by (now eapply (argChecksP _ _ ρ)).
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

Lemma GetVarTyped : ltac2:(
  let f t :=
    let (head, args) := decompose_app_list t in
    match (synt_ind_arity head) with
    | 2 => let Γ := List.nth args 0 in
           let Γ' := List.nth args 1 in
           '(forall n A B, in_ctx $Γ n A -> in_ctx $Γ' n B -> [ $Γ ≡ $Γ' |- A ≡ B ])
    | 1 => let Γ := List.nth args 0 in
           constr:(forall n A, in_ctx $Γ n A -> [ $Γ ≡ $Γ |- A ≡ A ])
    | _ => constr:(unit)
    end in
  refine (syntax_ind_concl f)).
Proof.
  eapply SyntaxInduction; intros *; repeat (first [ intros ? ? * | try (rename H into H'); intros H ]).
  try (lazy_match! goal with [|- unit] => constructor end).
  1: depelim H.
  1: depelim H1; depelim H2.
  1: eapply RenStable > [eassumption | econstructor; eassumption | | ]; eapply RenWeakenOnce; eapply RenId.
  1: eapply RenStable > [now eapply H0 | econstructor; eassumption | | ]; eapply RenWeakenOnce; eapply RenId.
  eauto.
Defined.

Lemma WellTyped : ltac2:(
  let f t :=
    match! t with
    | [ ?Γ ≡ ?Γ' |- _ ≡ _ ▷ ?a ≡whnf ?b ] => '[ $Γ ≡ $Γ' |- $a ≡whnf $b ]
    | [ ?Γ ≡ ?Γ' |- _ ≡whnf _ ▷ ?a ≡whnf ?b ] => '[ $Γ ≡ $Γ' |- $a ≡whnf $b ]
    | [ ?Γ ≡ ?Γ' |- _ ≡ne _ ▷red ?a ≡ ?b ] => '[ $Γ ≡ $Γ' |- $a ≡ $b ]
    | [ ?Γ ≡ ?Γ' |- _ ≡ne _ ▷ ?a ≡ ?b ] => '[ $Γ ≡ $Γ' |- $a ≡ $b ]
    | [ ?Γ |- ?a ~* ?b ] => '(forall Γ' B, [ $Γ ≡ Γ' |- $a ≡ B ] -> [ $Γ ≡ Γ' |- $b ≡ B ])
    | _ => 'unit
    end in
  refine (syntax_ind_concl f)).
Proof.
  eapply SyntaxInduction; intros *; repeat (first [ intros ? ? * | try (rename H into H'); intros H ]).
  try (lazy_match! goal with [|- unit] => constructor end).
  - eassumption.
  - repeat (eassumption || econstructor).
  - repeat (eassumption || econstructor).
  - repeat (eassumption || econstructor || (now (eapplyprod 'Conv_ConvCont; () + eapply Conv_Left; () + eapply Conv_Symm))).
  - repeat ((now (eapplyprod 'Conv_ConvCont; eapply Conv_Left; () + eapply Conv_Symm)) || eassumption || econstructor).
  - eapply H2.
    eapply Conv_Symm.
    eapply H4.
    eapply Conv_Symm.
    eassumption.
  - now eapplyprod 'GetVarTyped.
  - eassumption.
  - eassumption.
  - eassumption.
Defined.

Ltac2 bing () := iter_hypo (fun h => let h := Control.hyp h in eapply $h) || (now convsymmetries ()) || econstructor.

Lemma Output : SyntaxInductionConcl
  (fun Γ Γ' => unit)
  (fun Γ Γ' A B => unit)
  (fun Γ Γ' A B => unit)
  (fun Γ Γ' A B t u => unit)
  (fun Γ Γ' A B t u => forall C, [ Γ ≡ Γ |- t ≡ t ▷ C ≡whnf C ] -> A = C)
  (fun Γ Γ' A B t u => forall C, [ Γ ≡ Γ |- t ≡whnf t ▷ C ≡whnf C ] -> A = C)
  (fun Γ Γ' A B t u => forall C, [ Γ ≡ Γ |- A ≡whnf A ]
    -> [ Γ ≡ Γ |- C ≡whnf C ] -> [ Γ ≡ Γ |- t ≡ne t ▷red C ≡ C ] -> A = C)
  (fun Γ Γ' A B t u => forall C, [ Γ ≡ Γ |- t ≡ne t ▷ C ≡ C ] -> A = C)
  (fun Γ A B => forall C, [ Γ ≡ Γ |- B ≡whnf B ] -> [ Γ ≡ Γ |- C ≡whnf C ] -> [ Γ |- A ~* C ]  -> B = C)
  (fun Γ t u => forall v, [ Γ |- t ~>tm v ] -> u = v)
  (fun Γ t u => forall v, [ Γ |- t ↗ v ] -> u = v)
  (fun Γ t u => forall v A B,
       [ Γ ≡ Γ |- u ≡whnf u ▷ A ≡whnf A ]
    -> [ Γ ≡ Γ |- v ≡whnf v ▷ B ≡whnf B ]
    -> [ Γ |- t ~*tm v ]
    -> u = v).
Proof.
  eapply SyntaxInduction; intros *; repeat (first [ intros ? ? * | try (rename H into H'); intros H ]).
  all: try (lazy_match! goal with [|- unit] => constructor end).
  depelim H.
  (* > iter_hypo (fun h => try (let h' := Control.hyp h in erewrite $h' by bing (); printf "%I" h; clear0 [h])). *)
   try (once (repeat (> reflexivity || progress f_equal || bing () || iter_hypo (fun h => let h' := Control.hyp h in progress (erewrite ! $h' by bing ())) || eapply in_ctx_inj)); >fail).
  - depelim H'. depelim c.
  - depelim c. depelim c.
  - f_equal.
    eassert (noconf : tProd Dom Cod = tProd Dom0 Cod0).
    + eapply H0.
      * eapply WellTyped in H'.
        eapply Conv_Left in H'.
        depelim H'.
        depelim r.
        depelim r0.
        eassumption.
      * eapply WellTyped in c.
        eapply Conv_Left in c.
        depelim c.
        depelim r.
        depelim r0.
        eassumption.
      * now eapply Conv_Left.
    + now noconf noconf.
  - depelim H.
  - depelim H'.
  - f_equal.
    eassert (noconf : tProd Dom Cod = tProd Dom0 Cod0).
    + eapply H0.
      * eapply WellTyped in H'.
        depelim H'.
        depelim r.
        now depelim r0.
      * eapply WellTyped in c.
        depelim c.
        depelim r.
        now depelim r0.
      * eassumption.
    + now noconf noconf.
  - depelim e.
    depelim H1.
    + depelim c1; depelim c1.
    + depelim c1; depelim c1.
    + 
  1-2: Control.shelve ().
  - bing ().
    depelim H5.
    erewrite ?H0 by bing ().
    > bing ().
    > bing ().
    > bing ().
    > bing ().
  - bing ().
    erewrite H4 by bing ().
    bing ().
  - depelim H'.
    depelim c.
    erewrite H4 by bing ().
    bing ().
    > bing ().
    > bing (). depelim H; reflexivity.
  - depelim H; reflexivity.
  - depelim H; try reflexivity.
    depelim X; depelim c.
  - depelim H.
    + depelim c; depelim c.
    + f_equal; tea eapply H0.
  - depelim X2.
    assert (__ : B = B0) by (tea eapply H'). subst.
    tea eapply H1.
  - depelim H.
    tea eapply in_ctx_inj.
  - depelim H.
    f_equal.
    enough (prodeq : tProd Dom' Cod' = tProd Dom'0 Cod'0) by (noconf prodeq; reflexivity).
    eapply H' > [eassumption | ..]; econstructor.
Defined.

Lemma Conv_Trans : SyntaxInductionConcl
  (fun Γ Γ' => forall Γ'', [ |- Γ' ≡ Γ'' ] -> [ |- Γ ≡ Γ'' ])
  (fun Γ Γ' A B => forall Γ'' C, [ Γ' ≡ Γ'' |- B ≡ C ] -> [ Γ ≡ Γ'' |- A ≡ C ])
  (fun Γ Γ' A B => forall Γ'' C, [ Γ' ≡ Γ'' |- B ≡whnf C ] -> [ Γ ≡ Γ'' |- A ≡whnf C ])
  (fun Γ Γ' A B t u => forall Γ'' C v, [ Γ' ≡ Γ'' |- u ≡ v ◁ B ≡ C ] -> [ Γ ≡ Γ'' |- t ≡ v ◁ A ≡ C ])
  (fun Γ Γ' A B t u => forall Γ'' C v, [ Γ' ≡ Γ'' |- u ≡ v ▷ B ≡whnf C ] -> [ Γ ≡ Γ'' |- t ≡ v ▷ A ≡whnf C ])
  (fun Γ Γ' A B t u => forall Γ'' C v, [ Γ' ≡ Γ'' |- u ≡whnf v ▷ B ≡whnf C ] -> [ Γ ≡ Γ'' |- t ≡whnf v ▷ A ≡whnf C ])
  (fun Γ Γ' A B t u => forall Γ'' C v, [ Γ' ≡ Γ'' |- u ≡ne v ▷red B ≡ C ] -> [ Γ ≡ Γ'' |- t ≡ne v ▷red A ≡ C ])
  (fun Γ Γ' A B t u => forall Γ'' C v, [ Γ' ≡ Γ'' |- u ≡ne v ▷ B ≡ C ] -> [ Γ ≡ Γ'' |- t ≡ne v ▷ A ≡ C ])
  (fun _ _ _ => unit)
  (fun _ _ _ => unit)
  (fun _ _ _ => unit)
  (fun _ _ _ => unit).
Proof.
  eapply SyntaxInduction; intros *; repeat (first [ intros ? ? * | try (rename H into H'); intros H ]).
  all: try (lazy_match! goal with [|- unit] => constructor end).
  all: depelim H.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - invertRedTy.
  - invertRedTy.
  - invertRedTy.
    now eapply tyProd.
  - econstructor.
    + eapply X0.
  - assert ()
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
