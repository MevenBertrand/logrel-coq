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

Inductive ConvCont : forall (Γ Γ' : context), Type :=
  | connil :
      [ |- ε ≡ ε ]
  | concons {Γ Γ' A B} :
      [ Γ ≡ Γ' |- A ≡ B]
   -> [ |- Γ ,, A ≡ Γ' ,, B]
with ConvTy : forall (Γ Γ' : context) (A B : term), Type :=
  | normTy {Γ Γ' A B A' B'} :
      [ Γ ≡ Γ' |- A' ≡whnf B' ]
   -> [ Γ |- A ~* A' ]
   -> [ Γ' |- B ~* B' ]
   -> [ Γ ≡ Γ' |- A ≡ B ]
with ConvWhnfTy : forall (Γ Γ' : context) (A B : term), Type :=
  | nfNat {Γ Γ'} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ ≡ Γ' |- tNat ≡whnf tNat ]
  | nfProd {Γ Γ' Dom Dom' Cod Cod'} :
      [ Γ ≡ Γ' |- Dom ≡ Dom' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ]
   -> [ Γ ≡ Γ' |- tProd Dom Cod ≡whnf tProd Dom' Cod' ]
with ConvNeTy : forall (Γ Γ' : context) (A B : term), Type :=
with ConvCheckTm : forall (Γ Γ' : context) (A B : term) (t u : term), Type :=
  | check {Γ Γ' A B A' B' t t'} :
      [ Γ ≡ Γ' |- t ≡ t' ▷ A ≡whnf B ]
   -> [ Γ ≡ Γ |- A' ≡ A ]
   -> [ Γ' ≡ Γ' |- B' ≡ B ]
   -> [ Γ ≡ Γ' |- t ≡ t' ◁ A' ≡ B' ]
with ConvTm : forall (Γ Γ' : context) (A B : term) (t u : term), Type :=
  | norm {Γ Γ' A B t t' u u'} :
      [ Γ ≡ Γ' |- t ≡whnf t' ▷ A ≡whnf B ]
   -> [ Γ |- u ~*tm t ]
   -> [ Γ' |- u' ~*tm t' ]
   -> [ Γ ≡ Γ' |- u ≡ u' ▷ A ≡whnf B ]
with ConvWhnfTm : forall (Γ Γ' : context) (A B : term) (t u : term), Type :=
  | nfZero {Γ Γ'} :
      [ |- Γ ≡ Γ' ]
   -> [ Γ ≡ Γ' |- tZero ≡whnf tZero ▷ tNat ≡whnf tNat ]
  | nfSucc {Γ Γ' t t'} :
      [ Γ ≡ Γ' |- t ≡ t' ▷ tNat ≡whnf tNat ]
   -> [ Γ ≡ Γ' |- tSucc t ≡whnf tSucc t' ▷ tNat ≡whnf tNat ]
  | nfNeNat {Γ Γ' n n'} :
      [ Γ ≡ Γ' |- n ≡ne n' ▷red tNat ≡ tNat ]
   -> [ Γ ≡ Γ' |- n ≡whnf n' ▷ tNat ≡whnf tNat ]
  | nfLambda {Γ Γ' Dom Dom' Cod Cod' t t'} :
      [ Γ ≡ Γ' |- Dom ≡ Dom' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- t ≡ t' ▷ Cod ≡whnf Cod' ]
   -> [ Γ ≡ Γ' |- tLambda Dom t ≡whnf tLambda Dom' t' ▷ tProd Dom Cod ≡whnf tProd Dom' Cod' ]
with ConvNeRedTm : forall (Γ Γ' : context) (A B : term) (t u : term), Type :=
  | tyReduces {Γ Γ' n n' A B A' B'} :
      [ Γ ≡ Γ' |- n ≡ne n' ▷ A ≡ B ]
   -> [ Γ |- A ~* A' ]
   -> [ Γ' |- B ~* B' ]
   -> [ Γ ≡ Γ' |- n ≡ne n' ▷red A' ≡ B' ]
with ConvNeTm : forall (Γ Γ' : context) (A B : term) (t u : term), Type :=
  | neVar {Γ Γ' A B n} :
      [ |- Γ ≡ Γ' ]
   -> in_ctx Γ n A
   -> in_ctx Γ' n B
   -> [ Γ ≡ Γ' |- tRel n ≡ne tRel n ▷ A ≡ B ]
  | neApp {Γ Γ' Dom Dom' Cod Cod' t t' u u'} :
      [ Γ ≡ Γ' |- t ≡ne t' ▷red tProd Dom Cod ≡ tProd Dom' Cod' ]
   -> [ Γ ≡ Γ' |- Dom ≡ Dom' ]
   -> [ Γ ≡ Γ' |- u ≡ u' ◁ Dom ≡ Dom' ]
   -> [ Γ ,, Dom ≡ Γ' ,, Dom' |- Cod ≡ Cod' ]
   -> [ Γ ≡ Γ' |- Cod[u..] ≡ Cod'[u'..] ]
   -> [ Γ ≡ Γ' |- tApp t u ≡ne tApp t' u' ▷ Cod[u..] ≡ Cod'[u'..] ]
  | neNatElim {Γ Γ' P P' hz hz' hs hs' t t'} :
      [ Γ ,, tNat ≡ Γ' ,, tNat |- P ≡ P' ]
   -> [ Γ ≡ Γ' |- hz ≡ hz' ◁ P[tZero..] ≡ P'[tZero..] ]
   -> [ Γ ≡ Γ' |- hs ≡ hs' ◁ tProd tNat P[(tSucc (tRel 0))]⇑ ≡ tProd tNat P'[(tSucc (tRel 0))]⇑ ]
   -> [ Γ ≡ Γ' |- t ≡ne t' ▷red tNat ≡ tNat ]
   -> [ Γ ≡ Γ' |- P[t..] ≡ P'[t'..] ]
   -> [ Γ ≡ Γ' |- tNatElim P hz hs t ≡ne tNatElim P' hz' hs' t' ▷ P[t..] ≡ P'[t'..] ]
(* with RedTyStep : forall (Γ : context) (A B : term), Type := *)
with RedTy : forall (Γ : context) (A B : term), Type :=
  | redTyDone {Γ A} :
      [ |- Γ ≡ Γ]
   -> [ Γ |- A ~* A ]
  (* | redTyStep {Γ A B C} :
   *     [ Γ |- A ~> B ]
   *  -> [ Γ |- B ~* C ]
   *  -> [ Γ |- A ~* C ] *)
with RedTmStep : forall (Γ : context) (t u : term), Type :=
  | redBeta {Γ A B t u} :
      [ Γ ≡ Γ |- A ≡ A ]
   -> [ Γ ,, A ≡ Γ ,, A |- t ≡ t ▷ B ≡whnf B ]
   -> [ Γ ≡ Γ |- u ≡ u ▷ A ≡whnf A ]
   -> [ Γ |- tApp (tLambda A t) u ~>tm t[u..] ]
  | redAppHead {Γ t t' u} :
      [ Γ |- t ~>tm t' ]
   -> [ Γ |- tApp t u ~>tm tApp t' u ]
with ExpTmStep : forall (Γ : context) (t u : term), Type :=
  | expandPi {Γ n Dom Cod} :
      [ Γ ≡ Γ |- n ≡ne n ▷red tProd Dom Cod ≡ tProd Dom Cod ]
   -> [ Γ |- n ↗ tLambda Dom (tApp n⟨↑⟩ (tRel 0)) ]
with RedTm : forall (Γ : context) (t u : term), Type :=
  | redTmNoEta {Γ t} :
      [ |- Γ ≡ Γ]
   -> [ Γ |- t ~*tm t ]
  | redTmEta {Γ t u} :
      [ |- Γ ≡ Γ]
   -> [ Γ |- t ↗ u ]
   -> [ Γ |- t ~*tm u ]
  | redTmStep {Γ t t' t''} :
      [ Γ |- t ~>tm t' ]
   -> [ Γ |- t' ~*tm t'' ]
   -> [ Γ |- t ~*tm t'' ]
  where "[ |- Γ ≡ Γ' ]" := (ConvCont Γ Γ')
    and "[ Γ ≡ Γ' |- A ≡ B ]" := (ConvTy Γ Γ' A B)
    and "[ Γ ≡ Γ' |- A ≡whnf B ]" := (ConvWhnfTy Γ Γ' A B)
    and "[ Γ ≡ Γ' |- t ≡ t' ◁ A ≡ B ]" := (ConvCheckTm Γ Γ' A B t t')
    and "[ Γ ≡ Γ' |- t ≡ t' ▷ A ≡whnf B ]" := (ConvTm Γ Γ' A B t t')
    and "[ Γ ≡ Γ' |- t ≡whnf t' ▷ A ≡whnf B ]" := (ConvWhnfTm Γ Γ' A B t t')
    and "[ Γ ≡ Γ' |- A ≡ne B ]" := (ConvNeTy Γ Γ' A B)
    and "[ Γ ≡ Γ' |- t ≡ne t' '▷red' A ≡ B ]" := (ConvNeRedTm Γ Γ' A B t t')
    and "[ Γ ≡ Γ' |- t ≡ne t' ▷ A ≡ B ]" := (ConvNeTm Γ Γ' A B t t')
    (* and "[ Γ |- A ~> B ]" := (RedTyStep Γ A B) *)
    and "[ Γ |- A ~* B ]" := (RedTy Γ A B)
    and "[ Γ |- t ↗ u ]" := (ExpTmStep Γ t u)
    and "[ Γ |- t ~>tm u ]" := (RedTmStep Γ t u)
    and "[ Γ |- t ~*tm u ]" := (RedTm Γ t u).

Derive NoConfusion for term.

Derive Signature for ConvCont
ConvTy
ConvWhnfTy
ConvCheckTm
ConvTm
ConvWhnfTm
ConvNeRedTm
ConvNeTm
RedTy
(* RedTyStep *)
RedTmStep
ExpTmStep
RedTm.

Scheme ConvCont_rect_nodep := Minimality for ConvCont Sort Type
  with ConvTy_rect_nodep := Minimality for ConvTy Sort Type
  with ConvWhnfTy_rect_nodep := Minimality for ConvWhnfTy Sort Type
  with ConvCheckTm_rect_nodep := Minimality for ConvCheckTm Sort Type
  with ConvTm_rect_nodep := Minimality for ConvTm Sort Type
  with ConvWhnfTm_rect_nodep := Minimality for ConvWhnfTm Sort Type
  with ConvNeRedTm_rect_nodep := Minimality for ConvNeRedTm Sort Type
  with ConvNeTm_rect_nodep := Minimality for ConvNeTm Sort Type
  with RedTy_rect_nodep := Minimality for RedTy Sort Type
  (* with RedTyStep_rect_nodep := Minimality for RedTyStep Sort Type *)
  with RedTmStep_rect_nodep := Minimality for RedTmStep Sort Type
  with ExpTmStep_rect_nodep := Minimality for ExpTmStep Sort Type
  with RedTm_rect_nodep := Minimality for RedTm Sort Type.

Combined Scheme _Syntax_rect_nodep from
ConvCont_rect_nodep,
ConvTy_rect_nodep,
ConvWhnfTy_rect_nodep,
ConvCheckTm_rect_nodep,
ConvTm_rect_nodep,
ConvWhnfTm_rect_nodep,
ConvNeRedTm_rect_nodep,
ConvNeTm_rect_nodep,
RedTy_rect_nodep,
RedTmStep_rect_nodep,
ExpTmStep_rect_nodep,
RedTm_rect_nodep.

Ltac2 make_forall (x : ident) (dom : constr) (body : constr -> constr) : constr :=
  let f := Constr.in_context x dom (fun () => let body := body (Control.hyp x) in exact $body) in
  match Constr.Unsafe.kind f with
    | Constr.Unsafe.Lambda f cl => Constr.Unsafe.make (Constr.Unsafe.Prod f cl)
    | _ => Control.throw Assertion_failure
  end.


Ltac2 make_fun (x : ident) (dom : constr) (body : constr -> constr) : constr :=
  Constr.in_context x dom (fun () => let body := body (Control.hyp x) in exact $body).

Ltac2 get_binder (body : constr) : ident option :=
  match Constr.Unsafe.kind body with
    | Constr.Unsafe.Prod f _ => Constr.Binder.name f
    | Constr.Unsafe.Lambda f _ => Constr.Binder.name f
    | _ => None
  end.

Ltac2 in_goal_opt (x : ident option) : ident :=
  match x with
  | Some x => Fresh.in_goal x
  | None => Fresh.in_goal @x
  end.

Ltac2 rec polymorphise t :=
  lazy_match! t with
    | forall x : ?hyp, @?t x => make_forall (in_goal_opt (get_binder t)) hyp
      (fun x => let t' := eval hnf in ($t $x) in let t'' := polymorphise t' in t'')
    | (?t1 * ?t2)%type => let t1' := polymorphise t1 in let t2' := polymorphise t2 in
        constr:($t1' × $t2')
    | ?t' => t'
  end.

Ltac2 rec remove_steps t :=
  lazy_match! t with
  | _ -> ?t => remove_steps t
  | forall x : ?dom, @?t x => make_fun (in_goal_opt (get_binder t)) dom
      (fun x => let t' := eval hnf in ($t $x) in let t'' := remove_steps t' in t'')
  | ?t' => t'
  end.

Definition _SyntaxInductionType :=
  ltac2:(let ind := Fresh.in_goal @ind in
      pose (ind := _Syntax_rect_nodep);
      fold ind ;
      let ind_ty := Constr.type (Control.hyp ind) in
      exact $ind_ty).

Definition SyntaxInductionType :=
  ltac2: (let ind := eval cbv delta [_SyntaxInductionType] zeta
    in _SyntaxInductionType in
    let ind' := polymorphise ind in
  exact $ind').

Definition SyntaxInduction : SyntaxInductionType.
Proof.
  intros ?**.
  let h :=
    List.fold_left
      (fun a (b,_,_) => let b := Control.hyp b in constr:($a $b))
      constr:(_Syntax_rect_nodep)
      (Control.hyps ())
  in pose (H := $h).
  repeat split.
  apply H.
Defined.

Definition SyntaxInductionConcl := ltac2:(let t := eval cbv delta [SyntaxInductionType] beta in SyntaxInductionType in let t' := remove_steps t in exact $t').
Print SyntaxInductionConcl.

(* TODO: Should be in Constr? *)
(* Substitutes the argument in the body of a given lambda *)
Ltac2 app_lambda (lam : constr) (a : constr) : constr :=
  match Constr.Unsafe.kind lam with
  | Constr.Unsafe.Lambda _ body => Constr.Unsafe.substnl [a] 0 body
  | _ => Control.throw Assertion_failure
  end.

Ltac2 decompose_app_list (c : constr) :=
  match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f cl => (f, Array.to_list cl)
    | _ => (c,[])
  end.

Ltac2 mkApp_list (h : constr) (args : constr list) : constr :=
  match args with
  | [] => h
  | _ => Constr.Unsafe.make (Constr.Unsafe.App h (Array.of_list args))
  end.

Ltac2 syntax_ind_concl (f : constr -> constr) :=
  let rec transform_clause t :=
    lazy_match! t with
    (* XXX: Need to give a name to _cod so that it only matches closed terms *)
    | ?dom -> ?_cod =>
      let r := f dom in constr:($dom -> $r)
    | forall (x : ?dom), @?a x => make_forall (in_goal_opt (get_binder t)) dom
        (fun x => transform_clause (app_lambda a x))
    end
  in
  let rec transform_clauses t :=
    lazy_match! t with
    | fun (x : ?dom) => @?a x =>
      let f := make_fun (in_goal_opt (get_binder t)) dom
        (fun x => transform_clauses (app_lambda a x))
      in
      lazy_match! f with
      | fun _ => ?b => b
      end
    | ?a × ?b => let a := transform_clause a in let b := transform_clauses b in constr:($a × $b)
    | ?a => let a := transform_clause a in a
    end in
  let t := eval cbv [SyntaxInductionConcl] in SyntaxInductionConcl in
  let res := transform_clauses t in
  res.

Ltac2 Notation "syntax_ind_concl" t(next) := syntax_ind_concl t.

Ltac2 synt_ind_arity (c : constr) :=
  lazy_match! c with
  | ConvCont => 2
  | ConvTy => 2
  | ConvWhnfTy => 2
  | ConvCheckTm => 2
  | ConvTm => 2
  | ConvWhnfTm => 2
  | ConvNeRedTm => 2
  | ConvNeTm => 2
  | RedTy => 1
  (* | RedTyStep => 1 *)
  | RedTmStep => 1
  | ExpTmStep => 1
  | RedTm => 1
  end.

Lemma Conv_ConvCont : ltac2:(
  let f t :=
    let (head, args) := decompose_app_list t in
    match (synt_ind_arity head) with
    | 2 => let Γ := List.nth args 0 in
           let Γ' := List.nth args 1 in
           constr:([ |- $Γ ≡ $Γ' ])
    | 1 => let Γ := List.nth args 0 in
           constr:([ |- $Γ ≡ $Γ ])
    | _ => constr:(unit)
    end in
  refine (syntax_ind_concl f)).
Proof.
  Print SyntaxInductionType.
  apply SyntaxInduction.
  > intros **.
  > repeat (exact tt || assumption || constructor).
Defined.

Ltac2 fold_righti (f : int -> 'a -> 'b -> 'b) (ls : 'a list) (a : 'b) : 'b :=
  let rec go i ls a :=
    match ls with
    | [] => a
    | l :: ls => f i l (go (Int.add i 1) ls a)
    end
  in go 0 ls a.

Ltac2 unzip (ls : 'a list) : 'a list * 'a list :=
  let f i x (l, r) :=
    if Int.equal (Int.mod i 2) 0
    then (x :: l, r)
    else (l, x :: r)
  in
  fold_righti f ls ([],[]).

Ltac2 rec zipWith (f : 'a -> 'b -> 'c) (l : 'a list) (r : 'b list) : 'c list :=
  match l with
  | [] => []
  | hl :: l =>
    match r with
    | [] => []
    | hr :: r => f hl hr :: zipWith f l r
  end end.

Ltac2 zip (l : 'a list) (r : 'b list) : ('a * 'b) list :=
  zipWith (fun a b => (a, b)) l r.

Ltac2 uncurry (f : 'a -> 'b -> 'c) (u : 'a * 'b) : 'c :=
  let (a , b) := u in f a b.

Lemma Conv_Symm : ltac2:(
  let f t :=
    let (head, args) := decompose_app_list t in
    match (synt_ind_arity head) with
    | 2 => let m := List.concat (uncurry (zipWith (fun a b => [b ; a])) (unzip args)) in
        mkApp_list head m
    | _ => constr:(unit)
    end in
  refine (syntax_ind_concl f)).
Proof.
  apply SyntaxInduction; now econstructor.
Defined.

Lemma Conv_Left : ltac2:(
  let f t :=
    let (head, args) := decompose_app_list t in
    match (synt_ind_arity head) with
    | 2 => let m := List.concat (uncurry (zipWith (fun a _ => [a ; a])) (unzip args)) in
        mkApp_list head m
    | _ => constr:(unit)
    end in
  let t := syntax_ind_concl f
  in exact $t).
Proof.
  apply SyntaxInduction; now econstructor.
Defined.

Ltac2 Notation "rename" renames(list1(seq(ident, "into", ident), ",")) := Std.rename renames.


Ltac2 rec eapplyprod c :=
  (Unification.unify (TransparentState.current ()) c open_constr:((_ , _));
  eapply (fst $c) + eapplyprod constr:(snd $c))
  + eapply $c.

Ltac2 convsymmetries () :=
  () + eapply Conv_Left; () + eapply Conv_Symm.

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

Create HintDb typing discriminated.

Hint Resolve Conv_Left Conv_Symm : typing.
Hint Constructors ConvCont
ConvTy
ConvWhnfTy
ConvCheckTm
ConvTm
ConvWhnfTm
ConvNeRedTm
ConvNeTm
RedTy
RedTmStep
ExpTmStep
RedTm

in_ctx
renames : typing.

Print HintDb typing.

Ltac2 iter_hypo (f : ident -> unit) := match! goal with [ h : _ |- _] => f h end.

(* Lemmas *)
Lemma RenStable : ltac2:(
  let f t :=
    let (head, args) := decompose_app_list t in
    match (synt_ind_arity head) with
    | 2 =>
      let (Γ , Γ' , args) := match args with
      | Γ :: (Γ' :: args) => Γ , Γ' , args
      | _ => Control.throw Assertion_failure
      end in
       constr:(forall (Δ Δ' : context) ρ,
         [ |- Δ ≡ Δ' ] -> renames Δ ρ $Γ -> renames Δ' ρ $Γ' ->
         ltac2:(refine (mkApp_list head (&Δ :: &Δ' :: (List.map (fun c => constr:($c⟨&ρ⟩)) args)))))
    | 1 =>
      let (Γ , args) := match args with
      | Γ :: args => Γ , args
      | _ => Control.throw Assertion_failure
      end in
      constr:(forall (Δ : context) ρ,
        [ |- Δ ≡ Δ] -> renames Δ ρ $Γ ->
        ltac2:(refine (mkApp_list head (&Δ ::(List.map (fun c => constr:($c⟨&ρ⟩)) args)))))
    | _ => constr:(unit)
    end in
  refine (syntax_ind_concl f)).
Proof.
  apply SyntaxInduction.
  > (intros *; repeat (first [ intros ? ? * | try (rename H into H'); intros H ])).
  1-2: eassumption.

  myautosubst_tac ().

  (* Use resp. each constructor of the mind block  *)
  let s := Env.get [@LogRel; @Paranoia; @ConvCont] in
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

  try (once (repeat (> iter_hypo (fun h => let h := Control.hyp h in eapply $h) || (eapply Conv_Left; now (() + eapply Conv_Symm)) || econstructor || eapply RenWeakenOnce || (ltac1:(change (↑ >> upRen_term_term ?ρ) with (ρ >> ↑)); rewrite <- (renRen_term _ ↑)))); >fail).
Defined.

Ltac2 bing () := iter_hypo (fun h => let h := Control.hyp h in eapply $h) || (now convsymmetries ()) || econstructor.

Lemma Output : SyntaxInductionConcl
  (fun Γ Γ' => unit)
  (fun Γ Γ' A B => unit)
  (fun Γ Γ' A B => unit)
  (fun Γ Γ' A B t u => unit)
  (fun Γ Γ' A B t u => forall Γ'' t' A' C, [ Γ'' ≡ Γ' |- t' ≡ u ▷ A' ≡whnf C ] -> B = C)
  (fun Γ Γ' A B t u => forall Γ'' t' A' C, [ Γ'' ≡ Γ' |- t' ≡whnf u ▷ A' ≡whnf C ] -> B = C)
  (fun Γ Γ' A B t u => forall Γ'' t' A' C, [ Γ' ≡ Γ' |- B ≡whnf B ]
    -> [ Γ' ≡ Γ' |- C ≡whnf C ] -> [ Γ'' ≡ Γ' |- t' ≡ne u ▷red A' ≡ C ] -> B = C)
  (fun Γ Γ' A B t u => forall Γ'' t' A' C, [ Γ'' ≡ Γ' |- t' ≡ne u ▷ A' ≡ C ] -> B = C)
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
  1: depelim H'; depelim c.
  1: depelim c; depelim c.
  1: f_equal.
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
