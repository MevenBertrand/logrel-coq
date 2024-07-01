From MetaCoq.Utils Require Import MCString bytestring.
From MetaCoq.Common Require Import uGraph BasicAst.
From MetaCoq.Template Require Import ReflectAst Checker Typing Ast Loader TemplateMonad.

From LogRel Require Export Utils.

Import monad_utils.MCMonadNotation.
Require Import MSets List.
Open Scope bs.

Set Universe Polymorphism.
Unset MetaCoq Strict Unquote Universe Mode.

(** ** MetaCoq utility functions *)

Definition term_eqb (t1 t2 : term) :=
  @eq_term config.default_checker_flags init_graph t1 t2.

Notation "t ?= u" := (term_eqb t u) (at level 70).

Notation "'$run' f" := ltac:(let p y := exact y in
    run_template_program
    f
    p) (at level 0, only parsing).

Section MetaCoqLocallyNameless.

  Definition to_set {A} (f : A -> IdentSet.t) : list A -> IdentSet.t :=
    fold_right (fun a => IdentSet.union (f a)) IdentSet.empty.

  Fixpoint to_ident_set (t : term) : IdentSet.t :=
    match t with
    | tVar id => IdentSet.singleton id
    | tRel n => IdentSet.empty
    | tEvar ev args => to_set to_ident_set args
    | tSort s => IdentSet.empty
    | tCast t kind v => IdentSet.union (to_ident_set t) (to_ident_set v)
    | tProd na ty body => IdentSet.union (to_ident_set ty) (to_ident_set body)
    | tLambda na ty body => IdentSet.union (to_ident_set ty) (to_ident_set body)
    | tLetIn na def def_ty body => IdentSet.union (to_ident_set def) (IdentSet.union (to_ident_set def_ty) (to_ident_set body))
    | tApp f args => IdentSet.union (to_ident_set f) (to_set to_ident_set args)
    | tConst _ _ | tInd _ _ | tConstruct _ _ _ => IdentSet.empty
    | tCase ind p discr brs =>
        IdentSet.union (to_set to_ident_set (pparams p))
        (IdentSet.union (to_ident_set (preturn p))
        (IdentSet.union (to_ident_set discr)
        (to_set (fun b => (to_ident_set b.(bbody))) brs
        )))
    | tProj proj t => to_ident_set t
    | tFix mfix idx => to_set (fun d => IdentSet.union (to_ident_set d.(dtype)) (to_ident_set d.(dbody))) mfix
    | tCoFix mfix idx => to_set (fun d => IdentSet.union (to_ident_set d.(dtype)) (to_ident_set d.(dbody))) mfix
    | tInt _ | tFloat _ | tArray _ _ _ _ => IdentSet.empty
    end.

    Definition fresh (i : ident) (s : IdentSet.t) : ident :=
      let s' := IdentSet.filter (String.prefix i) s in
      if (IdentSet.is_empty s') then i else (String.append i (MCString.string_of_nat (IdentSet.cardinal s))).

    Definition open (n : name) (t : term) : ident × term :=
      let i' := (match n with | nNamed i => i | nAnon => "x" end)
      in let i'' := fresh i' (to_ident_set t)
      in (i',t{0 := tVar i'}).

    Fixpoint close (i : ident) (k : nat) t : term :=
      match t with
      | tRel i => tRel (if Nat.leb k i then (S i) else i)
      | tVar id => if (String.eqb i id) then tRel k else tVar id
      | tEvar ev args => tEvar ev (List.map (close i k) args)
      | tLambda na T M => tLambda na (close i k T) (close i (S k) M)
      | tApp u v => tApp (close i k u) (List.map (close i k) v)
      | tProd na A B => tProd na (close i k A) (close i (S k) B)
      | tCast c kind t => tCast (close i k c) kind (close i k t)
      | tLetIn na b t b' => tLetIn na (close i k b) (close i k t) (close i (S k) b')
      | tCase ind p c brs =>
        let k' := List.length (pcontext p) + k in
        let p' := map_predicate id (close i k) (close i k') p in
        let brs' := map_branches_k (close i) k brs in
        tCase ind p' (close i k c) brs'
      | tProj p c => tProj p (close i k c)
      | tFix mfix idx =>
        let k' := List.length mfix + k in
        let mfix' := List.map (map_def (close i k) (close i k')) mfix in
        tFix mfix' idx
      | tCoFix mfix idx =>
        let k' := List.length mfix + k in
        let mfix' := List.map (map_def (close i k) (close i k')) mfix in
        tCoFix mfix' idx
      | tArray u a def ty =>
        tArray u (List.map (close i k) a) (close i k def) (close i k ty)
      | x => x
      end.

End MetaCoqLocallyNameless.

Definition is_lift (t : term) := (noccur_between 0 1 t).

(* ideally, we should fuse is_lift and strengthen (having the latter return an optional value),
  but that would mean having strengthen living in the option monad, which is painful *)

Fixpoint strengthen (n k : nat) t : term :=
  match t with
  | tRel i => tRel (if Nat.leb (k + n) i then (i - n) else i)
  | tVar id => tVar id
  | tEvar ev args => tEvar ev (List.map (strengthen n k) args)
  | tLambda na T M => tLambda na (strengthen n k T) (strengthen n (S k) M)
  | tApp u v => tApp (strengthen n k u) (List.map (strengthen n k) v)
  | tProd na A B => tProd na (strengthen n k A) (strengthen n (S k) B)
  | tCast c kind t => tCast (strengthen n k c) kind (strengthen n k t)
  | tLetIn na b t b' => tLetIn na (strengthen n k b) (strengthen n k t) (strengthen n (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (strengthen n k) (strengthen n k') p in
    let brs' := map_branches_k (strengthen n) k brs in
    tCase ind p' (strengthen n k c) brs'
  | tProj p c => tProj p (strengthen n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (strengthen n k) (strengthen n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (strengthen n k) (strengthen n k')) mfix in
    tCoFix mfix' idx
  | tArray u a def ty =>
    tArray u (List.map (strengthen n k) a) (strengthen n k def) (strengthen n k ty)
  | x => x
  end.

Definition unlift (t : term) := strengthen 0 1 t.

Definition type_of_constructor@{t u} mdecl (c : inductive * nat) : TemplateMonad@{t u} term :=
  match nth_error (ind_bodies mdecl) (inductive_ind (Datatypes.fst c)) with
  | None => tmFail ("inductive not found")
  | Some idecl =>
      match nth_error (ind_ctors idecl) (Datatypes.snd c) with
      | None => tmFail ("constructor not found")
      | Some cdecl => tmReturn (Template.Typing.type_of_constructor mdecl cdecl c nil)
      end
  end.

Definition constType@{t u} (q : qualid) : TemplateMonad@{t u} term :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstructRef ind n =>
      mdecl <- (tmQuoteInductive ind.(inductive_mind)) ;;
      type_of_constructor mdecl (Datatypes.pair ind n)
  | _ => tmFail ("[" ++ q ++ "] is not a constructor")
  end.

#[bypass_check(guard)]Fixpoint under_prod (f : term -> term) (hyp : term) {struct hyp} : term :=
  match hyp with
  | tProd na A b =>
      if is_lift b then f hyp else
      let (i,b') := open (binder_name na) b in
      tProd na A (close i 0 (under_prod f b')) 
  | hyp => f hyp
  end.

Fixpoint concl (hyp : term) : term :=
  match hyp with
  | tProd na A b =>
      if is_lift b then unlift (concl b) else hyp
  | hyp => hyp
  end.


Fixpoint premise_preserve (pre_cond post_cond : term -> term) (n : nat) (ty : term) : term :=
  match ty, n with
  | tProd na h ty', 0 => tProd na (pre_cond (concl (unlift ty'))) (pre_cond h)
  | tProd na h ty', S n' => tProd na (post_cond h) (premise_preserve pre_cond post_cond n' ty')
  | _, _ => tRel 0
  end.

Fixpoint concl_preserve (pre_cond post_cond : term -> term) (ty : term) : term :=
  match ty with
  | tProd na h ty' => tProd na (post_cond h) (concl_preserve pre_cond post_cond ty')
  | concl => tProd {| binder_name := nAnon ; binder_relevance := Relevant |} (pre_cond concl) (post_cond concl)
  end.

Definition constructor_premise_preserve (pre_cond post_cond : term -> term) (n : nat) (q : qualid) :
  TemplateMonad Type :=
  t <- (constType q) ;;
  tmUnquoteTyped Type (under_prod (premise_preserve pre_cond post_cond n) t)
  >>= (tmEval cbn).

Definition constructor_concl_preserve (pre_cond post_cond : term -> term) (q : qualid) :
  TemplateMonad Type :=
  t <- (constType q) ;;
  tmUnquoteTyped Type (under_prod (concl_preserve pre_cond post_cond) t)
  >>= (tmEval cbn).