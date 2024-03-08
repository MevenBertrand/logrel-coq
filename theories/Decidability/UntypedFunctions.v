(** * LogRel.Decidability.UnytpedFunctions: implementation of untyped conversion. *)
From Coq Require Import Nat Lia.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context.
From PartialFun Require Import Monad PartialFun MonadExn.
From LogRel.Decidability Require Import Functions.

Import MonadNotations.
Set Universe Polymorphism.

Inductive nf_view2 : term -> term -> Type :=
| sorts (s1 s2 : sort) : nf_view2 (tSort s1) (tSort s2)
| prods (A A' B B' : term) :
    nf_view2 (tProd A B) (tProd A' B')
| nats : nf_view2 tNat tNat
| emptys : nf_view2 tEmpty tEmpty
| sigs (A A' B B' : term) : nf_view2 (tSig A B) (tSig A' B')
| ids A A' x x' y y' : nf_view2 (tId A x y) (tId A' x' y')
| lams A A' t t' : nf_view2 (tLambda A t) (tLambda A' t')
| lam_ne A t n' : nf_view2 (tLambda A t) n'
| ne_lam n A' t' : nf_view2 n (tLambda A' t')
| zeros : nf_view2 tZero tZero
| succs t t' : nf_view2 (tSucc t) (tSucc t')
| pairs A A' B B' t t' u u' :
    nf_view2 (tPair A B t u) (tPair A' B' t' u')
| pair_ne A B t u n' :
    nf_view2 (tPair A B t u) n'
| ne_pair n A' B' t' u' :
    nf_view2 n (tPair A' B' t' u')
| refls A A' x x' : nf_view2 (tRefl A x) (tRefl A' x')
| neutrals (n n' : term) : nf_view2 n n'
| mismatch (t u : term) : nf_view2 t u
| anomaly (t u : term) : nf_view2 t u.

Equations build_nf_view2 (t t' : term) : nf_view2 t t' :=
  build_nf_view2 t t' with (build_nf_view1 t) := {
  | nf_view1_type (eSort s) with (build_nf_view1 t') := {
    | nf_view1_type (eSort s') := sorts s s' ;
    | nf_view1_type _ := mismatch _ _ ;
    | nf_view1_ne _ := mismatch _ _ ;
    | _ := anomaly _ _ } ;
  | nf_view1_type (eProd A B) with (build_nf_view1 t') := {
    | nf_view1_type (eProd A' B') := prods A A' B B' ;
    | nf_view1_type _ := mismatch _ _ ;
    | nf_view1_ne _ := mismatch _ _ ;
    | _ := anomaly _ _ } ;
  | nf_view1_type eNat with (build_nf_view1 t') := {
    | nf_view1_type eNat := nats ;
    | nf_view1_type _ := mismatch _ _ ;
    | nf_view1_ne _ := mismatch _ _ ;
    | _ := anomaly _ _ } ;
  | nf_view1_type eEmpty with (build_nf_view1 t') := {
    | nf_view1_type eEmpty := emptys ;
    | nf_view1_type _ := mismatch _ _ ; 
    | _ := anomaly _ _ } ;
  | nf_view1_type (eSig A B) with (build_nf_view1 t') := {
    | nf_view1_type (eSig A' B') := sigs A A' B B' ;
    | nf_view1_type _ := mismatch _ _ ;
    | nf_view1_ne _ := mismatch _ _ ;
    | _ := anomaly _ _ } ;
  | nf_view1_type (eId A x y) with (build_nf_view1 t') := {
    | nf_view1_type (eId A' x' y') := ids A A' x x' y y' ;
    | nf_view1_type _ := mismatch _ _ ;
    | nf_view1_ne _ := mismatch _ _ ;
    | _ := anomaly _ _ } ;
  | nf_view1_fun A t with (build_nf_view1 t') := {
    | nf_view1_fun A' t' := lams A A' t t' ;
    | nf_view1_ne _ := lam_ne A t _ ; 
    | _ := anomaly _ _ } ;
  | nf_view1_nat eZero with (build_nf_view1 t') := {
    | nf_view1_nat eZero := zeros ;
    | nf_view1_nat (eSucc _) := mismatch _ _ ;
    | nf_view1_ne _ := mismatch _ _ ; 
    | _ := anomaly _ _ } ;
  | nf_view1_nat (eSucc u) with (build_nf_view1 t') := {
    | nf_view1_nat (eSucc u') := succs u u' ;
    | nf_view1_nat eZero := mismatch _ _ ;
    | nf_view1_ne _ := mismatch _ _ ; 
    | _ := anomaly _ _ } ;
  | nf_view1_sig A B t u with (build_nf_view1 t') := {
    | nf_view1_sig A' B' t' u' := pairs A A' B B' t t' u u' ;
    | nf_view1_ne _ := pair_ne A B t u _ ; 
    | _ := anomaly _ _ } ;
  | nf_view1_id A x with (build_nf_view1 t') := {
    | nf_view1_id A' x' := refls A A' x x' ;
    | nf_view1_ne _ := mismatch _ _ ;
    | _ := anomaly _ _ } ;
  | nf_view1_ne _ with (build_nf_view1 t') := {
    | nf_view1_type _ := mismatch _ _ ;
    | nf_view1_fun A' t' := ne_lam _ A' t' ;
    | nf_view1_nat _ := mismatch _ _ ;
    | nf_view1_sig A' B' t' u' := ne_pair _ A' B' t' u' ;
    | nf_view1_id _ _ := mismatch _ _ ;
    | nf_view1_ne _ := neutrals _ _ ;
  }
  }.

  Variant uconv_state : Type :=
  | tm_state (** Conversion of arbitrary terms *)
  | tm_red_state (** Comparison of terms if weak-head normal forms *)
  | ne_state. (** Comparison of neutrals *)

Section Conversion.

Definition uconv_dom := uconv_state × term × term.
Definition uconv_cod (_ : uconv_dom) := exn errors unit.

#[local]
Notation M0 := (orec (Sing wh_red) (uconv_dom) (uconv_cod)).
#[local]
Notation M := (combined_orec (exn errors) (Sing wh_red) uconv_dom uconv_cod).

(* Equations uconv_ty :
  (term × term) -> M unit :=
  | (T,V) :=
    T' ← call_single wh_red T ;;[M0]
    V' ← call_single wh_red V ;;[M0]
    id <*> rec (ty_red_state,T',V').

Equations uconv_ty_red : 
  (term × term) -> M unit :=
  | (T,T') with (build_nf_ty_view2 T T') :=
  {
    | ty_sorts s s' := ret (eq_sort s s') ;
    | ty_prods A A' B B' :=
        rec (ty_state,A,A') ;;
        rec (ty_state,B,B') ;
    | ty_nats := ok ;
    | ty_emptys := ok ;
    | ty_sigs A A' B B' :=
        rec (ty_state,A,A') ;;
        rec (ty_state,B,B') ;
      | ty_neutrals _ _ :=
          rec (ne_state,T,T') ;
    | ty_ids A A' x x' y y' :=
      rec (ty_state,A,A') ;;
      rec (tm_state,x,x') ;;
      rec (tm_state,y,y') ;
    | ty_mismatch _ _ := raise (head_mismatch None T T') ;
    | ty_anomaly _ _ := undefined ;
  }. *)

Equations uconv_tm : (term × term) -> M unit :=
  | (t,u) :=
    t' ← call_single wh_red t ;;[M0]
    u' ← call_single wh_red u ;;[M0]
    id <*> rec (tm_red_state,t',u').
    
Equations uconv_tm_red : (term × term) -> M unit :=
  | (t,t') with (build_nf_view2 t t') :=
  {
    | sorts s s' :=
        ret (eq_sort s s') ;
    | prods A A' B B' :=
        rec (tm_state,A,A') ;;
        rec (tm_state,B,B') ;
    | nats := ok ;
    | emptys := ok ;
    | sigs A A' B B' :=
        rec (tm_state,A,A') ;;
        rec (tm_state,B,B') ;
    | ids A A' x x' y y' :=
        rec (tm_state,A,A') ;;
        rec (tm_state,x,x') ;;
        rec (tm_state,y,y') ;
    | lams _ _ t t' :=
        rec (tm_state,t,t') ;
    | lam_ne _ t t' :=
        rec (tm_state,t,eta_expand t') ;
    | ne_lam t _ t' :=
        rec (tm_state,eta_expand t,t') ;
    | zeros := ok ;
    | succs t t' :=
        rec (tm_state,t,t') ;
    | pairs _ _ _ _ t t' u u' :=
        rec (tm_state,t,t') ;;
        rec (tm_state,u,u') ;
    | pair_ne _ _ t u t' :=
        rec (tm_state,t,tFst t') ;;
        rec (tm_state,u,tSnd t') ;
    | ne_pair t _ _ t' u' :=
        rec (tm_state,tFst t, t') ;;
        rec (tm_state,tSnd t,u') ;
    | refls A A' x x' := 
      rec (tm_state,A,A') ;;
      rec (tm_state,x,x') ;
    | neutrals _ _ :=
      rec (ne_state,t,t') ;
    | mismatch _ _ := raise (head_mismatch None t t') ;
    | anomaly _ _ := undefined ;
  }.

Equations uconv_ne : (term × term) -> M unit :=
  | (tRel n , tRel n')
      with n =? n' :=
      { | false := raise (variable_mismatch n n') ;
        | true := ok ;
      } ;
      
  | (tApp n t , tApp n' t') :=
    rec (ne_state,n,n') ;;
    rec (tm_state,t,t') ;

| (tNatElim P hz hs n,tNatElim P' hz' hs' n') :=
  rec (ne_state,n,n') ;;
  rec (tm_state,P,P') ;;
  rec (tm_state,hz,hz') ;;
  rec (tm_state,hs,hs')

| (tEmptyElim P n,tEmptyElim P' n') :=
  rec (ne_state,n,n') ;;
  rec (tm_state,P,P')

| (tFst n , tFst n') :=
  rec (ne_state,n,n')

| (tSnd n , tSnd n') :=
  rec (ne_state,n,n')

| (tIdElim A x P hr y e, tIdElim A' x' P' hr' y' e') :=
    rec (ne_state,e,e') ;;
    rec (tm_state,P,P') ;;
    rec (tm_state,hr,hr')

| (n,n') := raise (destructor_mismatch n n').

Equations _uconv : ∇ _ : uconv_state × term × term, Sing wh_red  ⇒ exn errors ♯ unit :=
  (* | (ty_state,ts) := uconv_ty ts;
  | (ty_red_state,ts) := uconv_ty_red ts ; *)
  | (tm_state,ts) := uconv_tm ts ;
  | (tm_red_state,ts) := uconv_tm_red ts;
  | (ne_state,ts) := uconv_ne ts.

  #[local] Instance: PFun _uconv := pfun_gen _ _ _uconv.

  Equations uconv : (context × term × term) ⇀ exn errors unit :=
    uconv (Γ,T,V) := call _uconv (tm_state,T,V).
  
End Conversion.

#[export] Instance: PFun uconv := pfun_gen _ _ uconv.