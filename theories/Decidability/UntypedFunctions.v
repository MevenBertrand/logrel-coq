(** * LogRel.Decidability.UnytpedFunctions: implementation of untyped conversion. *)
From Coq Require Import Nat Lia.
From Equations Require Import Equations.
From PartialFun Require Import Monad PartialFun MonadExn.
From LogRel Require Import Utils BasicAst AutoSubst.Extra Context NormalForms.
From LogRel.Decidability Require Import Functions.

Import MonadNotations.
Set Universe Polymorphism.

Inductive nf_view2 : term -> term -> Type :=
| sorts2 (s1 s2 : sort) : nf_view2 (tSort s1) (tSort s2)
| prods2 (A A' B B' : term) :
    nf_view2 (tProd A B) (tProd A' B')
| nats2 : nf_view2 tNat tNat
| emptys2 : nf_view2 tEmpty tEmpty
| sigs2 (A A' B B' : term) : nf_view2 (tSig A B) (tSig A' B')
| ids2 A A' x x' y y' : nf_view2 (tId A x y) (tId A' x' y')
| lams2 A A' t t' : nf_view2 (tLambda A t) (tLambda A' t')
| lam_ne2 A t n' : nf_view2 (tLambda A t) n'
| ne_lam2 n A' t' : nf_view2 n (tLambda A' t')
| zeros2 : nf_view2 tZero tZero
| succs2 t t' : nf_view2 (tSucc t) (tSucc t')
| pairs2 A A' B B' t t' u u' :
    nf_view2 (tPair A B t u) (tPair A' B' t' u')
| pair_ne2 A B t u n' :
    nf_view2 (tPair A B t u) n'
| ne_pair2 n A' B' t' u' :
    nf_view2 n (tPair A' B' t' u')
| refls2 A A' x x' : nf_view2 (tRefl A x) (tRefl A' x')
| neutrals2 (n n' : term) : nf_view2 n n'
| mismatch2 (t u : term) : nf_view2 t u
| anomaly2 (t u : term) : nf_view2 t u.

Equations build_nf_view2 (t t' : term) : nf_view2 t t' :=
  build_nf_view2 t t' with (build_nf_view1 t) := {
  | nf_view1_type (eSort s) with (build_nf_view1 t') := {
    | nf_view1_type (eSort s') := sorts2 s s' ;
    | nf_view1_type _ := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ;
    | _ := anomaly2 _ _ } ;
  | nf_view1_type (eProd A B) with (build_nf_view1 t') := {
    | nf_view1_type (eProd A' B') := prods2 A A' B B' ;
    | nf_view1_type _ := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ;
    | _ := anomaly2 _ _ } ;
  | nf_view1_type eNat with (build_nf_view1 t') := {
    | nf_view1_type eNat := nats2 ;
    | nf_view1_type _ := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ;
    | _ := anomaly2 _ _ } ;
  | nf_view1_type eEmpty with (build_nf_view1 t') := {
    | nf_view1_type eEmpty := emptys2 ;
    | nf_view1_type _ := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ; 
    | _ := anomaly2 _ _ } ;
  | nf_view1_type (eSig A B) with (build_nf_view1 t') := {
    | nf_view1_type (eSig A' B') := sigs2 A A' B B' ;
    | nf_view1_type _ := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ;
    | _ := anomaly2 _ _ } ;
  | nf_view1_type (eId A x y) with (build_nf_view1 t') := {
    | nf_view1_type (eId A' x' y') := ids2 A A' x x' y y' ;
    | nf_view1_type _ := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ;
    | _ := anomaly2 _ _ } ;
  | nf_view1_fun A t with (build_nf_view1 t') := {
    | nf_view1_fun A' t' := lams2 A A' t t' ;
    | nf_view1_ne _ := lam_ne2 A t _ ; 
    | _ := anomaly2 _ _ } ;
  | nf_view1_nat eZero with (build_nf_view1 t') := {
    | nf_view1_nat eZero := zeros2 ;
    | nf_view1_nat (eSucc _) := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ; 
    | _ := anomaly2 _ _ } ;
  | nf_view1_nat (eSucc u) with (build_nf_view1 t') := {
    | nf_view1_nat (eSucc u') := succs2 u u' ;
    | nf_view1_nat eZero := mismatch2 _ _ ;
    | nf_view1_ne _ := mismatch2 _ _ ; 
    | _ := anomaly2 _ _ } ;
  | nf_view1_sig A B t u with (build_nf_view1 t') := {
    | nf_view1_sig A' B' t' u' := pairs2 A A' B B' t t' u u' ;
    | nf_view1_ne _ := pair_ne2 A B t u _ ; 
    | _ := anomaly2 _ _ } ;
  | nf_view1_id A x with (build_nf_view1 t') := {
    | nf_view1_id A' x' := refls2 A A' x x' ;
    | nf_view1_ne _ := mismatch2 _ _ ;
    | _ := anomaly2 _ _ } ;
  | nf_view1_ne _ with (build_nf_view1 t') := {
    | nf_view1_type _ := mismatch2 _ _ ;
    | nf_view1_fun A' t' := ne_lam2 _ A' t' ;
    | nf_view1_nat _ := mismatch2 _ _ ;
    | nf_view1_sig A' B' t' u' := ne_pair2 _ A' B' t' u' ;
    | nf_view1_id _ _ := mismatch2 _ _ ;
    | nf_view1_ne _ := neutrals2 _ _ ;
  }
}.

Variant uconv_state : Type :=
  | tm_state (** Conversion of arbitrary terms *)
  | tm_red_state (** Comparison of terms in weak-head normal forms *)
  | ne_state. (** Comparison of neutrals *)

Section Conversion.

Definition uconv_dom := uconv_state × term × term.
Definition uconv_cod (_ : uconv_dom) := exn errors unit.

#[local]
Notation M0 := (orec (Sing wh_red) (uconv_dom) (uconv_cod)).
#[local]
Notation M := (combined_orec (exn errors) (Sing wh_red) uconv_dom uconv_cod).

Equations uconv_tm : (term × term) -> M unit :=
  | (t,u) :=
    t' ← call_single wh_red t ;;[M0]
    u' ← call_single wh_red u ;;[M0]
    rec (tm_red_state,t',u').
    
Equations uconv_tm_red : (term × term) -> M unit :=
  | (t,t') with (build_nf_view2 t t') :=
  {
    | sorts2 s s' :=
        ret (eq_sort s s') ;
    | prods2 A A' B B' :=
        rec (tm_state,A,A') ;;
        rec (tm_state,B,B') ;
    | nats2 := ok ;
    | emptys2 := ok ;
    | sigs2 A A' B B' :=
        rec (tm_state,A,A') ;;
        rec (tm_state,B,B') ;
    | ids2 A A' x x' y y' :=
        rec (tm_state,A,A') ;;
        rec (tm_state,x,x') ;;
        rec (tm_state,y,y') ;
    | lams2 _ _ t t' :=
        rec (tm_state,t,t') ;
    | lam_ne2 _ t t' :=
        rec (tm_state,t,eta_expand t') ;
    | ne_lam2 t _ t' :=
        rec (tm_state,eta_expand t,t') ;
    | zeros2 := ok ;
    | succs2 t t' :=
        rec (tm_state,t,t') ;
    | pairs2 _ _ _ _ t t' u u' :=
        rec (tm_state,t,t') ;;
        rec (tm_state,u,u') ;
    | pair_ne2 _ _ t u t' :=
        rec (tm_state,t,tFst t') ;;
        rec (tm_state,u,tSnd t') ;
    | ne_pair2 t _ _ t' u' :=
        rec (tm_state,tFst t, t') ;;
        rec (tm_state,tSnd t,u') ;
    | refls2 A A' x x' := 
      ok ;
    | neutrals2 _ _ :=
      rec (ne_state,t,t') ;
    | mismatch2 _ _ := raise head_mismatch ;
    | anomaly2 _ _ := undefined ;
  }.

Equations uconv_ne : (term × term) -> M unit :=
  uconv_ne (t,t') with build_ne_view2 t t' :=
  {
  | ne_rels n n' with n =? n' :=
    { | false := raise variable_mismatch ;
      | true := ok ;
    } ;
      
  | ne_apps n t n' t' :=
    rec (ne_state,n,n') ;;
    rec (tm_state,t,t') ;

  | ne_nats n P hz hs n' P' hz' hs' :=
    rec (ne_state,n,n') ;;
    rec (tm_state,P,P') ;;
    rec (tm_state,hz,hz') ;;
    rec (tm_state,hs,hs')

  | ne_emptys n P n' P' :=
    rec (ne_state,n,n') ;;
    rec (tm_state,P,P')

  | ne_fsts n n' :=
    rec (ne_state,n,n')

  | ne_snds n n' :=
    rec (ne_state,n,n')

  | ne_ids A x P hr y n A' x' P' hr' y' n' :=
      rec (ne_state,n,n') ;;
      rec (tm_state,P,P') ;;
      rec (tm_state,hr,hr') ;

  | ne_mismatch _ _ => raise destructor_mismatch ;
  | ne_anomaly _ _ => undefined
}.

Equations _uconv : ∇ _ : uconv_state × term × term, [Sing wh_red]⇒[exn errors] unit :=
  | (tm_state,t,u) := uconv_tm (t,u) ;
  | (tm_red_state,t,u) := uconv_tm_red (t,u);
  | (ne_state,t,u) := uconv_ne (t,u).

  #[local] Instance: PFun _uconv := pfun_gen _ _ _uconv.

  Equations uconv : (context × term × term) ⇀ exn errors unit :=
    uconv (Γ,T,V) := call _uconv (tm_state,T,V).
  
End Conversion.

#[export] Instance: PFun uconv := pfun_gen _ _ uconv.