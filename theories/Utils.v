(** * LogRel.Utils: basic generically useful definitions, notations, tactics… *)
From Coq Require Import Morphisms List CRelationClasses.
From Coq Require Import ssrbool.
From smpl Require Import Smpl.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Primitive Projections.

(** ** General Notations *)

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |").
Notation "`=1`" := (pointwise_relation _ Logic.eq) (at level 80).
Infix "=1" := (pointwise_relation _ Logic.eq) (at level 70).
Notation "`=2`" := (pointwise_relation _ (pointwise_relation _ Logic.eq)) (at level 80).
Infix "=2" := (pointwise_relation _ (pointwise_relation _ Logic.eq)) (at level 70).
Infix "<~>" := iffT (at level 90).

(** Since we work a lot with type-level propositions,
we override the notation for negation from the
standard library. **)
#[export] Set Warnings "-notation-overridden".
Notation "~ x" := (notT x) : type_scope.
#[export] Set Warnings "notation-overridden".


#[global]Hint Unfold notT: core.

(** ** Polymorphic and cumulative redefinitions from the standard library. *)

#[universes(polymorphic)]
Definition tr@{u v} {A : Type@{u}} (P : A -> Type@{v}) {x y : A} (e: x = y) : P x -> P y :=
    match e in _ = z return P x -> P z with
    | eq_refl => fun w => w
    end.

#[universes(polymorphic)]
Lemma lrefl {A R} `{!PER R} {a b : A} : R a b -> R a a.
Proof.
  intros; etransitivity;[|symmetry]; eassumption.
Qed.

#[universes(polymorphic)]
Lemma urefl {A R} `{!PER R} {a b : A} : R a b -> R b b.
Proof.
  intros; etransitivity;[symmetry|]; eassumption.
Qed.

Inductive prod (A B : Type) : Type := | pair : A -> B -> prod A B.
Arguments pair {_ _} _ _.

Definition fst {A B} : prod A B -> A := fun '(pair a b) => a.
Definition snd {A B} : prod A B -> B := fun '(pair a b) => b.


Notation "( x , .. , y , z )" := (pair x .. (pair y z) ..) : core_scope.

Notation "x × y" := (prod x y) (at level 80, right associativity).
Reserved Notation "[ × P1 & P2 ]" (at level 0).
Reserved Notation "[ × P1 , P2 & P3 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 ']' '/ '  &  P3 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 & P4 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 ']' '/ '  &  P4 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 & P5 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  &  P5 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6  ']' '/ '  &  P7 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 ']' '/ '  &  P8 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 ']' '/ '  &  P9 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/'  P9 ']' '/ '  &  P10 ] ']'").

Variant and3 (P1 P2 P3 : Type) : Type := Times3 of P1 & P2 & P3.
Variant and4 (P1 P2 P3 P4 : Type) : Type := Times4 of P1 & P2 & P3 & P4.
Variant and5 (P1 P2 P3 P4 P5 : Type) : Type := Times5 of P1 & P2 & P3 & P4 & P5.
Variant and6 (P1 P2 P3 P4 P5 P6 : Type) : Type := Times6 of P1 & P2 & P3 & P4 & P5 & P6.
Variant and7 (P1 P2 P3 P4 P5 P6 P7 : Type) : Type := Times7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Variant and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Type) : Type := Times8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Variant and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Type) : Type := Times9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Variant and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Type) : Type := Times10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.

Notation "[ × P1 & P2 ]" := (prod P1 P2) (only parsing) : type_scope.
Notation "[ × P1 , P2 & P3 ]" := (and3 P1 P2 P3) : type_scope.
Notation "[ × P1 , P2 , P3 & P4 ]" := (and4 P1 P2 P3 P4) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 & P5 ]" := (and5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.

#[global] Hint Constructors prod and3 and3 and5 and6 and7 and8 and9 : core.

Inductive sigT {A : Type} (P : A -> Type) : Type :=
  | existT (projT1 : A) (projT2 : P projT1) : sigT P.

Definition projT1 {A P} (x : @sigT A P) : A := let '(existT _ a _) := x in a.
Definition projT2 {A P} (x : @sigT A P) : P (projT1 x) := let '(existT _ _ p) := x in p.

Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; .. ; y ; z )" := (existT _ x .. (existT _ y z) ..) : core_scope.
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").

#[global] Hint Constructors sigT : core.

(** ** Reflexive and Transitivite closure of a (proof-relevant) relation *)

Section ReflexiveTransitiveClosure.
  Universe u v.
  Context {A : Type@{u}} (R : A -> A -> Type@{v}).

  Inductive reflTransClos : A -> A -> Type@{v} :=
  | rtc_refl {x} : reflTransClos x x
  | rtc_step {x y z} : R x y -> reflTransClos y z -> reflTransClos x z.

  #[global] Instance rtc_reflexive : Reflexive reflTransClos.
  Proof. constructor; apply rtc_refl. Defined.

  #[global] Instance rtc_transitive : Transitive reflTransClos.
  Proof.
    intros ?? z r; induction r in z |- *.
    + easy.
    + intros ?%IHr. eapply rtc_step; eassumption.
  Defined.
End ReflexiveTransitiveClosure.



(** ** Tactics *)

(* To use in intro patterns, similar to SSReflects' /dup view *)
Definition dup {A : Type} : A -> A × A := fun x => (x,x).

Ltac tea := try eassumption.
#[global] Ltac easy ::= solve [intuition eauto 3 with core crelations].

Ltac prod_splitter :=
  repeat match goal with
  | |- sigT _ => eexists
  | |- prod _ _ => split
  | |- and3 _ _ _ => split
  | |- and4 _ _ _ _ => split
  | |- and5 _ _ _ _ _ => split
  | |- _ /\ _ => split
  end.

Ltac prod_hyp_splitter :=
  repeat match goal with
    | H : ∑ _, _ |- _ => destruct H
    | H : [× _ & _] |- _ => destruct H
    | H : [× _, _ & _] |- _ => destruct H
    | H : [× _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _, _, _, _ & _] |- _ => destruct H
  end.

Ltac by_prod_splitter :=
  solve [now prod_splitter].

(** The database used for generic typing *)
Create HintDb gen_typing.
#[global] Hint Constants Opaque : gen_typing.
#[global] Hint Variables Transparent : gen_typing.

Ltac gen_typing := typeclasses eauto bfs 6 with gen_typing typeclass_instances.
Ltac gtyping := timeout 2 gen_typing.

(** A general refolding tactic to recover lost typeclasses
  (due for instance to the cbn or constructor tactics).
  Updated on the fly using the Smpl plugin. *)
Smpl Create refold [progress].

Ltac refold := repeat (smpl refold).

Ltac core_constructor := constructor.
Tactic Notation "constructor" := core_constructor ; refold.

Ltac core_econstructor := econstructor.
Tactic Notation "econstructor" := core_econstructor ; refold.

(** A tactic for presuppositions, ie deriving the well-formation of parts of a typing
judgment from said typing judgement. For instance, [Γ |- A] from [Γ |- t : A].
Made stronger over time, as we prove more of these properties. *)

Create HintDb boundary.
#[global] Hint Constants Opaque : boundary.
#[global] Hint Variables Transparent : boundary.

Ltac boundary := solve[eauto 3 with boundary typeclass_instances].

(** Tactics used to create good induction principles using Scheme *)

Ltac polymorphise t :=
  lazymatch t with
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
        let T' := ltac:(eval hnf in (T x)) in let T'' := polymorphise T' in exact T''))
    | (?t1 * ?t2)%type => let t1' := polymorphise t1 in let t2' := polymorphise t2 in
        constr:(t1' × t2')
    | ?t' => t'
  end.

Ltac remove_steps t :=
  lazymatch t with
  | _ -> ?T => remove_steps T
  | forall x : ?Hyp, @?T x => constr:(fun  x : Hyp => ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := remove_steps T' in exact T''))
  | ?t' => t'
  end.

Definition NotShelved (A:Type) := A.
Definition Shelved (A:Type) := A.

(** Opaque econstructor:
  similar to unshelve econstructor but makes the unshelved goal opaque in subsquent goals.
  Provided by Gaetan Gilbert, modified K.M for recursive dependencies
*)
Ltac gen_shelved_evar_rec :=
  repeat match goal with
      |- context [ ?x ] =>
        is_evar x;
        let t := type of x in
        match t with
          Shelved ?t' =>
            (* cast to t' so that we get a name based on the real type in intro
                instead of "s" based on "Shelved" *)
            generalize (x:t');
            try gen_shelved_evar_rec ;
            intro
        end
  end.

Ltac opector :=
  unshelve (econstructor;match goal with |- ?g => change (NotShelved g) end);
  match goal with |- NotShelved ?g => idtac | |- ?g => change (Shelved g) end; revgoals;
  match goal with
    |- NotShelved ?g => change g; gen_shelved_evar_rec
    | |- Shelved ?g => change g; gen_shelved_evar_rec
  end; revgoals.

(** To block and unblock hypotheses from the context
  (see the tactic escape in LogicalRelations/Escape.v for example)*)
Definition Block (A : Type) := A.

Ltac block H :=
  let T := type of H in (change T with (Block T) in H).

Ltac unblock := unfold Block in *.

(** To get warnings whenever needed *)

#[deprecated(note="Fix me!")]Axiom fixme : False.



(** Pairs and dependent pairs with primitive projections *)

#[projections(primitive)]
Record nprod {A B : Type} := npair { nfst : A ; nsnd : B }.
Arguments nprod : clear implicits.
Arguments npair {_ _} _ _.
Notation "x <&> y" := (nprod x y) (at level 80, right associativity).
Notation "'(&' x , .. , y , z )" := (npair x .. (npair y z) ..) : core_scope.

#[projections(primitive)]
Record sum {A : Type} {B : A -> Type} :=
  dpair { dfst : A ; dsnd : B dfst }.
Arguments sum : clear implicits.
Arguments dpair {_ _} _ _.

Notation "'∑&' x .. y , p" := (sum _ (fun x => .. (sum _ (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑&'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation "'(&' x ; .. ; y ; z )" := (dpair x .. (dpair y z) ..) : core_scope.


(** Indexed partial-equivalence relation (IPER) over a PER *)

Class IPER {A : Type} {R} `{PER A R} {B : A -> Type}
  {S : forall {a1 a2} (a12 : R a1 a2), B a1 -> B a2 -> Type} := {
  isym : forall {a1 a2 : A} {a12 : R a1 a2} {b1 b2}, S a12 b1 b2 -> S (symmetry a12) b2 b1 ;
  itrans : forall {a1 a2 a3 : A} {a12 : R a1 a2} {a23: R a2 a3}
      {b1 b2 b3} (b12 : S a12 b1 b2) (b23 : S a23 b2 b3),
      S (transitivity a12 a23) b1 b3 ;
}.
Arguments IPER {_} _ {_}.

Section PackedIPER.
  Context {A : Type} {R} `{PER A R} {B S} `{IPER A R B S}.
  Arguments S {_ _}.

  Definition packed_iper : crelation (∑& a : A, B a) :=
    fun p q => ∑& (w : R (dfst p) (dfst q)), S w (dsnd p) (dsnd q).

  Definition mk_packed_iper p q (w : R (dfst p) (dfst q)) :
    S w (dsnd p) (dsnd q) -> packed_iper p q :=
    dpair w.

  Definition packed_iper_per : PER packed_iper.
  Proof.
    constructor; red.
    - intros ?? w; exists (symmetry w.(dfst)); apply isym; exact (w.(dsnd)).
    - intros ??? w w' ; exists (transitivity w.(dfst) w'.(dfst)).
      eapply itrans ; [exact w.(dsnd) | exact w'.(dsnd)].
  Defined.
End PackedIPER.

(* Special case where the family B is constant
  CIPER := Constant Indexed PER*)
Section PackedCIPER.
  Context {A : Type} {R} `{PER A R} {B S} `{IPER A R (fun _ => B) S}.
  Arguments S {_ _}.

  Definition packed_ciper : crelation (A <&> B) :=
    fun p q => ∑& (w : R (nfst p) (nfst q)), S w (nsnd p) (nsnd q).

  Definition mk_packed_ciper p q (w : R (nfst p) (nfst q)) :
    S w (nsnd p) (nsnd q) -> packed_ciper p q :=
    dpair w.

  Definition packed_ciper_per : PER packed_ciper.
  Proof.
    constructor; red.
    - intros ?? w; exists (symmetry w.(dfst)); apply isym; exact (w.(dsnd)).
    - intros ??? w w' ; exists (transitivity w.(dfst) w'.(dfst)).
      eapply itrans ; [exact w.(dsnd) | exact w'.(dsnd)].
  Defined.
End PackedCIPER.


Arguments packed_ciper {_} _ {_} _.

