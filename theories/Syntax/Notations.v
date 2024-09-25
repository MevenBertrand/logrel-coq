(** * LogRel.Notations: notations for conversion, typing and the logical relations. *)
From LogRel Require Import Utils.
From LogRel.Syntax Require Import BasicAst Context.
From LogRel.AutoSubst Require Import Ast.

(** We have several families of definitions. We discriminate them by using an opaque tag as a phantom type.

All notations come in two versions: the tagged and the untagged one. The untagged one can be used in input only,
ideally wisely in cases where there is only one instance at hand. The tagged one is used systematically in printing,
and can be used in input when disambiguation is desired. *)

Variant tag := mkTag.
Inductive class := istype | isterm : term -> class.

Declare Scope typing_scope.
Delimit Scope typing_scope with ty.

Declare Scope declarative_scope.
Delimit Scope declarative_scope with de.
Close Scope declarative_scope.

Open Scope typing_scope.

(** ** Typing *)
Class WfContext (ta : tag) := wf_context : context -> Set.
Class WfType (ta : tag) := wf_type : context -> term -> Set.
Class Typing (ta : tag) := typing : context -> term -> term -> Set.
Class Inferring (ta : tag) := inferring : context -> term -> term -> Set.
Class InferringRed (ta : tag) := infer_red : context -> term -> term -> Set.
Class Checking (ta : tag) := check : context -> term -> term -> Set.
Class ConvType (ta : tag) := conv_type : context -> term -> term -> Set.
Class ConvTypeRed (ta : tag) := conv_type_red : context -> term -> term -> Set.
Class ConvTerm (ta : tag) := conv_term : context -> term -> term -> term -> Set.
Class ConvTermRed (ta : tag) := conv_term_red : context -> term -> term -> term -> Set.
Class ConvNeu (ta : tag) := conv_neu : context -> term -> term -> term -> Set.
Class ConvNeuRed (ta : tag) := conv_neu_red : context -> term -> term -> term -> Set.
Class ConvNeuConv (ta : tag) := conv_neu_conv : context -> term -> term -> term -> Set.

(** The context Γ is well-formed *)
Notation "[ |- Γ ]" := (wf_context Γ)
  (at level 0, Γ at level 50, only parsing) : typing_scope.
Notation "[ |-[ ta  ] Γ ]" := (wf_context (ta := ta) Γ)
  (at level 0, ta, Γ at level 50) : typing_scope.
(** The contexts Γ and Δ are convertible *)
Reserved Notation "[ |- Γ ≅ Δ ]" (at level 0, Γ, Δ at level 50).
Reserved Notation "[ |-[ ta  ] Γ ≅ Δ ]" (at level 0, ta, Γ, Δ at level 50).
(** The type A is well-formed in Γ *)
Notation "[ Γ |- A ]" := (wf_type Γ A)
  (at level 0, Γ, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ]" := (wf_type (ta := ta) Γ A)
  (at level 0, ta, Γ, A at level 50) : typing_scope.

(** The term t has type A in Γ *)
Notation "[ Γ |- t : A ]" := (typing Γ A t)
  (at level 0, Γ, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t : A ]" :=
  (typing (ta := ta) Γ A t) (at level 0, ta, Γ, t, A at level 50) : typing_scope.

(** The term t checks against type A in Γ *)
Notation "[ Γ |- t ◃ A ]" := (check Γ A t)
  (at level 0, Γ, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ◃ A ]" :=
  (check (ta := ta) Γ A t) (at level 0, ta, Γ, t, A at level 50) : typing_scope.
(** The term t infers A in Γ *)
Notation "[ Γ |- t ▹ A ]" := (inferring Γ A t)
  (at level 0, Γ, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ▹ A ]" :=
  (inferring (ta := ta) Γ A t) (at level 0, ta, Γ, t, A at level 50) : typing_scope.
(** The term t infers the reduced A in Γ *)
Notation "[ Γ |- t ▹h A ]" := (infer_red Γ A t) (at level 0, Γ, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ▹h A ]" := (infer_red (ta := ta) Γ A t) (at level 0, ta, Γ, t, A at level 50) : typing_scope.
(** Types A and B are convertible in Γ *)
Notation "[ Γ |- A ≅ B ]" := (conv_type Γ A B)
  (at level 0, Γ, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ≅ B ]" := (conv_type (ta := ta) Γ A B)
  (at level 0, ta, Γ, A, B at level 50) : typing_scope.
(** Types in whnf A and B are convertible in Γ *)
Notation "[ Γ |- A '≅h' B ]" := (conv_type_red Γ A B) (at level 0, Γ, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A '≅h' B ]" := (conv_type_red (ta := ta) Γ A B) (at level 0, ta, Γ, A, B at level 50) : typing_scope.
(** Terms t and t' are convertible in Γ *)
Notation "[ Γ |- t ≅ t' : A ]" := (conv_term Γ A t t')
  (at level 0, Γ, t, t', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ≅ t' : A ]" := (conv_term (ta := ta) Γ A t t')
  (at level 0, ta, Γ, t, t', A at level 50) : typing_scope.
(** Whnfs t and t' are convertible in Γ *)
Notation "[ Γ |- t '≅h' t' : A ]" := (conv_term_red Γ A t t') (at level 0, Γ, t, t', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t '≅h' t' : A ]" := (conv_term_red (ta := ta) Γ A t t') (at level 0, ta, Γ, t, t', A at level 50) : typing_scope.
(** Neutral n and n' are convertible in Γ, inferring the type A *)
Notation "[ Γ |- n ~ n' ▹ A ]" := (conv_neu Γ A n n')
  (at level 0, Γ, n, n', A at level 50, only parsing) : typing_scope. 
Notation "[ Γ |-[ ta  ] n ~ n' ▹ A ]" := (conv_neu (ta := ta) Γ A n n')
  (at level 0, ta, Γ, n, n', A at level 50) : typing_scope.
(** Neutral n and n' are convertible in Γ, inferring the reduced type A *)
Notation "[ Γ |- n '~h' n' ▹ A ]" := (conv_neu_red Γ A n n') (at level 0, Γ, n, n', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] n '~h' n' ▹ A ]" := (conv_neu_red (ta := ta) Γ A n n') (at level 0, ta, Γ, n, n', A at level 50) : typing_scope.
(** Neutral n and n' are convertible in Γ at type A *)
Notation "[ Γ |- n ~ n' : A ]" := (conv_neu_conv Γ A n n')
  (at level 0, Γ, n, n', A at level 50, only parsing) : typing_scope. 
Notation "[ Γ |-[ ta  ] n ~ n' : A ]" := (conv_neu_conv (ta := ta) Γ A n n')
  (at level 0, ta, Γ, n, n', A at level 50) : typing_scope.

(** ** Untyped Conversion *)

(** Types/terms t and u are convertible *)
Reserved Notation "[ t ≅ u ]" (at level 0, t, u at level 50).
(** Types/terms in whnf t and u are convertible *)
Reserved Notation "[ t '≅h' u ]" (at level 0, t, u at level 50).
(** Neutrals n and n' are convertible *)
Reserved Notation "[ n ~ n' ]" (at level 0, n, n' at level 50).


(** ** Reductions *)
Class RedType (ta : tag) := red_ty : context -> term -> term -> Set.
Class OneStepRedTerm (ta : tag) := osred_tm : context -> term -> term -> term -> Set.
Class RedTerm (ta : tag) := red_tm : context -> term -> term -> term -> Set.

(** Term t untyped one-step weak-head reduces to term t' *)
Reserved Notation "[ t ⤳ t' ]" (at level 0, t, t' at level 50).
(** Term t untyped multi-step weak-head reduces to term t' *)
Reserved Notation "[ t ⤳* t' ]" (at level 0, t, t' at level 50).

(** Type A one-step weak-head reduces to type B in Γ *)
Reserved Notation "[ Γ |- A ⤳ B ]" (at level 0, Γ, A, B at level 50).
(** Term or type t one-step weak-head reduces to term or type type u as class A in Γ *)
Reserved Notation "[ Γ |- t ⤳ u ∈ A ]" (at level 0, Γ, t, u, A at level 50).
(** Term or type t multi-step weak-head reduces to term or type type u as class A in Γ *)
Reserved Notation "[ Γ |- t ⤳* u ∈ A ]" (at level 0, Γ, t, u, A at level 50).
(** Term t one-step weak-head reduces to term u at type A in Γ *)
Notation "[ Γ |- t ⤳ u : A ]" := (osred_tm Γ A t u) (at level 0, Γ, t, u, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ⤳ u : A ]" := (osred_tm (ta:=ta) Γ A t u) (at level 0, ta,Γ, t, u, A at level 50) : typing_scope.
(** Type A multi-step weak-head reduces to type B in Γ *)
Notation "[ Γ |- A ⤳* B ]" := (red_ty Γ A B) (at level 0, Γ, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ⤳* B ]" := (red_ty (ta := ta) Γ A B)
(at level 0, ta, Γ, A, B at level 50) : typing_scope.
(** Term t multi-step weak-head reduces to term t' at type A in Γ *)
Notation "[ Γ |- t ⤳* t' : A ]" := (red_tm Γ A t t')
(at level 0, Γ, t, t', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ⤳* t' : A ]" := (red_tm (ta := ta) Γ A t t')
(at level 0, ta, Γ, t, t', A at level 50) : typing_scope.
(** Set A weak-head normalizes to B in Γ, ie it multi-step reduces to the weak-head normal form B*)
Reserved Notation "[ Γ |- A ↘ B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A ↘ B ]" (at level 0, ta, Γ, A, B at level 50).
(** Term t weak-head normalizes to u at type A in Γ *)
Reserved Notation "[ Γ |- t ↘ u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t ↘ u : A ]" (at level 0, ta, Γ, t, u, A at level 50).

(** ** Substitutions *)

(** Substitution σ is of type Δ in context Γ*)
Reserved Notation "[ Γ '|-s' σ : Δ ]" (at level 0, Γ, σ, Δ at level 50).
Reserved Notation "[ Γ |-[ ta  ']s' σ : Δ ]" (at level 0, ta, Γ, σ, Δ at level 50).
(** Substitutions σ and τ are convertible at types Δ in context Γ *)
Reserved Notation "[ Γ '|-s' σ ≅ τ : Δ ]" (at level 0, Γ, σ, τ, Δ at level 50).
Reserved Notation "[ Γ |-[ ta  ']s' σ ≅ τ : Δ ]" (at level 0, ta, Γ, σ, τ, Δ at level 50).

(** ** Extra typing conditions *)
(** Types A and B are well-formed and convertible in Γ *)
Reserved Notation "[ Γ |- A :≅: B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A :≅: B ]" (at level 0, ta, Γ, A, B at level 50).
(** Terms t and u are well-typed and convertible at type A in Γ *)
Reserved Notation "[ Γ |- t :≅: u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t :≅: u : A ]" (at level 0, ta, Γ, t, u, A at level 50).
(** Set A and B are well-formed and A weak-head reduces to B in Γ *)
Reserved Notation "[ Γ |- A :⤳*: B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A :⤳*: B ]" (at level 0, ta, Γ, A, B at level 50).
(** Terms t and u have type A in Γ and t weak-head reduces to u *)
Reserved Notation "[ Γ |- t :⤳*: u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t :⤳*: u : A ]" (at level 0, ta, Γ, t, u, A at level 50).

(** ** Weakenings *)
(** Well-formed weakening *)
Reserved Notation "Γ ≤ Δ" (at level 40).
(** Composition of weakenings *)
Reserved Notation "ρ ∘w ρ'" (at level 50).


(** ** Logical relation *)
(** The universe is reducible in Γ, according to the kit K *)
Reserved Notation "[ K | Γ ||-U ]" (at level 0, K, Γ at level 50).
(** The type A is reducible as a Π type in Γ according to the kit K *)
Reserved Notation "[ K | Γ ||-Π A ]" (at level 0, K, Γ, A at level 50).
(** The type A is reducible in Γ, according to the kit K *)
Reserved Notation "[ K | Γ ||- A ]"  (at level 0, K, Γ, A at level 50).
(** The types A and B are reducibly convertible in Γ, given the proof R than A is reducible, according to the kit K*)
Reserved Notation "[ K | Γ ||- A ≅ B | R ]" (at level 0, K, Γ, A, B, R at level 50).
(** The term t is reducible at type A in Γ, given the proof R than A is reducible, according to the kit K *)
Reserved Notation "[ K | Γ ||- t : A | R ]"  (at level 0, K, Γ, t, A, R at level 50).
(** The terms t and u are reducibly convertible at type A in Γ, given the proof R than A is reducible, according to the kit K *)
Reserved Notation "[ K | Γ ||- t ≅ u : A | R ]" (at level 0, K, Γ, t, u, A, R at level 50).

(** The types A and B are reducibly equal in Γ, according to the pack P for Γ and A *)
Reserved Notation "[ P | Γ ||- A ≅ B ]" (at level 0, P, Γ, A, B at level 50).
(** The term t is reducible at type A in Γ, according to the pack P *)
Reserved Notation "[ P | Γ ||- t : A ]" (at level 0, P, Γ, t, A at level 50).
(** The terms t and u are reducibly equal at type A in Γ, according to the pack P *)
Reserved Notation "[ P | Γ ||- t ≅ u : A ]" (at level 0, P, Γ, t, u, A at level 50).

(** Set level l is (strictly) smaller than type level l' *)
Reserved Notation "l << l'" (at level 70, l' at next level).

(** A is reducible as a neutral in Γ *)
Reserved Notation "[ Γ ||-ne A ]" (at level 0, Γ, A at level 50).
(** Set B is reducibly convertible to type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne A ≅ B | neA ]" (at level 0, Γ, A, B, neA at level 50).
(** Term t is reducible at type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne t : A | neA ]" (at level 0, Γ, t, A, neA at level 50).
(** Terms t and u are reducibly convertible at type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne t ≅ u : A | neA ]" (at level 0, Γ, t, u, A at level 50).

(** The type U is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-U l ]" (at level 0, Γ, l at level 50).
(** The type B is reducibly convertible to U *)
Reserved Notation "[ Γ ||-U≅ B ]" (at level 0, Γ, B at level 50).
(** The term t is reducible at the universe U, given the proof R that the universe is reducible and the kits rec at lower levels *)
Reserved Notation "[ rec | Γ ||-U t :U | R ]" (at level 0, rec, Γ, t, R at level 50).
(** The terms t and u are reducibly convertible at the universe U, given the same *)
Reserved Notation "[ rec | Γ ||-U t ≅ u :U | R ]" (at level 0, rec, Γ, t, u, R at level 50).


(** The type A has the packs of a reducible Π type in Γ *)
Reserved Notation "[ Γ ||-Πd A ]" (at level 0, Γ, A at level 50).
(** The type B is reducibly convertible to A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π A ≅ B | ΠA ]" (at level 0, Γ, A, B, ΠA at level 50).
(** The term t is reducible at type A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π t : A | ΠA ]" (at level 0, Γ, t, A, ΠA at level 50).
(** The terms t and u are reducibly convertible at type A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π t ≅ u : A | ΠA ]" (at level 0, Γ, t, u, A, ΠA at level 50).

(** The universe is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-< l >U]" (at level 0, Γ, l at level 50).
(** The type A is reducible as a Π type in Γ at level l *)
Reserved Notation "[ Γ ||-< l >Π  A ]" (at level 0, Γ, l, A at level 50).
(** The type A is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-< l >  A ]" (at level 0, Γ, l, A at level 50).
(** The types A and B are reducibly convertible in Γ at level l, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< l >  A ≅ B | R ]" (at level 0, Γ, l, A, B, R at level 50).
(** The term t is reducible at type A and level l in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< l >  t : A | R ]" (at level 0, Γ, l, t, A, R at level 50).
(** The terms t and u are reducibly convertible at type A and level l in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< l > t ≅ u : A | R ]" (at level 0, Γ, l, t, u, A, R at level 50).

(** The type A is reducible in Γ at level 0*)
Reserved Notation "[ Γ ||-<0>  A ]" (at level 0, Γ, A at level 50).
(** The types A and B are reducibly convertible in Γ at level 0, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-<0>  A ≅ B | R ]" (at level 0, Γ, A, B, R at level 50).
(** The term t is reducible at type A and level 0 in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-<0>  t : A | R ]" (at level 0, Γ, t, A, R at level 50).
(** The terms t and u are reducibly convertible at type A and level 0 in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-<0> t ≅ u : A | R ]" (at level 0, Γ, t, u, A, R at level 50).

(** Reducibility notations for identity types *)
Reserved Notation "[ Γ ||-Id< l > A ]" (at level 0, Γ, l,  A at level 50).
Reserved Notation "[ Γ ||-Id< l > A ≅ B | RA ]" (at level 0, Γ, l, A, B, RA at level 50).
Reserved Notation "[ Γ ||-Id< l > t : A | RA ]" (at level 0, Γ, l, t, A, RA at level 50).
Reserved Notation "[ Γ ||-Id< l > t ≅ u : A | RA ]" (at level 0, Γ, l, t, u, A, RA at level 50).




(** ** Validity notations *)
Reserved Notation "[||-v Γ ]" (at level 0, Γ at level 50).
Reserved Notation "[ Δ ||-v σ : Γ | VΓ | wfΔ ]" (at level 0, Δ, σ, Γ, VΓ, wfΔ at level 50).
Reserved Notation "[ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ ]" (at level 0, Δ, σ, σ', Γ, VΓ, wfΔ, vσ at level 50).
Reserved Notation "[ Γ ||-v< l > A | VΓ ]" (at level 0, Γ, l , A, VΓ at level 50).
Reserved Notation "[ P | Δ ||-v σ : Γ | wfΔ ]" (at level 0, P, Δ, σ, Γ, wfΔ at level 50).
Reserved Notation "[ P | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ ]"  (at level 0, P, Δ, σ, σ', Γ, wfΔ, vσ at level 50).
Reserved Notation "[ R | ||-v Γ ]"  (at level 0, R, Γ at level 50).
Reserved Notation "[ R | Δ ||-v σ : Γ | RΓ | wfΔ ]"  (at level 0, R, Δ, σ, Γ, RΓ, wfΔ at level 50).
Reserved Notation "[ R | Δ ||-v σ ≅ σ' : Γ | RΓ | wfΔ | vσ ]" (at level 0, R, Δ, σ, σ', Γ, RΓ, wfΔ, vσ at level 50).
Reserved Notation "[ P | Γ ||-v< l > A ]"  (at level 0, P, Γ, l, A at level 50).

