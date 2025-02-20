(** * LogRel.GenericTyping: the generic interface of typing used to build the logical relation. *)
From Coq Require Import CRelationClasses ssrbool.
From LogRel Require Import Utils Syntax.All.

(** In order to factor the work, the logical relation is defined over a generic
notion of typing (and conversion),
and its properties are established given abstract properties
of this generic notion. This way, we can instantiate the logical relation multiple
times with different instances of this abstract notion of typing, gathering more
and more properties. *)

(**
More precisely, an instance consists of giving notions of
- context well-formation [|- Γ]
- type well-formation [Γ |- A]
- term well-formation [Γ |- t : A]
- convertibility of types [Γ |- A ≅ B]
- convertibility of terms [Γ |- t ≅ u : A]
- neutral convertibility of terms [Γ |- m ~ n : A]
- (multi-step, weak-head) reduction of types [Γ |- A ⤳* B]
- (multi-step, weak-head) reduction of terms [Γ |- t ⤳* u : A]
*)

(** ** Generic definitions *)

(** These can be defined over typing and conversion in a generic way. *)

Section RedDefinitions.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  (** *** Bundling of a predicate with side-conditions *)

  Record TypeRedWhnf (Γ : context) (A B : term) : Type :=
    {
      tyred_whnf_red :> [ Γ |- A ⤳* B ] ;
      tyred_whnf_whnf :> whnf B
    }.

  Record TermRedWhnf (Γ : context) (A t u : term) : Type :=
    {
      tmred_whnf_red :> [ Γ |- t ⤳* u : A ] ;
      tmred_whnf_whnf :> whnf u
    }.

  Record TypeConvWf (Γ : context) (A B : term) : Type :=
    {
      tyc_wf_l : [Γ |- A] ;
      tyc_wf_r : [Γ |- B] ;
      tyc_wf_conv :> [Γ |- A ≅ B]
    }.

  Record TermConvWf (Γ : context) (A t u : term) : Type :=
    {
      tmc_wf_l : [Γ |- t : A] ;
      tmc_wf_r : [Γ |- u : A] ;
      tmc_wf_conv :> [Γ |- t ≅ u : A]
    }.

  Record TypeRedWf (Γ : context) (A B : term) : Type := {
    tyr_wf_r : [Γ |- B];
    tyr_wf_red :> [Γ |- A ⤳* B]
  }.

  Record TermRedWf (Γ : context) (A t u : term) : Type := {
    tmr_wf_r : [Γ |- u : A];
    tmr_wf_red :> [Γ |- t ⤳* u : A]
  }.

  (** *** Lifting of typing and conversion to contexts and substitutions *)

  Inductive WellSubst (Γ : context) : context -> (nat -> term) -> Type :=
    | well_sempty (σ : nat -> term) : [Γ |-s σ : ε ]
    | well_scons (σ : nat -> term) (Δ : context) A :
      [Γ |-s ↑ >> σ : Δ] -> [Γ |- σ var_zero : A[↑ >> σ]] ->
      [Γ |-s σ : Δ,, A]
  where "[ Γ '|-s' σ : Δ ]" := (WellSubst Γ Δ σ).

  Inductive ConvSubst (Γ : context) : context -> (nat -> term) -> (nat -> term) -> Type :=
  | conv_sempty (σ τ : nat -> term) : [Γ |-s σ ≅ τ : ε ]
  | conv_scons (σ τ : nat -> term) (Δ : context) A :
    [Γ |-s ↑ >> σ ≅ ↑ >> τ : Δ] -> [Γ |- σ var_zero ≅ τ var_zero: A[↑ >> σ]] ->
    [Γ |-s σ ≅ τ : Δ,, A]
  where "[ Γ '|-s' σ ≅ τ : Δ ]" := (ConvSubst Γ Δ σ τ).

  Inductive ConvCtx : context -> context -> Type :=
  | conv_cempty : [ |- ε ≅ ε]
  | conv_ccons Γ A Δ B : [ |- Γ ≅ Δ ] -> [Γ |- A ≅ B] -> [ |- Γ,, A ≅ Δ,, B]
  where "[ |- Γ ≅ Δ ]" := (ConvCtx Γ Δ).


  Lemma well_subst_ext Γ Δ (σ σ' : nat -> term) :
    σ =1 σ' ->
    [Γ |-s σ : Δ] ->
    [Γ |-s σ' : Δ].
  Proof.
    intros Heq.
    induction 1 in σ', Heq |- *.
    all: constructor.
    - eapply IHWellSubst.
      now rewrite Heq.
    - rewrite <- Heq.
      now replace A[↑ >> σ'] with A[↑ >> σ]
        by (now rewrite Heq).
  Qed.

  Definition WellClass (Γ : context) (A : class) (t : term) :=
    match A with
      | istype => [Γ |- t]
      | isterm A => [Γ |- t : A]
    end.

  Record well_typed Γ t :=
  {
    well_typed_type : term ;
    well_typed_typed : [Γ |- t : well_typed_type]
  }.

  Record well_formed Γ t :=
  {
    well_formed_class : class ;
    well_formed_typed : WellClass Γ well_formed_class t
  }.

  Definition ConvClass (Γ : context) (A : class) (t u : term) :=
    match A with
      | istype => [Γ |- t ≅ u]
      | isterm A => [Γ |- t ≅ u : A]
    end.

  Record RedClosureClass (Γ : context) (A : class) (t u : term) := {
    reddecl_typ : match A with istype => [Γ |- t] | isterm A => [Γ |- t : A] end;
    reddecl_red : RedClosureAlg t u;
    reddecl_conv : ConvClass Γ A t u ;
  }.

  Inductive isWfFun (Γ : context) (A B : term) : term -> Set :=
    LamWfFun : forall A' t : term,
      [Γ |- A'] -> [Γ |- A ≅ A'] -> [Γ,, A |- t : B] -> [Γ,, A' |- t : B] -> isWfFun Γ A B (tLambda A' t)
  | NeWfFun : forall f : term, [Γ |- f ~ f : tProd A B] -> isWfFun Γ A B f.

  Inductive isWfPair (Γ : context) (A B : term) : term -> Set :=
    PairWfPair : forall A' B' a b : term,
      [Γ |- A'] -> [Γ |- A ≅ A'] ->
      [Γ,, A' |- B] ->
      [Γ,, A' |- B'] ->
      [Γ,, A |- B'] ->
      [Γ,, A |- B ≅ B'] ->
      [Γ,, A' |- B ≅ B'] ->
      [Γ |- a : A] ->
      [Γ |- B[a..]] ->
      [Γ |- B'[a..]] ->
      [Γ |- B[a..] ≅ B'[a..]] ->
      [Γ |- b : B[a..]] ->
      isWfPair Γ A B (tPair A' B' a b)
  | NeWfPair : forall n : term, [Γ |- n ~ n : tSig A B] -> isWfPair Γ A B n.

End RedDefinitions.

Notation "[ Γ |- A ↘ B ]" := (TypeRedWhnf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ↘ B ]" := (TypeRedWhnf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t ↘ u : A ]" := (TermRedWhnf Γ A t u) (only parsing ): typing_scope.
Notation "[ Γ |-[ ta  ] t ↘ u : A ]" := (TermRedWhnf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ |- A :≅: B ]" := (TypeConvWf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A :≅: B ]" := (TypeConvWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :≅: u : A ]" := (TermConvWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :≅: u : A ]" := (TermConvWf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ |- A :⤳*: B ]" := (TypeRedWf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A :⤳*: B ]" := (TypeRedWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :⤳*: u : A ]" := (TermRedWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :⤳*: u : A ]" := (TermRedWf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ '|-s' σ : A ]" := (WellSubst Γ A σ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ : A ]" := (WellSubst (ta := ta) Γ A σ) : typing_scope.
Notation "[ Γ '|-s' σ ≅ τ : A ]" := (ConvSubst Γ A σ τ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ ≅ τ : A ]" := (ConvSubst (ta := ta) Γ A σ τ) : typing_scope.
Notation "[ |- Γ ≅ Δ ]" := (ConvCtx Γ Δ) (only parsing) : typing_scope.
Notation "[ |-[ ta  ] Γ ≅ Δ ]" := (ConvCtx (ta := ta) Γ Δ) : typing_scope.
Notation "[ Γ |- t ∈ A ]" := (WellClass Γ A t) : typing_scope.
Notation "[ Γ |-[ ta  ] t ∈ A ]" := (WellClass (ta := ta) Γ A t) : typing_scope.
Notation "[ Γ |- t ≅ t' ∈ A ]" := (ConvClass Γ A t t') : typing_scope.
Notation "[ Γ |-[ ta  ] t ≅ t' ∈ A ]" := (ConvClass (ta := ta) Γ A t t') : typing_scope.

#[export] Hint Resolve
  Build_TypeRedWhnf Build_TermRedWhnf Build_TypeConvWf
  Build_TermConvWf Build_TypeRedWf Build_TermRedWf
  well_sempty well_scons conv_sempty conv_scons
  tyr_wf_r tyr_wf_red tmr_wf_r tmr_wf_red
  : gen_typing.

(* #[export] Hint Extern 1 =>
  match goal with
    | H : [ _ |- _ ▹h _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ : _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ : _] |- _ => destruct H
    |  H : [ _ |- _ :⤳*: _ ] |- _ => destruct H
    |  H : [ _ |- _ :⤳*: _ : _ ] |- _ => destruct H
  end
  : gen_typing. *)

(** ** Properties of the abstract interface *)

Section GenericTyping.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta} `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Class WfContextProperties :=
  {
    wfc_nil : [|- ε ] ;
    wfc_cons {Γ} {A} : [|- Γ] -> [Γ |- A] -> [|- Γ,,A];
    wfc_wft {Γ A} : [Γ |- A] -> [|- Γ];
    wfc_ty {Γ A t} : [Γ |- t : A] -> [|- Γ];
    wfc_convty {Γ A B} : [Γ |- A ≅ B] -> [|- Γ];
    wfc_convtm {Γ A t u} : [Γ |- t ≅ u : A] -> [|- Γ];
    wfc_redty {Γ A B} : [Γ |- A ⤳* B] -> [|- Γ];
    wfc_redtm {Γ A t u} : [Γ |- t ⤳* u : A] -> [|- Γ];
  }.

  Class WfTypeProperties :=
  {
    wft_wk {Γ Δ A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A] -> [Δ |- A⟨ρ⟩] ;
    wft_U {Γ} :
      [ |- Γ ] ->
      [ Γ |- U ] ;
    wft_prod {Γ} {A B} :
      [ Γ |- A ] ->
      [Γ ,, A |- B ] ->
      [ Γ |- tProd A B ] ;
    wft_sig {Γ} {A B} :
      [ Γ |- A ] ->
      [Γ ,, A |- B ] ->
      [ Γ |- tSig A B ] ;
    wft_Id {Γ} {A x y} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ |- y : A] ->
      [Γ |- tId A x y] ;
    wft_term {Γ} {A} :
      [ Γ |- A : U ] ->
      [ Γ |- A ] ;
  }.

  Class TypingProperties :=
  {
    ty_wk {Γ Δ t A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t : A] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩] ;
    ty_var {Γ} {n decl} :
      [   |- Γ ] ->
      in_ctx Γ n decl ->
      [ Γ |- tRel n : decl ] ;
    ty_prod {Γ} {A B} :
        [ Γ |- A : U] ->
        [Γ ,, A |- B : U ] ->
        [ Γ |- tProd A B : U ] ;
    ty_lam {Γ}  {A B t} :
        [ Γ |- A ] ->
        [ Γ ,, A |- t : B ] ->
        [ Γ |- tLambda A t : tProd A B] ;
    ty_app {Γ}  {f a A B} :
        [ Γ |- f : tProd A B ] ->
        [ Γ |- a : A ] ->
        [ Γ |- tApp f a : B[a ..] ] ;
    ty_nat {Γ} :
        [|-Γ] ->
        [Γ |- tNat : U] ;
    ty_zero {Γ} :
        [|-Γ] ->
        [Γ |- tZero : tNat] ;
    ty_succ {Γ n} :
        [Γ |- n : tNat] ->
        [Γ |- tSucc n : tNat] ;
    ty_natElim {Γ P hz hs n} :
      [Γ ,, tNat |- P ] ->
      [Γ |- hz : P[tZero..]] ->
      [Γ |- hs : elimSuccHypTy P] ->
      [Γ |- n : tNat] ->
      [Γ |- tNatElim P hz hs n : P[n..]] ;
    ty_empty {Γ} :
        [|-Γ] ->
        [Γ |- tEmpty : U] ;
    ty_emptyElim {Γ P e} :
      [Γ ,,  tEmpty |- P ] ->
      [Γ |- e : tEmpty] ->
      [Γ |- tEmptyElim P e : P[e..]] ;
    ty_sig {Γ} {A B} :
        [ Γ |- A : U] ->
        [Γ ,, A |- B : U ] ->
        [ Γ |- tSig A B : U ] ;
    ty_pair {Γ} {A B a b} :
        [ Γ |- A ] ->
        [Γ ,, A |- B ] ->
        [Γ |- a : A] ->
        [Γ |- b : B[a..]] ->
        [Γ |- tPair A B a b : tSig A B] ;
    ty_fst {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tFst p : A] ;
    ty_snd {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tSnd p : B[(tFst p)..]] ;
    ty_Id {Γ} {A x y} :
      [Γ |- A : U] ->
      [Γ |- x : A] ->
      [Γ |- y : A] ->
      [Γ |- tId A x y : U] ;
    ty_refl {Γ A x} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ |- tRefl A x : tId A x x] ;
    ty_IdElim {Γ A x P hr y e} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
      [Γ |- hr : P[tRefl A x .: x..]] ->
      [Γ |- y : A] ->
      [Γ |- e : tId A x y] ->
      [Γ |- tIdElim A x P hr y e : P[e .: y..]];
    ty_exp {Γ t A A'} : [Γ |- t : A'] -> [Γ |- A ⤳* A'] -> [Γ |- t : A] ;
    ty_conv {Γ t A A'} : [Γ |- t : A'] -> [Γ |- A' ≅ A] -> [Γ |- t : A] ;
  }.

  Class ConvTypeProperties :=
  {
    convty_term {Γ A B} : [Γ |- A ≅ B : U] -> [Γ |- A ≅ B] ;
    convty_equiv {Γ} :: PER (conv_type Γ) ;
    convty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ≅ B] -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩] ;
    convty_exp {Γ A A' B B'} :
      [Γ |- A ⤳* A'] -> [Γ |- B ⤳* B'] ->
      [Γ |- A' ≅ B'] -> [Γ |- A ≅ B] ;
    convty_uni {Γ} :
      [|- Γ] -> [Γ |- U ≅ U] ;
    convty_prod {Γ A A' B B'} :
      [Γ |- A] ->
      [Γ |- A ≅ A'] -> [Γ,, A |- B ≅ B'] ->
      [Γ |- tProd A B ≅ tProd A' B'] ;
    convty_sig {Γ A A' B B'} :
      [Γ |- A] ->
      [Γ |- A ≅ A'] -> [Γ,, A |- B ≅ B'] ->
      [Γ |- tSig A B ≅ tSig A' B'] ;
    convty_Id {Γ A A' x x' y y'} :
      (* [Γ |- A] -> ?  *)
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- tId A x y ≅ tId A' x' y' ] ;
  }.

  Class ConvTermProperties :=
  {
    convtm_equiv {Γ A} :: PER (conv_term Γ A) ;
    convtm_conv {Γ t u A A'} : [Γ |- t ≅ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ≅ u : A'] ;
    convtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ≅ u : A] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩] ;
    convtm_exp {Γ A t t' u u'} :
      [Γ |- t ⤳* t' : A] -> [Γ |- u ⤳* u' : A] ->
      [Γ |- A] -> [Γ |- t' : A] -> [Γ |- u' : A] ->
      [Γ |- A ≅ A] -> [Γ |- t' ≅ u' : A] -> [Γ |- t ≅ u : A] ;
    convtm_convneu {Γ n n' A} :
      isPosType A ->
      [Γ |- n ~ n' : A] -> [Γ |- n ≅ n' : A] ;
    convtm_prod {Γ A A' B B'} :
      [Γ |- A : U] ->
      [Γ |- A ≅ A' : U] -> [Γ,, A |- B ≅ B' : U] ->
      [Γ |- tProd A B ≅ tProd A' B' : U] ;
    convtm_sig {Γ A A' B B'} :
      [Γ |- A : U] ->
      [Γ |- A ≅ A' : U] -> [Γ,, A |- B ≅ B' : U] ->
      [Γ |- tSig A B ≅ tSig A' B' : U] ;
    convtm_eta {Γ f g A B} :
      [ Γ |- A ] ->
      [ Γ,, A |- B ] ->
      [ Γ |- f : tProd A B ] ->
      isWfFun Γ A B f ->
      [ Γ |- g : tProd A B ] ->
      isWfFun Γ A B g ->
      [ Γ ,, A |- eta_expand f ≅ eta_expand g : B ] ->
      [ Γ |- f ≅ g : tProd A B ] ;
    convtm_nat {Γ} :
      [|-Γ] -> [Γ |- tNat ≅ tNat : U] ;
    convtm_zero {Γ} :
      [|-Γ] -> [Γ |- tZero ≅ tZero : tNat] ;
    convtm_succ {Γ} {n n'} :
        [Γ |- n ≅ n' : tNat] ->
        [Γ |- tSucc n ≅ tSucc n' : tNat] ;
    convtm_eta_sig {Γ p p' A B} :
      [Γ |- A] ->
      [Γ ,, A |- B] ->
      [Γ |- p : tSig A B] ->
      isWfPair Γ A B p ->
      [Γ |- p' : tSig A B] ->
      isWfPair Γ A B p' ->
      [Γ |- tFst p ≅ tFst p' : A] ->
      [Γ |- tSnd p ≅ tSnd p' : B[(tFst p)..]] ->
      [Γ |- p ≅ p' : tSig A B] ;
    convtm_empty {Γ} :
      [|-Γ] -> [Γ |- tEmpty ≅ tEmpty : U] ;
    convtm_Id {Γ A A' x x' y y'} :
      (* [Γ |- A] -> ?  *)
      [Γ |- A ≅ A' : U] ->
      [Γ |- x ≅ x' : A] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- tId A x y ≅ tId A' x' y' : U ] ;
    convtm_refl {Γ A A' x x'} :
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ |- tRefl A x ≅ tRefl A' x' : tId A x x] ;
  }.

  Class ConvNeuProperties :=
  {
    convneu_equiv {Γ A} :: PER (conv_neu_ty Γ A) ;
    convneu_conv {Γ t u A A'} : [Γ |- t ~ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ~ u : A'] ;
    convneu_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ~ u : A] -> [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ : A⟨ρ⟩] ;
    convneu_whne {Γ A t u} : [Γ |- t ~ u : A] -> whne t;
    convneu_var {Γ n A} :
      [Γ |- tRel n : A] -> [Γ |- tRel n ~ tRel n : A] ;
    convneu_app {Γ f g t u A B} :
      [ Γ |- f ~ g : tProd A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp f t ~ tApp g u : B[t..] ] ;
    convneu_natElim {Γ P P' hz hz' hs hs' n n'} :
        [Γ ,, tNat |- P ≅ P'] ->
        [Γ |- hz ≅ hz' : P[tZero..]] ->
        [Γ |- hs ≅ hs' : elimSuccHypTy P] ->
        [Γ |- n ~ n' : tNat] ->
        [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' : P[n..]] ;
    convneu_emptyElim {Γ P P' e e'} :
        [Γ ,, tEmpty |- P ≅ P'] ->
        [Γ |- e ~ e' : tEmpty] ->
        [Γ |- tEmptyElim P e ~ tEmptyElim P' e' : P[e..]] ;
    convneu_fst {Γ A B p p'} :
      [Γ |- p ~ p' : tSig A B] ->
      [Γ |- tFst p ~ tFst p' : A] ;
    convneu_snd {Γ A B p p'} :
      [Γ |- p ~ p' : tSig A B] ->
      [Γ |- tSnd p ~ tSnd p' : B[(tFst p)..]] ;
    convneu_IdElim {Γ A A' x x' P P' hr hr' y y' e e'} :
      (* Parameters well formed: required by declarative instance *)
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'] ->
      [Γ |- hr ≅ hr' : P[tRefl A x .: x..]] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- e ~ e' : tId A x y] ->
      [Γ |- tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e' : P[e .: y..]];
  }.

  Class RedTypeProperties :=
  {
    redty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ⤳* B] -> [Δ |- A⟨ρ⟩ ⤳* B⟨ρ⟩] ;
    redty_sound {Γ A B} : [Γ |- A ⤳* B] -> [A ⤳* B] ;
    redty_ty_src {Γ A B} : [Γ |- A ⤳* B] -> [Γ |- A] ;
    redty_term {Γ A B} :
      [ Γ |- A ⤳* B : U] -> [Γ |- A ⤳* B ] ;
    redty_refl {Γ A} :
      [ Γ |- A] ->
      [Γ |- A ⤳* A] ;
    redty_trans {Γ} ::
      Transitive (red_ty Γ) ;
  }.

  Class RedTermProperties :=
  {
    redtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ⤳* u : A] -> [Δ |- t⟨ρ⟩ ⤳* u⟨ρ⟩ : A⟨ρ⟩] ;
    redtm_sound {Γ A t u} : [Γ |- t ⤳* u : A] -> [t ⤳* u] ;
    redtm_ty_src {Γ A t u} : [Γ |- t ⤳* u : A] -> [Γ |- t : A] ;
    redtm_beta {Γ A B t u} :
      [ Γ |- A ] ->
      [ Γ ,, A |- t : B ] ->
      [ Γ |- u : A ] ->
      [ Γ |- tApp (tLambda A t) u ⤳* t[u..] : B[u..] ] ;
    redtm_natElimZero {Γ P hz hs} :
        [Γ ,, tNat |- P ] ->
        [Γ |- hz : P[tZero..]] ->
        [Γ |- hs : elimSuccHypTy P] ->
        [Γ |- tNatElim P hz hs tZero ⤳* hz : P[tZero..]] ;
    redtm_natElimSucc {Γ P hz hs n} :
        [Γ ,, tNat |- P ] ->
        [Γ |- hz : P[tZero..]] ->
        [Γ |- hs : elimSuccHypTy P] ->
        [Γ |- n : tNat] ->
        [Γ |- tNatElim P hz hs (tSucc n) ⤳* tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]] ;
    redtm_app {Γ A B f f' t} :
      [ Γ |- f ⤳* f' : tProd A B ] ->
      [ Γ |- t : A ] ->
      [ Γ |- tApp f t ⤳* tApp f' t : B[t..] ];
    redtm_natelim {Γ P hz hs n n'} :
      [ Γ,, tNat |- P ] ->
      [ Γ |- hz : P[tZero..] ] ->
      [ Γ |- hs : elimSuccHypTy P ] ->
      [ Γ |- n ⤳* n' : tNat ] ->
      [ Γ |- tNatElim P hz hs n ⤳* tNatElim P hz hs n' : P[n..] ];
    redtm_emptyelim {Γ P n n'} :
      [ Γ,, tEmpty |- P ] ->
      [ Γ |- n ⤳* n' : tEmpty ] ->
      [ Γ |- tEmptyElim P n ⤳* tEmptyElim P n' : P[n..] ];
    redtm_fst_beta {Γ A B a b} :
      [Γ |- A] ->
      [Γ ,, A |- B] ->
      [Γ |- a : A] ->
      [Γ |- b : B[a..]] ->
      [Γ |- tFst (tPair A B a b) ⤳* a : A] ;
    redtm_fst {Γ A B p p'} :
      [Γ |- p ⤳* p' : tSig A B] ->
      [Γ |- tFst p ⤳* tFst p' : A] ;
    redtm_snd_beta {Γ A B a b} :
      [Γ |- A] ->
      [Γ ,, A |- B] ->
      [Γ |- a : A] ->
      [Γ |- b : B[a..]] ->
      [Γ |- tSnd (tPair A B a b) ⤳* b : B[(tFst (tPair A B a b))..]] ;
    redtm_snd {Γ A B p p'} :
      [Γ |- p ⤳* p' : tSig A B] ->
      [Γ |- tSnd p ⤳* tSnd p' : B[(tFst p)..]] ;
    redtm_idElimRefl {Γ A x P hr y A' z} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
      [Γ |- hr : P[tRefl A x .: x..]] ->
      [Γ |- y : A] ->
      [Γ |- A'] ->
      [Γ |- z : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ y : A] ->
      [Γ |- x ≅ z : A] ->
      [Γ |- tIdElim A x P hr y (tRefl A' z) ⤳* hr : P[tRefl A' z .: y..]];
    redtm_idElim {Γ A x P hr y e e'} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
      [Γ |- hr : P[tRefl A x .: x..]] ->
      [Γ |- y : A] ->
      [Γ |- e ⤳* e' : tId A x y] ->
      [Γ |- tIdElim A x P hr y e ⤳* tIdElim A x P hr y e' : P[e .: y..]];
    redtm_conv {Γ t u A A'} :
      [Γ |- t ⤳* u : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- t ⤳* u : A'] ;
    redtm_refl {Γ A t } :
      [ Γ |- t : A] ->
      [Γ |- t ⤳* t : A] ;
    redtm_trans {Γ A} ::
      Transitive (red_tm Γ A) ;
  }.

End GenericTyping.

(** This class bundles together the various predicate and relations, and their
properties all together. Most of the logical relation is constructed over an
abstract instance of this class. *)

Class GenericTypingProperties `(ta : tag)
  `(WfContext ta) `(WfType ta) `(Typing ta)
  `(ConvType ta) `(ConvTerm ta) `(ConvNeuConv ta)
  `(RedType ta) `(RedTerm ta)
  `(RedType ta) `(RedTerm ta)
:=
{
  wfc_prop :: WfContextProperties ;
  wfty_prop :: WfTypeProperties ;
  typ_prop :: TypingProperties ;
  convty_prop :: ConvTypeProperties ;
  convtm_prop :: ConvTermProperties ;
  convne_prop :: ConvNeuProperties ;
  redty_prop :: RedTypeProperties ;
  redtm_prop :: RedTermProperties ;
}.

(** Hints for gen_typing *)
(* Priority 0 *)
#[export] Hint Resolve wfc_wft wfc_ty wfc_convty wfc_convtm wfc_redty wfc_redtm : gen_typing.
(* Priority 2 *)
#[export] Hint Resolve wfc_nil wfc_cons | 2 : gen_typing.
#[export] Hint Resolve wft_wk wft_U wft_prod wft_sig wft_Id | 2 : gen_typing.
#[export] Hint Resolve ty_wk ty_var ty_prod ty_lam ty_app ty_nat ty_empty ty_zero ty_succ ty_natElim ty_emptyElim ty_sig ty_pair ty_fst ty_snd ty_Id ty_refl ty_IdElim| 2 : gen_typing.
#[export] Hint Resolve convty_wk convty_uni convty_prod convty_sig convty_Id | 2 : gen_typing.
#[export] Hint Resolve convtm_wk convtm_prod convtm_sig convtm_eta convtm_nat convtm_empty convtm_zero convtm_succ convtm_eta_sig convtm_Id convtm_refl | 2 : gen_typing.
#[export] Hint Resolve convneu_wk convneu_var convneu_app convneu_natElim convneu_emptyElim convneu_fst convneu_snd convneu_IdElim | 2 : gen_typing.
#[export] Hint Resolve redty_ty_src redtm_ty_src | 2 : gen_typing.
(* Priority 4 *)
#[export] Hint Resolve wft_term convty_term convtm_convneu | 4 : gen_typing.
(* Priority 6 *)
#[export] Hint Resolve ty_conv ty_exp convty_exp convtm_exp convtm_conv convneu_conv redtm_conv | 6 : gen_typing.

(** A tactic to transform applications of (untyped) renamings back to (well-typed) weakenings,
so that we can use stability by weakening. *)

Ltac renToWk0 judg :=
  lazymatch judg with
  (** Type judgement, weakening *)
  | [?X ,, ?Y |- ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
  (** Type judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (* Type judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on

  (** Type conversion judgement, weakening *)
  | [?X ,, ?Y |- ?T⟨↑⟩ ≅ _ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
  | [?X ,, ?Y |- _ ≅ ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
  (** Type conversion judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ≅ _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ≅ _ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (* Type conversion judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ≅ _ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- _ ≅ ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on

  (** Term judgement, weakening *)
  | [?X ,, ?Y |- _ : ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- ?t⟨↑⟩ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
  (** Term judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ : _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ : ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (** Term judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ : ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on

  (** Term conversion judgement, weakening *)
  | [?X ,, ?Y |- _ ≅ _ : ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- ?t⟨↑⟩ ≅ _ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- _ ≅ ?t⟨↑⟩ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
  (** Term conversion judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ≅ _ : _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ _ : ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ ≅ _ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ ?t⟨upRen_term_term ↑⟩ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (** Term conversion judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ ≅ _ : ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ ≅ _ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ ≅ ?t⟨upRen_term_term _⟩ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on


  end.

Ltac renToWk :=
  fold ren_term;
  repeat change (ren_term ?x ?y) with y⟨x⟩;
  repeat change S with ↑;
  repeat lazymatch goal with
  | [ _ : _ |- ?G] => renToWk0 G
  end.


(** ** Easy consequences of the previous properties. *)

Section GenericConsequences.
  Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!RedTerm ta}
  `{!WfContextProperties} `{!WfTypeProperties}
  `{!TypingProperties} `{!ConvTypeProperties}
  `{!ConvTermProperties} `{!ConvNeuProperties}
  `{!RedTypeProperties} `{!RedTermProperties}.

  (** *** Meta-conversion *)
  (** Similar to conversion, but using a meta-level equality rather
  than a conversion *)

  Lemma typing_meta_conv (Γ : context) (t A A' : term) :
    [Γ |- t : A] ->
    A' = A ->
    [Γ |- t : A'].
  Proof.
    now intros ? ->.
  Qed.

  Lemma convtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ≅ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ≅ u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma convne_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ~ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ~ u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ⤳* u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ⤳* u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtmwf_meta_conv_ty (Γ : context) (t u A A' : term) :
    [Γ |- t :⤳*: u : A] ->
    A' = A ->
    [Γ |- t :⤳*: u : A'].
  Proof.
    now intros ? ->.
  Qed.

  (** *** Properties of well-typed reduction *)

  Lemma tyr_wf_l {Γ A B} : [Γ |- A :⤳*: B] -> [Γ |- A].
  Proof.
    intros []; now eapply redty_ty_src.
  Qed.

  Lemma tmr_wf_l {Γ t u A} : [Γ |- t :⤳*: u : A] -> [Γ |- t : A].
  Proof.
    intros []; now eapply redtm_ty_src.
  Qed.

  #[local] Hint Resolve tyr_wf_l tmr_wf_l : gen_typing.
  #[local] Hint Resolve redty_wk redty_term redty_refl redtm_wk redtm_app redtm_refl | 2 : gen_typing.
  #[local] Hint Resolve redtm_beta redtm_natElimZero redtm_natElimSucc | 2 : gen_typing.
  #[local] Hint Resolve  redtm_conv | 6 : gen_typing.

  Lemma redty_red {Γ A B} :
      [Γ |- A ⤳* B] -> [ A ⤳* B ].
  Proof.
    intros ?%redty_sound.
    assumption.
  Qed.

  Lemma redtm_red {Γ t u A} :
      [Γ |- t ⤳* u : A] ->
      [t ⤳* u].
  Proof.
    intros ?%redtm_sound.
    assumption.
  Qed.

  #[local] Hint Resolve redty_red  redtm_red | 2 : gen_typing.

  Lemma redtywf_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A :⤳*: B] -> [Δ |- A⟨ρ⟩ :⤳*: B⟨ρ⟩].
  Proof.
    intros ? []; constructor; gen_typing.
  Qed.

  Lemma redtywf_red {Γ A B} : [Γ |- A :⤳*: B] -> [A ⤳* B].
  Proof.
    intros []; now eapply redty_red.
  Qed.

  Lemma redtywf_term {Γ A B} :
      [ Γ |- A :⤳*: B : U] -> [Γ |- A :⤳*: B ].
  Proof.
    intros []; constructor; gen_typing.
  Qed.

  Lemma redtywf_refl {Γ A} : [Γ |- A] -> [Γ |- A :⤳*: A].
  Proof.  constructor; gen_typing.  Qed.

  #[global]
  Instance redtywf_trans {Γ} : Transitive (TypeRedWf Γ). (* fun A B => [Γ |- A :⤳*: B] *)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  (** Almost all of the RedTermProperties can be derived
    for the well-formed reduction [Γ |- t :⤳*: u : A]
    but for application (which requires stability of typing under substitution). *)

  Definition redtmwf_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t :⤳*: u : A] -> [Δ |- t⟨ρ⟩ :⤳*: u⟨ρ⟩ : A⟨ρ⟩].
  Proof.  intros ? []; constructor; gen_typing. Qed.

  Definition redtmwf_red {Γ t u A} :
    [Γ |- t :⤳*: u : A] -> [t ⤳* u].
  Proof. intros []; now eapply redtm_red. Qed.

  Definition redtmwf_conv {Γ} {t u A B} :
      [Γ |- t :⤳*: u : A] ->
      [Γ |- A ≅ B ] ->
      [Γ |- t :⤳*: u : B].
  Proof.
    intros [wfl red] ?.
    constructor.
    all: gen_typing.
  Qed.

  Lemma redtmwf_refl {Γ a A} : [Γ |- a : A] -> [Γ |- a :⤳*: a : A].
  Proof.
    constructor; tea.
    now apply redtm_refl.
  Qed.

  #[global]
  Instance redtmwf_trans {Γ A} : Transitive (TermRedWf Γ A). (*fun t u => [Γ |- t :⤳*: u : A]*)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  Lemma redtmwf_app {Γ A B f f' t} :
    [ Γ |- f :⤳*: f' : tProd A B ] ->
    [ Γ |- t : A ] ->
    [ Γ |- tApp f t :⤳*: tApp f' t : B[t..] ].
  Proof.
    intros [] ?; constructor; gen_typing.
  Qed.

  Lemma redtmwf_appwk {Γ Δ A B B' t u a} (ρ : Δ ≤ Γ) :
    [Γ |- t :⤳*: u : tProd A B] ->
    [Δ |- a : A⟨ρ⟩] ->
    B' = B⟨upRen_term_term ρ⟩[a..] ->
    [Δ |- tApp t⟨ρ⟩ a :⤳*: tApp u⟨ρ⟩ a : B'].
  Proof.
    intros redtu **.
    eapply redtmwf_meta_conv_ty; tea.
    eapply redtmwf_app; tea.
    unshelve eapply (redtmwf_wk ρ _ redtu).
    gen_typing.
  Qed.

  Lemma redtmwf_natElimZero {Γ P hz hs} :
    [Γ ,, tNat |- P ] ->
    [Γ |- hz : P[tZero..]] ->
    [Γ |- hs : elimSuccHypTy P] ->
    [Γ |- tNatElim P hz hs tZero :⤳*: hz : P[tZero..]].
  Proof.
    intros ???; constructor; tea; gen_typing.
  Qed.

  (** *** Properties of well-typing *)

  Definition well_typed_well_formed Γ t : well_typed Γ t -> well_formed Γ t :=
  fun w =>
  {|
    well_formed_class := isterm (well_typed_type Γ t w) ;
    well_formed_typed := well_typed_typed Γ t w
  |}.

  #[warning="-uniform-inheritance"]Coercion well_typed_well_formed : well_typed >-> well_formed.

  Definition well_formed_well_typed Γ t (w : well_formed Γ t) : (well_typed Γ t + [Γ |- t]) :=
  (match (well_formed_class _ _ w) as c return
      (match c with
      | istype => [Γ |-[ ta ] t]
      | isterm A => [Γ |-[ ta ] t : A]
      end -> well_typed Γ t + [Γ |-[ ta ] t])
  with
  | istype => inr
  | isterm A => fun w' => inl {| well_typed_type := A ; well_typed_typed := w' |}
    end) (well_formed_typed _ _ w).

  (** *** Derived typing, reduction and conversion judgements *)

  Lemma ty_var0 {Γ A} :
    [Γ |- A] ->
    [Γ ,, A |- tRel 0 : A⟨↑⟩].
  Proof.
    intros; refine (ty_var _ (in_here _ _)); gen_typing.
  Qed.

  Lemma wft_simple_arr {Γ A B} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- arr A B].
  Proof.
    intros. eapply wft_prod; renToWk; tea.
    eapply wft_wk; gen_typing.
  Qed.

  Lemma convty_simple_arr {Γ A A' B B'} :
    [Γ |- A] ->
    [Γ |- A ≅ A'] ->
    [Γ |- B ≅ B'] ->
    [Γ |- arr A B ≅ arr A' B'].
  Proof.
    intros; eapply convty_prod; tea.
    renToWk; eapply convty_wk; gen_typing.
  Qed.

  Lemma ty_simple_app {Γ A B f a} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- f : arr A B] ->
    [Γ |- a : A] ->
    [Γ |- tApp f a : B].
  Proof.
    intros. replace B with B⟨shift⟩[a..] by now asimpl.
    eapply ty_app; tea.
  Qed.

  Lemma convneu_simple_app {Γ f g t u A B} :
      [ Γ |- f ~ g : arr A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp f t ~ tApp g u : B ].
  Proof.
    intros.
    replace B with B⟨↑⟩[t..] by now asimpl.
    now eapply convneu_app.
  Qed.

  #[local]
  Hint Resolve ty_simple_app : gen_typing.

  Lemma ty_id {Γ A B C} :
    [Γ |- A] ->
    [Γ |- A ≅ B] ->
    [Γ |- A ≅ C] ->
    [Γ |- idterm A : arr B C].
  Proof.
    intros.
    eapply ty_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply ty_lam; tea.
    now eapply ty_var0.
  Qed.

  Lemma ty_id' {Γ A} :
    [Γ |- A] ->
    [Γ |- idterm A : arr A A].
  Proof.
    intros.
    (* eapply ty_conv. *)
    (* 2: eapply convty_simple_arr; cycle 1; tea. *)
    eapply ty_lam; tea.
    now eapply ty_var0.
  Qed.

  Lemma redtm_id_beta {Γ a A} :
    [Γ |- A] ->
    [Γ |- A ≅ A] ->
    [Γ |- a : A] ->
    [Γ |- tApp (idterm A) a ⤳* a : A].
  Proof.
    intros.
    eapply redtm_meta_conv.
    1: eapply redtm_beta; tea.
    + now eapply ty_var0.
    + cbn; now bsimpl.
    + now asimpl.
  Qed.

  Lemma convtm_id {Γ A A' B C} :
    [|- Γ] ->
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ |- A ≅ A'] ->
    [Γ |- A ≅ B] ->
    [Γ |- A ≅ C] ->
    [Γ,, A |- tRel 0 ≅ tRel 0 : A⟨↑⟩] ->
    [Γ |- idterm A ≅ idterm A' : arr B C].
  Proof.
    intros.
    assert [Γ |- A ≅ A] by (etransitivity; tea; now symmetry).
    eapply convtm_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply convtm_eta; tea.
    { renToWk; apply wft_wk; [apply wfc_cons|]; tea. }
    2:{ constructor; first [now eapply lrefl|now apply ty_var0|tea]. }
    3:{ constructor; first [now eapply lrefl|now apply ty_var0|tea].
        eapply ty_conv; [now apply ty_var0|].
        do 2 rewrite <- (@wk1_ren_on Γ A'); apply convty_wk; [|now symmetry].
        now apply wfc_cons. }
    1,2: eapply ty_id; tea; now symmetry.
    assert [|- Γ,, A] by gen_typing.
    assert [Γ,, A |-[ ta ] A⟨@wk1 Γ A⟩] by now eapply wft_wk.
    eapply convtm_exp.
    - cbn. eapply redtm_id_beta.
      3: now eapply ty_var0.
      1,2: renToWk; tea; now eapply convty_wk.
    - cbn.
      assert [Γ,, A |- A'⟨↑⟩ ≅ A⟨↑⟩]
        by (renToWk; symmetry; now eapply convty_wk).
      eapply redtm_conv; tea.
      eapply redtm_id_beta.
      1: renToWk; now eapply wft_wk.
      1: now eapply lrefl.
      eapply ty_conv. 2: now symmetry.
      now eapply ty_var0.
    - renToWk; tea; now eapply convty_wk.
    - now eapply ty_var0.
    - now eapply ty_var0.
    - renToWk; tea; now eapply convty_wk.
    - eassumption.
  Qed.

  Lemma ty_comp {Γ A B C f g} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- g : arr A B] ->
    [Γ |- f : arr B C] ->
    [Γ |- comp A f g : arr A C].
  Proof.
    intros tyA tyB **.
    eapply ty_lam; tea.
    assert [|- Γ,, A] by gen_typing.
    pose (r := @wk1 Γ A).
    eapply ty_simple_app; renToWk.
    - unshelve eapply (wft_wk _ _ tyB) ; tea.
    - now eapply wft_wk.
    - replace (arr _ _) with (arr B C)⟨r⟩ by (unfold r; now bsimpl).
      now eapply ty_wk.
    - eapply ty_simple_app; renToWk.
      + unshelve eapply (wft_wk _ _ tyA) ; tea.
      + now eapply wft_wk.
      + replace (arr _ _) with (arr A B)⟨r⟩ by (unfold r; now bsimpl).
        now eapply ty_wk.
      + unfold r; rewrite wk1_ren_on; now refine (ty_var _ (in_here _ _)).
  Qed.

  Lemma wft_wk1 {Γ A B} : [Γ |- A] -> [Γ |- B] -> [Γ ,, A |- B⟨↑⟩].
  Proof.
    intros; renToWk; eapply wft_wk; gen_typing.
  Qed.

  Lemma redtm_comp_beta {Γ A B C f g a} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- f : arr A B] ->
    [Γ |- g : arr B C] ->
    [Γ |- a : A] ->
    [Γ |- tApp (comp A g f) a ⤳* tApp g (tApp f a) : C].
  Proof.
    intros hA hB hC hf hg ha.
    eapply redtm_meta_conv.
    1: eapply redtm_beta; tea.
    + eapply ty_simple_app.
      4: eapply ty_simple_app.
      1,2,4,5: eapply wft_wk1; [gen_typing|].
      1: exact hB. 1: exact hC. 1: exact hA. 1: tea.
      1,2: rewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      now eapply ty_var0.
    + cbn; now bsimpl.
    + now asimpl.
  Qed.

  Lemma convtm_comp_app {Γ A B C f f' g g'} :
    [|- Γ] ->
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- C ≅ C] ->
    [Γ |- f : arr A B] ->
    [Γ |- f' : arr A B] ->
    [Γ |- g : arr B C] ->
    [Γ |- g' : arr B C] ->
    [Γ,, A |- tApp g⟨↑⟩ (tApp f⟨↑⟩ (tRel 0)) ≅ tApp g'⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : C⟨↑⟩] ->
    [Γ ,, A |- tApp (comp A g f)⟨↑⟩ (tRel 0) ≅ tApp (comp A g' f')⟨↑⟩ (tRel 0) : C⟨↑⟩].
  Proof.
    intros.
    eapply convtm_exp.
    - cbn.
      do 2 rewrite <- shift_upRen.
      eapply redtm_comp_beta.
      5: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      4: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      1-3: now eapply wft_wk1.
      now eapply ty_var0.
    - cbn. do 2 rewrite <- shift_upRen.
      eapply redtm_comp_beta.
      5: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      4: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      1-3: now eapply wft_wk1.
      now eapply ty_var0.
    - now eapply wft_wk1.
    - eapply @ty_simple_app with (A := B⟨↑⟩).
      + now eapply wft_wk1.
      + now eapply wft_wk1.
      + erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      + eapply @ty_simple_app with (A := A⟨↑⟩); [now eapply wft_wk1|now eapply wft_wk1| |now apply ty_var0].
        erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
    - eapply @ty_simple_app with (A := B⟨↑⟩).
      + now eapply wft_wk1.
      + now eapply wft_wk1.
      + erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      + eapply @ty_simple_app with (A := A⟨↑⟩); [now eapply wft_wk1|now eapply wft_wk1| |now apply ty_var0].
        erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
    - renToWk; apply convty_wk; gen_typing.
    - assumption.
  Qed.


  Lemma convtm_comp {Γ A B C f f' g g'} :
    [|- Γ] ->
    [Γ |- A] ->
    [Γ |- A ≅ A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- C ≅ C] ->
    [Γ |- f : arr A B] ->
    [Γ |- f' : arr A B] ->
    [Γ |- g : arr B C] ->
    [Γ |- g' : arr B C] ->
    [Γ,, A |-[ ta ] tApp g⟨↑⟩ (tApp f⟨↑⟩ (tRel 0)) ≅ tApp g'⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : C⟨↑⟩] ->
    [Γ |- comp A g f ≅ comp A g' f' : arr A C].
  Proof.
    intros.
    assert (Hup : forall X Y h, [Γ |- h : arr X Y] -> [Γ,, A |- h⟨↑⟩ : arr X⟨↑⟩ Y⟨↑⟩]).
    { intros; rewrite <- arr_ren1, <- !(wk1_ren_on Γ A).
      apply (ty_wk (@wk1 Γ A)); [|now rewrite wk1_ren_on].
      now apply wfc_cons. }
    eapply convtm_eta; tea.
    { renToWk; apply wft_wk; [apply wfc_cons|]; tea. }
    2:{ assert [Γ,, A |-[ ta ] tApp g⟨↑⟩ (tApp f⟨↑⟩ (tRel 0)) : C⟨↑⟩].
        { eapply (ty_simple_app (A := B⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          eapply (ty_simple_app (A := A⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          now apply ty_var0. }
        constructor; tea. }
    3:{ assert [Γ,, A |-[ ta ] tApp g'⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : C⟨↑⟩].
        { eapply (ty_simple_app (A := B⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          eapply (ty_simple_app (A := A⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          now apply ty_var0. }
        constructor; tea. }
    1,2: eapply ty_comp.
    4,5,9,10: tea.
    all: tea.
    eapply convtm_comp_app; cycle 4; tea.
  Qed.

  Lemma typing_eta (Γ : context) A B f :
    [Γ |- A] ->
    [Γ,, A |- B] ->
    [Γ |- f : tProd A B] ->
    [Γ,, A |- eta_expand f : B].
  Proof.
    intros ? ? Hf.
    eapply typing_meta_conv.
    eapply ty_app; tea.
    2: refine (ty_var _ (in_here _ _)); gen_typing.
    1: eapply typing_meta_conv; [renToWk; eapply ty_wk; tea;gen_typing|now rewrite wk1_ren_on].
    fold ren_term. now bsimpl.
  Qed.

  Lemma lambda_cong {Γ A A' B B' t t'} :
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ,, A |- B] ->
    [Γ,, A |- t : B] ->
    [Γ,, A |- t' : B] ->
    [Γ,, A' |- t' : B'] ->
    [Γ |- A ≅ A'] ->
    [Γ,, A |- B ≅ B'] ->
    [Γ,, A' |- B ≅ B'] ->
    [Γ,, A |- t ≅ t' : B] ->
    [Γ |- tLambda A t ≅ tLambda A' t' : tProd A B].
  Proof.
    intros.
    assert [|- Γ,, A] by gen_typing.
    apply convtm_eta ; tea.
    - gen_typing.
    - constructor; first[now eapply lrefl|tea].
    - eapply ty_conv.
      1: eapply ty_lam ; tea.
      symmetry.
      now eapply convty_prod.
    - constructor; tea.
      now eapply ty_conv.
    - eapply @convtm_exp with (t' := t) (u' := t'); tea.
      3: now eapply lrefl.
      2: eapply redtm_conv ; cbn ; [eapply redtm_meta_conv |..] ; [eapply redtm_beta |..].
      1: eapply redtm_meta_conv ; cbn ; [eapply redtm_beta |..].
      + renToWk.
        now eapply wft_wk.
      + renToWk.
        eapply ty_wk ; tea.
        eapply wfc_cons ; tea.
        now eapply wft_wk.
      + eapply ty_var ; tea.
        now econstructor.
      + now bsimpl.
      + now bsimpl.
      + renToWk.
        now eapply wft_wk.
      + renToWk.
        eapply ty_wk ; tea.
        eapply wfc_cons ; tea.
        now eapply wft_wk.
      + eapply ty_conv.
        1: eapply ty_var0 ; tea.
        renToWk.
        now eapply convty_wk.
      + shelve.
      + now bsimpl.
      + symmetry. eassumption.
      Unshelve.
      now bsimpl.
  Qed.


  (** *** Lifting determinism properties from untyped reduction to typed reduction. *)

  Lemma redtm_whnf {Γ t u A} : [Γ |- t ⤳* u : A] -> whnf t -> t = u.
  Proof.
    intros.
    apply red_whnf; [|assumption].
    now eapply redtm_sound.
  Qed.

  Lemma redtmwf_whnf {Γ t u A} : [Γ |- t :⤳*: u : A] -> whnf t -> t = u.
  Proof.
    intros []; now eapply redtm_whnf.
  Qed.

  Lemma redtmwf_whne {Γ t u A} : [Γ |- t :⤳*: u : A] -> whne t -> t = u.
  Proof.
    intros ? ?%whnf_whne; now eapply redtmwf_whnf.
  Qed.

  Lemma redty_whnf {Γ A B} : [Γ |- A ⤳* B] -> whnf A -> A = B.
  Proof.
    intros.
    apply red_whnf; [|eassumption].
    now eapply redty_sound.
  Qed.

  Lemma redtywf_whnf {Γ A B} : [Γ |- A :⤳*: B] -> whnf A -> A = B.
  Proof.
    intros []; now eapply redty_whnf.
  Qed.

  Lemma redtywf_whne {Γ A B} : [Γ |- A :⤳*: B] -> whne A -> A = B.
  Proof.
    intros ? ?%whnf_whne; now eapply redtywf_whnf.
  Qed.

  Lemma redtmwf_det {Γ t u u' A A'} :
    whnf u -> whnf u' ->
    [Γ |- t :⤳*: u : A] -> [Γ |- t :⤳*: u' : A'] ->
    u = u'.
  Proof.
    intros ?? [] [].
    eapply whred_det; tea.
    all: now eapply redtm_sound.
  Qed.

  Lemma redtywf_det {Γ A B B'} :
    whnf B -> whnf B' ->
    [Γ |- A :⤳*: B] -> [Γ |- A :⤳*: B'] ->
    B = B'.
  Proof.
    intros ?? [] [].
    eapply whred_det; tea.
    all: now eapply redty_sound.
  Qed.

  (* Unused, consider removing*)
  Lemma whredtm_det Γ t u u' A A' :
    [Γ |- t ↘ u : A] -> [Γ |- t ↘ u' : A'] ->
    u = u'.
  Proof.
    intros [] [].
    eapply whred_det; tea.
    all: now eapply redtm_sound.
  Qed.

  (* Unused, consider removing*)
  Lemma whredty_det Γ A B B' :
    [Γ |- A ↘ B] -> [Γ |- A ↘ B'] ->
    B = B'.
  Proof.
    intros [] [].
    eapply whred_det; tea.
    all: now eapply redty_sound.
  Qed.


  Lemma isWfFun_isFun : forall Γ A B t, isWfFun Γ A B t -> isFun t.
  Proof.
  intros * []; constructor; now eapply convneu_whne.
  Qed.

  Lemma isWfPair_isPair : forall Γ A B t, isWfPair Γ A B t -> isPair t.
  Proof.
  intros * []; constructor; now eapply convneu_whne.
  Qed.

End GenericConsequences.

#[export] Hint Resolve tyr_wf_l tmr_wf_l well_typed_well_formed : gen_typing.
#[export] Hint Resolve redtywf_wk redtywf_term redtywf_red redtywf_refl redtmwf_wk redtmwf_app redtmwf_refl redtm_beta redtmwf_red redtmwf_natElimZero | 2 : gen_typing.
#[export] Hint Resolve  redtmwf_conv | 6 : gen_typing.
