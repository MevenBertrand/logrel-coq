(** * LogRel.PropertiesDefinition: the high-level, abstract properties of conversion and typing, that we obtain as consequences of the logical relation. *)
From Coq Require Import CRelationClasses ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping.

Section Properties.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta} `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.


  (** Typing is stable by substitution *) 
  Class TypingSubst :=
  {
    ty_subst {Γ Δ σ A} :
      [|- Δ] -> [Δ |-s σ : Γ] ->
      [Γ |- A] -> [Δ |- A[σ]];
    tm_subst {Γ Δ σ A t} :
      [|- Δ] -> [Δ |-s σ : Γ] ->
      [Γ |- t : A] -> [Δ |- t[σ] : A[σ]];
    ty_conv_subst {Γ Δ σ σ' A B} :
      [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] ->
      [Γ |- A ≅ B] -> [Δ |- A[σ] ≅ B[σ']];
    tm_conv_subst {Γ Δ σ σ' A t u} :
      [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] ->
      [Γ |- t ≅ u : A] -> [Δ |- t[σ] ≅ u[σ'] : A[σ]] ;
  }.

  Class Strengthening :=
  {
  ty_str {Γ Δ A} (ρ : Γ ≤ Δ) :
    [|- Δ] ->
    [Γ |- A⟨ρ⟩] -> [Δ |- A];
  tm_str {Γ Δ A t} (ρ : Γ ≤ Δ) :
    [|- Δ] ->
    [Γ |- t⟨ρ⟩ : A⟨ρ⟩] -> [Δ |- t : A];
  ty_conv_str {Γ Δ A B} (ρ : Γ ≤ Δ) :
    [|- Δ] ->
    [Γ |- A⟨ρ⟩ ≅ B⟨ρ⟩] -> [Δ |- A ≅ B];
  tm_conv_str {Γ Δ A t u} (ρ : Γ ≤ Δ) :
    [|- Δ] ->
    [Γ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩] -> [Δ |- t ≅ u : A] ;
  }.

  (** Reduction is complete for type conversion: if a
    type is convertible to a whnf, then it also reduces
    to a whnf. *)
  Class TypeReductionComplete :=
  {
    red_ty_complete_l (Γ : context) (T T' : term) :
      isType T ->
      [Γ |- T ≅ T'] ->
      ∑ T'', [Γ |- T' ⤳* T''] × isType T'' ;

    red_ty_complete_r (Γ : context) (T T' : term) :
      isType T' ->
      [Γ |- T ≅ T'] ->
      ∑ T'', [Γ |- T ⤳* T''] × isType T'' ;
  }.

  Definition type_hd_view (Γ : context) {T T' : term}
    (nfT : isType T) (nfT' : isType T') : Type :=
    
    match nfT, nfT' with
      | @UnivType s, @UnivType s' => s = s'
      | @ProdType A B, @ProdType A' B' => [Γ |- A' ≅ A] × [Γ,, A' |- B ≅ B']
      | NatType, NatType => True
      | EmptyType, EmptyType => True
      | NeType _, NeType _ => [Γ |- T ≅ T' : U]
      | @SigType A B, @SigType A' B' => [Γ |- A ≅ A'] × [Γ,, A |- B ≅ B']
      | @IdType A x y, @IdType A' x' y' => [× [Γ |- A ≅ A'], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]]
      | _, _ => False
    end.

  (** Type constructors injectivity/no-confusion: two
  convertible whnf types must be the same head constructor,
  with convertible arguments. *)

  Class TypeConstructorsInj :=
  {
   ty_conv_inj (Γ : context) (T T' : term)
    (nfT : isType T) (nfT' : isType T') :
    [Γ |- T ≅ T'] ->
    type_hd_view Γ nfT nfT'
  }.

  (** Similar notions for term constructors at positive types. *)

  Definition univ_hd_view (Γ : context) {T T' : term} (nfT : isType T) (nfT' : isType T') : Type :=
    match nfT, nfT' with
      | @UnivType s, @UnivType s' => False
      | @ProdType A B, @ProdType A' B' => [Γ |- A' ≅ A : U] × [Γ,, A' |- B ≅ B' : U]
      | NatType, NatType => True
      | EmptyType, EmptyType => True
      | NeType _, NeType _ => [Γ |- T ≅ T' : U]
      | @SigType A B, @SigType A' B' => [Γ |- A ≅ A' : U] × [Γ,, A |- B ≅ B' : U]
      | @IdType A x y, @IdType A' x' y' => [× [Γ |- A ≅ A' : U], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]]
      | _, _ => False
    end.

  Definition nat_hd_view (Γ : context) {t t' : term} (nft : isNat t) (nft' : isNat t') : Type :=
  match nft, nft' with
    | ZeroNat, ZeroNat => True
    | @SuccNat u, @SuccNat u' => [Γ |- u ≅ u' : tNat]
    | NeNat _, NeNat _ => [Γ |- t ≅ t' : tNat ]
    | _, _ => False
  end.

  Definition id_hd_view (Γ : context) (A x x' : term) {t t' : term} (nft : isId t) (nft' : isId t') : Type :=
    match nft, nft' with
      | @ReflId A a, @ReflId A' a' => [Γ |- A ≅ A'] × [Γ |- a ≅ a' : A]
      | NeId _, NeId _ => [Γ |- t ≅ t' : tId A x x']
      | _, _ => False
    end.

  Class TermConstructorsInj :=
  {
    univ_conv_inj (Γ : context) (T T' : term)
      (nfT : isType T) (nfT' : isType T') :
      [Γ |- T ≅ T' : U] ->
      univ_hd_view Γ nfT nfT' ;

    nat_conv_inj (Γ : context) (t t' : term)
      (nft : isNat t) (nft' : isNat t') :
      [Γ |- t ≅ t' : tNat] ->
      nat_hd_view Γ nft nft' ;

    (* empty_conv_inj (Γ : context) (t t' : term) :
      whne t -> whne t' ->
      [Γ |- t ≅ t' : tEmpty] ->
      [Γ |- t ~ t' : tEmpty] ; *)

    id_conv_inj (Γ : context) (A x y t t' : term)
      (nft : isId t) (nft' : isId t') :
      [Γ |- t ≅ t' : tId A x y] ->
      id_hd_view Γ A x y nft nft' ;
    
    (* neu_conv_inj (Γ : context) (A t t' : term) :
      whne A -> whne t -> whne t' ->
      [Γ |- t ≅ t' : A] ->
      [Γ |- t ~ t' : A] *)
  }.

  (** Completeness of neutral conversion, at positive types or at all types *)

  Class ConvNeutralConvPos :=
  {
    conv_neu_conv_p Γ T n n' :
      whne n -> whne n' -> isPosType T ->
      [Γ |- n ≅ n' : T] ->
      [Γ |- n ~ n' : T]
  }.

  Class ConvNeutralConv :=
  {
    conv_neu_conv Γ T n n' :
      whne n -> whne n' ->
      [Γ |- n ≅ n' : T] ->
      [Γ |- n ~ n' : T]
  }.

  (** Injectivity of neutral destructors *)

  Definition ne_view (Γ : context) (T : term) {n n' : term} (ne : whne n) (ne' : whne n') : Type :=
  match ne, ne' with
    | @whne_tRel v, @whne_tRel v' => ∑ T', [× v' = v, in_ctx Γ v T' & [Γ |- T' ≅ T] ]
    | @whne_tApp t u _, @whne_tApp t' u' _ => ∑ A B, [× [Γ |- t ≅ t' : tProd A B], [Γ |- u ≅ u' : A] & [Γ |- B[u..] ≅ T]]
    | @whne_tNatElim P hz hs n _, @whne_tNatElim P' hz' hs' n' _ =>
      [× [Γ |- n ≅ n' : tNat],
        [Γ ,, tNat |- P ≅ P'],
        [Γ |- hz ≅ hz' : P[tZero..]],
        [Γ |- hs ≅ hs' : elimSuccHypTy P] &
        [Γ |- P[n..] ≅ T]]

    | @whne_tEmptyElim P e _, @whne_tEmptyElim P' e' _ =>
      [× [Γ ,, tEmpty |- P ≅ P'],
        [Γ |- e ≅ e' : tEmpty] &
        [Γ |- P[e..] ≅ T]]
        
    | @whne_tFst p _, @whne_tFst p' _ => ∑ A B, [Γ |- p ≅ p' : tSig A B] × [Γ |- A ≅ T]
    | @whne_tSnd p _, @whne_tSnd p' _ => ∑ A B, [Γ |- p ≅ p' : tSig A B] × [Γ |- B[(tFst p)..] ≅ T]
    | @whne_tIdElim A x P hr y e _, @whne_tIdElim A' x' P' hr' y' e' _ =>
      [× [Γ |- A ≅ A'],
        [Γ |- x ≅ x' : A],
        [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'],
        [Γ |- hr ≅ hr' : P[tRefl A x .: x..]],
        [Γ |- y ≅ y' : A],
        [Γ |- e ≅ e' : tId A x y] &
        [Γ |- P[e .: y..] ≅ T]]
    | _, _ => False
  end.

  Class NeutralInj :=
  {
    neu_inj (Γ : context) (T t t' : term)
    (net : whne t) (net' : whne t') :
    [Γ |- t ≅ t' : T] ->
    ne_view Γ T net net'
  }.

  (** ** Normalisation *)

  Record normalising (t : term) := {
    norm_val : term;
    norm_red : [ t ⤳* norm_val ];
    norm_whnf : whnf norm_val;
  }.

  Class Normalisation :=
  {
    tm_norm {Γ A t} : [Γ |- t : A] -> normalising t ;
    ty_norm {Γ A} : [Γ |- A] -> normalising A ;
  }.

  (** ** Canonicity for natural numbers *)

  Class NatCanonicity :=
  {
    nat_canonicity {t} : [ε |- t : tNat] ->
      ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat]
  }.

  Context `{ta' : tag}
    `{!WfContext ta'} `{!WfType ta'} `{!Typing ta'} `{!ConvType ta'} `{!ConvTerm ta'} `{!ConvNeuConv ta'}
    `{!RedType ta'} `{!RedTerm ta'}.

  (** ** Completeness (of typing `ta'` with respect to typing `ta`). *)

  Class ConvComplete := {
    ty_conv_compl Γ A A' : [Γ |-[ta] A ≅ A'] -> [Γ |-[ta'] A ≅ A'] ;
    tm_conv_compl Γ A t t' : [Γ |-[ta] t ≅ t' : A] -> [Γ |-[ta'] t ≅ t' : A] ;
  }.

  Class TypingComplete := {
    ty_compl Γ A : [Γ |-[ta] A] -> [Γ |-[ta'] A] ;
    tm_compl Γ A t : [Γ |-[ta] t : A] -> [Γ |-[ta'] t : A] ;
  }.
  
End Properties.