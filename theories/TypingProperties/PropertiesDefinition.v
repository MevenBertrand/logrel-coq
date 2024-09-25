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
      | NeType _, NeType _ => [Γ |- T ~ T' : U]
      | @SigType A B, @SigType A' B' => [Γ |- A ≅ A' : U] × [Γ,, A |- B ≅ B' : U]
      | @IdType A x y, @IdType A' x' y' => [× [Γ |- A ≅ A' : U], [Γ |- x ≅ x' : A] & [Γ |- y ≅ y' : A]]
      | _, _ => False
    end.

  Definition nat_hd_view (Γ : context) {t t' : term} (nft : isNat t) (nft' : isNat t') : Type :=
  match nft, nft' with
    | ZeroNat, ZeroNat => True
    | @SuccNat u, @SuccNat u' => [Γ |- u ≅ u' : tNat]
    | NeNat _, NeNat _ => [Γ |- t ~ t' : tNat ]
    | _, _ => False
  end.

  Definition id_hd_view (Γ : context) (A x x' : term) {t t' : term} (nft : isId t) (nft' : isId t') : Type :=
    match nft, nft' with
      | @ReflId A a, @ReflId A' a' => [Γ |- A ≅ A'] × [Γ |- a ≅ a' : A]
      | NeId _, NeId _ => [Γ |- t ~ t' : tId A x x']
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

    empty_conv_inj (Γ : context) (t t' : term) :
      whne t -> whne t' ->
      [Γ |- t ≅ t' : tEmpty] ->
      [Γ |- t ~ t' : tEmpty] ;

    id_conv_inj (Γ : context) (A x y t t' : term)
      (nft : isId t) (nft' : isId t') :
      [Γ |- t ≅ t' : tId A x y] ->
      id_hd_view Γ A x y nft nft' ;
    
    neu_conv_inj (Γ : context) (A t t' : term) :
      whne A -> whne t -> whne t' ->
      [Γ |- t ≅ t' : A] ->
      [Γ |- t ~ t' : A]
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
  
End Properties.