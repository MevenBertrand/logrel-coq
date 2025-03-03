(** * LogRel.LogicalRelation.Definition.Poly : Definition of the logical relation for polynomial *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of a polynomial A,, B  *)

Module PolyRedPack.

  (* A polynomial is a pair (shp, pos) of a type of shapes [Γ |- shp] and
    a dependent type of positions [Γ |- pos] *)
  (* This should be used as a common entry for Π, Σ, W and M types *)

  Record PolyRedPack@{i} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta}
    {Γ : context} {shp shp' pos pos' : term}
  : Type (* @ max(Set, i+1) *) := {
    shpRed {Δ} (ρ : Δ ≤ Γ) : [ |- Δ ] -> LRPack@{i} Δ shp⟨ρ⟩ shp'⟨ρ⟩ ;
    posRed {Δ} {a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
        [ (shpRed ρ h) |  Δ ||- a ≅ b : shp⟨ρ⟩ ≅ shp'⟨ρ⟩] ->
        LRPack@{i} Δ (pos[a .: (ρ >> tRel)]) (pos'[b .: (ρ >> tRel)]);
  }.

  Arguments PolyRedPack {_ _ _ _}.

  (** We separate the recursive "data", ie the fact that we have reducibility data (an LRPack)
  for the domain and codomain, and the fact that these are in the graph of the logical relation.
  This is crucial for Coq to accept the definition, because it makes the nesting simple enough
  to be accepted. We later on show an induction principle that does not have this separation to
  make reasoning easier. *)
  Record PolyRedPackAdequate@{i j} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} {shp shp' pos pos' : term}
    {Γ : context} {R : RedRel@{i j}}  {PA : PolyRedPack@{i} Γ shp shp' pos pos'}
  : Type@{j} := {
    shpAd {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) : LRPackAdequate@{i j} R (PA.(shpRed) ρ h);
    posAd {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ PA.(shpRed) ρ h | Δ ||- a ≅ b : shp⟨ρ⟩ ])
      : LRPackAdequate@{i j} R (PA.(posRed) ρ h ha);
  }.

  Arguments PolyRedPackAdequate {_ _ _ _ _ _ _ _ _}.

End PolyRedPack.

Export PolyRedPack(PolyRedPack, Build_PolyRedPack, PolyRedPackAdequate, Build_PolyRedPackAdequate).


Module ParamRedTyPack.

  Record ParamTy {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A dom cod : term} := {
      red : [Γ |- A :⤳*: T dom cod];
      domTy : [Γ |- dom] ;
      codTy : [Γ,, dom |- cod] ;
  }.

  Arguments ParamTy {_ _ _ _ _ _}.

  Definition whred {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A dom cod : term} :
    (forall a b, isType (T a b)) ->
    ParamTy (T:=T) Γ A dom cod -> [Γ |- A ↘ ].
  Proof. intros h []; econstructor; tea; apply h. Defined.

  Record ParamRedTyPack {T : term -> term -> term}
    `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Type := {
    domL : term ;
    domR : term ;
    codL : term ;
    codR : term ;
    redL : ParamTy (T:=T) Γ A domL codL ;
    redR : ParamTy (T:=T) Γ B domR codR ;
    eqdom : [Γ |- domL ≅ domR];
    eq : [Γ |- T domL codL ≅ T domR codR];

    polyRed : PolyRedPack Γ domL domR codL codR ;
  }.


  Arguments ParamRedTyPack {_ _ _ _ _ _}.

  Definition outTy {T : term -> term -> term}
    `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} (PA : ParamRedTyPack (T:=T) Γ A B) :=
    T PA.(domL) PA.(codL).

  Arguments outTy {_ _ _ _ _ _ _ _ _} _ /.

  Definition whredL0 {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} :
    (forall a b, isType (T a b)) ->
    ParamRedTyPack (T:=T) Γ A B -> [Γ |- A ↘ ].
  Proof. intros h []; now eapply whred. Defined.

  Definition whredR0 {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} :
    (forall a b, isType (T a b)) ->
    ParamRedTyPack (T:=T) Γ A B -> [Γ |- B ↘ ].
  Proof. intros h []; now eapply whred. Defined.

End ParamRedTyPack.

Export ParamRedTyPack(ParamRedTyPack, Build_ParamRedTyPack, outTy).
Coercion ParamRedTyPack.polyRed : ParamRedTyPack >-> PolyRedPack.
