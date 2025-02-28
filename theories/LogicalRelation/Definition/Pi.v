(** * LogRel.LogicalRelation.Definition.Pi : Definition of the logical relation for dependent products *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Poly.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of product types *)

Definition PiRedTyPack `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} :=
  ParamRedTyPack (T:=tProd).

Definition PiRedTyAdequate@{i j} `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} (R : RedRel@{i j}) (ΠA : PiRedTyPack@{i} Γ A B)
  : Type@{j} := PolyRedPackAdequate R ΠA.

Module PiRedTyPack := ParamRedTyPack.

Inductive isLRFun `{ta : tag} `{WfContext ta}
  `{WfType ta} `{ConvType ta} `{RedType ta} `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta}
  {Γ : context} {A B : term} (ΠA : PiRedTyPack Γ A B) : term -> Type :=
| LamLRFun : forall A' t : term,
    [Γ |- A'] ->
    [Γ |-  ΠA.(PiRedTyPack.domL) ≅ A'] ->
    (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ ΠA.(PolyRedPack.shpRed) ρ h | Δ ||- a ≅ b : ΠA.(PiRedTyPack.domL)⟨ρ⟩ ]),
      [ΠA.(PolyRedPack.posRed) ρ h ha | Δ ||- t[a .: (ρ >> tRel)] ≅ t[b .: (ρ >> tRel)] : ΠA.(PiRedTyPack.codL)[a .: (ρ >> tRel)]]) ->
  isLRFun ΠA (tLambda A' t)
| NeLRFun : forall f : term, [Γ |- f ~ f : PiRedTyPack.outTy ΠA] -> isLRFun ΠA f.

Module PiRedTmEq.

  Import PiRedTyPack.

  Definition appRed `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ A B} (ΠA : PiRedTyPack Γ A B) (nfL nfR : term) Δ a b :=
    forall (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (hab : [ΠA.(PolyRedPack.shpRed) ρ h | Δ ||- a ≅ b : ΠA.(domL)⟨ρ⟩ ] ),
      [ ΠA.(PolyRedPack.posRed) ρ h hab | Δ ||- tApp nfL⟨ρ⟩ a ≅ tApp nfR⟨ρ⟩ b : _ ].

  Arguments appRed /.

  Record PiRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A B} {ΠA : PiRedTyPack Γ A B} {t : term}
  : Type := {
    nf : term;
    red : [ Γ |- t :⤳*: nf : outTy ΠA ];
    isfun : isLRFun ΠA nf;
  }.

  Arguments PiRedTm {_ _ _ _ _ _ _ _ _ _ _ _}.

  Definition whred `{GenericTypingProperties}
    {Γ : context} {A B} {ΠA : PiRedTyPack Γ A B} {t : term} :
    PiRedTm ΠA t -> [Γ |- t ↘  outTy ΠA].
  Proof.
    intros [?? isfun]; econstructor; tea; destruct isfun.
    1: gtyping.
    constructor; now eapply convneu_whne.
  Defined.

  Record PiRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A B : term} {ΠA : PiRedTyPack Γ A B} {t u : term}
  : Type := {
    redL : PiRedTm ΠA t ;
    redR : PiRedTm ΠA u ;
    eq : [ Γ |- redL.(nf) ≅ redR.(nf) : outTy ΠA ];
    eqApp {Δ a b} : appRed ΠA redL.(nf) redR.(nf) Δ a b;
  }.

  Arguments PiRedTmEq {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _.

  Definition whredL `{GenericTypingProperties}
    {Γ : context} {A B} {ΠA : PiRedTyPack Γ A B} {t u : term} :
    PiRedTmEq ΠA t u -> [Γ |- t ↘  outTy ΠA].
  Proof. intros []; now eapply whred. Defined.

  Definition whredR `{GenericTypingProperties}
    {Γ : context} {A B} {ΠA : PiRedTyPack Γ A B} {t u : term} :
    PiRedTmEq ΠA t u -> [Γ |- u ↘  outTy ΠA].
  Proof. intros []; now eapply whred. Defined.

End PiRedTmEq.

Export PiRedTmEq(PiRedTm,Build_PiRedTm,PiRedTmEq,Build_PiRedTmEq).
