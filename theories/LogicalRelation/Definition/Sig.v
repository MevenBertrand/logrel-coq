(** * LogRel.LogicalRelation.Definition.Sig : Definition of the logical relation for dependent sums *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Poly.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of dependent sum types *)

Definition SigRedTyPack `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} :=
  ParamRedTyPack (T:=tSig).

Definition SigRedTyAdequate@{i j} `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} (R : RedRel@{i j}) (ΣA : SigRedTyPack@{i} Γ A B)
  : Type@{j} := PolyRedPackAdequate R ΣA.

Module SigRedTyPack := ParamRedTyPack.

Inductive isLRPair `{ta : tag} `{WfContext ta}
  `{WfType ta} `{ConvType ta} `{RedType ta} `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta}
  {Γ : context} {A B : term} (ΣA : SigRedTyPack Γ A B) : term -> Type :=
| PairLRPair : forall (A' B' a b : term)
      (wtydom : [Γ |- A'])
      (convtydom : [Γ |- SigRedTyPack.domL ΣA ≅ A'])
      (wtycod : [Γ |- B'[a..]])
      (convtycod : [Γ |- (SigRedTyPack.codL ΣA)[a..] ≅ B'[a..]])
  (rfst : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]),
      [ΣA.(PolyRedPack.shpRed) ρ h | Δ ||- a⟨ρ⟩ ≅ a⟨ρ⟩ : (SigRedTyPack.domL ΣA)⟨ρ⟩])
  (rsnd : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]),
      [ΣA.(PolyRedPack.posRed) ρ h (rfst ρ h) | Δ ||- b⟨ρ⟩ ≅ b⟨ρ⟩ : (SigRedTyPack.codL ΣA)[a⟨ρ⟩ .: (ρ >> tRel)] ]),

  isLRPair ΣA (tPair A' B' a b)

| NeLRPair : forall p : term, [Γ |- p ~ p : SigRedTyPack.outTy ΣA] -> isLRPair ΣA p.

Module SigRedTmEq.

  Record SigRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A B : term} {ΣA : SigRedTyPack Γ A B} {t : term}
  : Type := {
    nf : term;
    red : [ Γ |- t :⤳*: nf : SigRedTyPack.outTy ΣA ];
    ispair : isLRPair ΣA nf;
  }.

  Arguments SigRedTm {_ _ _ _ _ _ _ _ _ _ _ _}.

  Lemma whnf `{GenericTypingProperties} {Γ A B} {ΣA : SigRedTyPack Γ A B} {t} :
    forall (red : SigRedTm ΣA t), whnf (nf red).
  Proof.
    intros [? ? ispair]; simpl; destruct ispair; constructor; tea.
    now eapply convneu_whne.
  Qed.

  Definition whred `{GenericTypingProperties} {Γ A B} {ΣA : SigRedTyPack Γ A B} {t} :
    SigRedTm ΣA t -> [Γ |- t ↘  SigRedTyPack.outTy ΣA].
  Proof.
    intros [?? ispair]; econstructor; tea.
    destruct ispair; constructor; now eapply convneu_whne.
  Defined.

  Record SigRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A B : term} {ΣA : SigRedTyPack Γ A B} {t u : term}
  : Type := {
    redL : SigRedTm ΣA t ;
    redR : SigRedTm ΣA u ;
    eq : [ Γ |- redL.(nf) ≅ redR.(nf) : SigRedTyPack.outTy ΣA ];
    eqFst [Δ] (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
      [ΣA.(PolyRedPack.shpRed) ρ h | Δ ||- tFst redL.(nf)⟨ρ⟩ ≅ tFst redR.(nf)⟨ρ⟩ : ΣA.(ParamRedTyPack.domL)⟨ρ⟩] ;
    eqSnd [Δ] (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
      [ΣA.(PolyRedPack.posRed) ρ h (eqFst ρ h) | Δ ||- tSnd redL.(nf)⟨ρ⟩ ≅ tSnd redR.(nf)⟨ρ⟩ : _] ;
  }.

  Arguments SigRedTmEq {_ _ _ _ _ _ _ _ _ _ _ _}.

  Definition whredL `{GenericTypingProperties} {Γ A B} {ΣA : SigRedTyPack Γ A B} {t u} :
    SigRedTmEq ΣA t u -> [Γ |- t ↘  SigRedTyPack.outTy ΣA ].
  Proof. intros []; now eapply whred. Defined.

  Definition whredR `{GenericTypingProperties} {Γ A B} {ΣA : SigRedTyPack Γ A B} {t u} :
    SigRedTmEq ΣA t u -> [Γ |- u ↘  SigRedTyPack.outTy ΣA ].
  Proof. intros []; now eapply whred. Defined.

End SigRedTmEq.

Export SigRedTmEq(SigRedTm,Build_SigRedTm, SigRedTmEq,Build_SigRedTmEq).