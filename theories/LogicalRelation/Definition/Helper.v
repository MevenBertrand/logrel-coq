(** * LogRel.LogicalRelation.Definition.Helper: Auxilliary definitions and rebundling of structures from the logical relation *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne Universe Poly Pi Sig Nat Empty Id Def.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Lemma instKripke `{GenericTypingProperties} {Γ A B l} (wfΓ : [|-Γ])
  (h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ B⟨ρ⟩]) : [Γ ||-<l> A ≅ B].
Proof.
  specialize (h Γ wk_id wfΓ); now rewrite 2!wk_id_ren_on in h.
Qed.

(** ** Rebundling reducibility of Polynomial *)

(** The definition of reducibility of product types in the logical relation, which separates
the "adequacy" part is not nice to work with. Here we relate it to the more natural one,
which lets us later on define an induction principle that does not show the separation at all. *)

Module PolyRed.

Section PolyRed.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}
    {Γ : context} {l : TypeLevel} {shp shp' pos pos' : term}.

  Record PolyRed@{i j k l} : Type@{l} :=
    {
      shpRed [Δ] (ρ : Δ ≤ Γ) : [ |- Δ ] -> [ LogRel@{i j k l} l | Δ ||- shp⟨ρ⟩ ≅ shp'⟨ρ⟩ ] ;
      posRed [Δ a b] (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
          [ (shpRed ρ h) |  Δ ||- a ≅ b : shp⟨ρ⟩] ->
          [ LogRel@{i j k l} l | Δ ||- pos[a .: (ρ >> tRel)] ≅ pos'[b .: (ρ >> tRel)]] ;
    }.

  Definition from@{i j k l} {PA : PolyRedPack@{k} Γ shp shp' pos pos'}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : PolyRed@{i j k l}.
  Proof.
    unshelve econstructor; intros.
    - econstructor; unshelve eapply PolyRedPack.shpAd; cycle 2; tea.
    - econstructor; unshelve eapply PolyRedPack.posAd; cycle 2; tea.
  Defined.

  Definition toPack@{i j k l} (PA : PolyRed@{i j k l}) : PolyRedPack@{k} Γ shp shp' pos pos'.
  Proof.
    unshelve econstructor.
    - now eapply shpRed.
    - intros; now eapply posRed.
  Defined.

  Definition toAd@{i j k l} (PA : PolyRed@{i j k l}) : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) (toPack PA).
  Proof.
    unshelve econstructor; intros.
    - eapply LRAd.adequate; eapply posRed.
    - eapply LRAd.adequate; eapply shpRed.
  Defined.

  Lemma eta@{i j k l} (PA : PolyRed@{i j k l}) : from (toAd PA) = PA.
  Proof. destruct PA; reflexivity. Qed.

  Lemma beta_pack@{i j k l} {PA : PolyRedPack@{k} Γ shp shp' pos pos'}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toPack (from PAad) = PA.
  Proof. destruct PA, PAad; reflexivity. Qed.

  Lemma beta_ad@{i j k l} {PA : PolyRedPack@{k} Γ shp shp' pos pos'}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toAd (from PAad) = PAad.
  Proof. destruct PA, PAad; reflexivity. Qed.

End PolyRed.

Arguments PolyRed : clear implicits.
Arguments PolyRed {_ _ _ _ _ _ _ _ _} _ _ _ _ _.

End PolyRed.

Export PolyRed(PolyRed,Build_PolyRed).
Coercion PolyRed.toPack : PolyRed >-> PolyRedPack.

Module ParamRedTy.
Section ParamRedTy.
  Context {T : term -> term -> term} `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}
    {Γ : context} {l : TypeLevel} {A B : term}.

  Record ParamRedTy@{i j k l} : Type@{l} :=
    {
      domL : term ;
      domR : term ;
      codL : term ;
      codR : term ;
      redL : ParamRedTyPack.ParamTy (T:=T) Γ A domL codL ;
      redR : ParamRedTyPack.ParamTy (T:=T) Γ B domR codR ;
      eqdom : [Γ |- domL ≅ domR];
      eq : [Γ |- T domL codL ≅ T domR codR] ;
      polyRed :> PolyRed@{i j k l} Γ l domL domR codL codR
    }.

  Definition from@{i j k l} {PA : ParamRedTyPack@{k} (T:=T) Γ A B}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA) :
    ParamRedTy@{i j k l}.
  Proof.
    exists (ParamRedTyPack.domL PA) (ParamRedTyPack.domR PA)
      (ParamRedTyPack.codL PA) (ParamRedTyPack.codR PA).
    - eapply ParamRedTyPack.redL.
    - eapply ParamRedTyPack.redR.
    - eapply ParamRedTyPack.eqdom.
    - eapply ParamRedTyPack.eq.
    - now eapply PolyRed.from.
  Defined.

  Definition toPack@{i j k l} (PA : ParamRedTy@{i j k l}) :
    ParamRedTyPack@{k} (T:=T) Γ A B.
  Proof.
    exists (domL PA) (domR PA) (codL PA) (codR PA).
    - now eapply redL.
    - now eapply redR.
    - apply eqdom.
    - now eapply eq.
    - exact (PolyRed.toPack PA).
  Defined.

  Definition toAd@{i j k l} (PA : ParamRedTy@{i j k l}) :
    PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) (toPack PA) :=
    PolyRed.toAd PA.

  Lemma eta@{i j k l} (PA : ParamRedTy@{i j k l}) : from (toAd PA) = PA.
  Proof. destruct PA; reflexivity. Qed.

  Lemma beta_pack@{i j k l} {PA : ParamRedTyPack@{k} (T:=T) Γ A B}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toPack (from PAad) = PA.
  Proof. destruct PA, PAad; reflexivity. Qed.

  Lemma beta_ad@{i j k l} {PA : ParamRedTyPack@{k} (T:=T) Γ A B}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toAd (from PAad) = PAad.
  Proof. destruct PA, PAad; reflexivity. Qed.

  Definition outTyL (PA : ParamRedTy)  := ParamRedTyPack.outTy (toPack PA).
  Definition outTyR (PA : ParamRedTy)  := T PA.(domR) PA.(codR).

End ParamRedTy.

Arguments ParamRedTy : clear implicits.
Arguments ParamRedTy _ {_ _ _ _ _ _ _ _ _}.

End ParamRedTy.

(** ** Rebundling reducibility of product and sigma types *)

Export ParamRedTy(ParamRedTy, Build_ParamRedTy, outTyL, outTyR).
Coercion ParamRedTy.polyRed : ParamRedTy >-> PolyRed.
Coercion ParamRedTy.toPack : ParamRedTy >-> ParamRedTyPack.
Arguments outTyL _ /.
Arguments outTyR _ /.

Section EvenMoreDefs.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Definition PiRedTy@{i j k l} Γ l A B := ParamRedTy@{i j k l} tProd Γ l A B.
  Definition SigRedTy@{i j k l} Γ l A B := ParamRedTy@{i j k l} tSig Γ l A B.

  Definition LRPi'@{i j k l} {l Γ A B} (ΠA : PiRedTy@{i j k l} Γ l A B)
    : [ LogRel@{i j k l} l | Γ ||- A ≅ B ] :=
    LRbuild (LRPi (LogRelRec l) _ (ParamRedTy.toAd ΠA)).

  Definition LRSig' @{i j k l} {l Γ A B} (ΠA : SigRedTy@{i j k l} Γ l A B)
    : [ LogRel@{i j k l} l | Γ ||- A ≅ B] :=
    LRbuild (LRSig (LogRelRec l) _ (ParamRedTy.toAd ΠA)).

End EvenMoreDefs.

Notation "[ Γ ||-Π< l > A ≅ B ]" := (PiRedTy Γ l A B) (at level 0, Γ, l, A, B at level 50).
Notation "[ Γ ||-Σ< l > A ≅ B ]" := (SigRedTy Γ l A B) (at level 0, Γ, l, A, B at level 50).
Notation "[ Γ ||-Π t ≅ u : A | ΠA ]" := (PiRedTmEq (Γ:=Γ) (A:=A) t u (ParamRedTy.toPack ΠA)).
Notation "[ Γ ||-Σ t ≅ u : A | ΣA ]" := (SigRedTmEq (Γ:=Γ) (A:=A) t u (ParamRedTy.toPack ΣA)).

Module PiRedTy.
  Include ParamRedTyPack.

  Section PiRedTy.
  Context `{GenericTypingProperties}.
  Definition whredL  {l Γ A B} : PiRedTy Γ l A B -> [Γ |- A ↘ ] :=
    ParamRedTyPack.whredL0 (T:=tProd) ltac:(intros; constructor).
  Definition whredR  {l Γ A B} : PiRedTy Γ l A B -> [Γ |- B ↘ ] :=
    ParamRedTyPack.whredR0 (T:=tProd) ltac:(intros; constructor).
  End PiRedTy.
End PiRedTy.

#[program]
Instance PiRedTyWhRed `{GenericTypingProperties} {Γ l} : WhRedTyRel Γ (PiRedTy Γ l) :=
  {| whredtyL := fun A B RAB => PiRedTy.whredL RAB ;
     whredtyR := fun A B RAB => PiRedTy.whredR RAB ; |}.
Next Obligation. now destruct h. Qed.

Instance PiRedTmWhRed `{GenericTypingProperties} {Γ l A B} (ΠA : [Γ ||-Π<l> A ≅ B])
  : WhRedTm Γ (outTyL ΠA) (PiRedTm ΠA) := fun t Rt => PiRedTmEq.whred Rt.

#[program]
Instance PiRedTmWhRedRel `{GenericTypingProperties} {Γ l A B} (ΠA : [Γ ||-Π<l> A ≅ B])
  : WhRedTmRel Γ (outTyL ΠA) (PiRedTmEq ΠA) :=
  {| whredtmL := fun t u Rtu => PiRedTmEq.whredL Rtu ;
     whredtmR := fun t u Rtu => PiRedTmEq.whredR Rtu ; |}.
Next Obligation. now destruct h. Qed.

Module SigRedTy.
  Include ParamRedTyPack.

  Section SigRedTy.
  Context `{GenericTypingProperties}.
  Definition whredL  {l Γ A B} : SigRedTy Γ l A B -> [Γ |- A ↘ ] :=
    ParamRedTyPack.whredL0 (T:=tSig) ltac:(intros; constructor).
  Definition whredR  {l Γ A B} : SigRedTy Γ l A B -> [Γ |- B ↘ ] :=
    ParamRedTyPack.whredR0 (T:=tSig) ltac:(intros; constructor).
  End SigRedTy.
End SigRedTy.

#[program]
Instance SigRedTyWhRed `{GenericTypingProperties} {Γ l} : WhRedTyRel Γ (SigRedTy Γ l) :=
  {| whredtyL := fun A B RAB => SigRedTy.whredL RAB ;
     whredtyR := fun A B RAB => SigRedTy.whredR RAB ; |}.
Next Obligation. now destruct h. Qed.

Instance SigRedTmWhRed `{GenericTypingProperties} {Γ l A B} (ΠA : [Γ ||-Σ<l> A ≅ B])
  : WhRedTm Γ (outTyL ΠA) (SigRedTm ΠA) := fun t Rt => SigRedTmEq.whred Rt.

#[program]
Instance SigRedTmWhRedRel `{GenericTypingProperties} {Γ l A B} (ΠA : [Γ ||-Σ<l> A ≅ B])
  : WhRedTmRel Γ (outTyL ΠA) (SigRedTmEq ΠA) :=
  {| whredtmL := fun t u Rtu => SigRedTmEq.whredL Rtu ;
     whredtmR := fun t u Rtu => SigRedTmEq.whredR Rtu ; |}.
Next Obligation. now destruct h. Qed.


Module IdRedTy.
Section IdRedTy.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Record IdRedTy@{i j k l} {Γ : context} {l} {A B : term}
  : Type :=
  {
    tyL : term ;
    tyR : term ;
    lhsL : term ;
    lhsR : term ;
    rhsL : term ;
    rhsR : term ;
    redL : [Γ |- A :⤳*: tId tyL lhsL rhsL] ;
    redR : [Γ |- B :⤳*: tId tyR lhsR rhsR] ;
    eq : [Γ |- tId tyL lhsL rhsL ≅ tId tyR lhsR rhsR] ;
    tyRed : [ LogRel@{i j k l} l | Γ ||- tyL ≅ tyR ] ;
    lhsRed : [ tyRed | Γ ||- lhsL ≅ lhsR : _ ] ;
    rhsRed : [ tyRed | Γ ||- rhsL ≅ rhsR : _ ] ;
    (* Bake in PER property for reducible conversion at ty  to cut dependency cycles *)
    tyPER : PER tyRed.(LRPack.eqTm) ;
  }.



  Definition from@{i j k l} {Γ l A B} {IA : IdRedTyPack@{k} Γ A B} (IAad : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) IA)
    : @IdRedTy@{i j k l} Γ l A B.
  Proof.
    unshelve econstructor; try (exact IA.(IdRedTyPack.redL) + exact IA.(IdRedTyPack.redR)).
    - econstructor; apply IAad.
    - exact IA.(IdRedTyPack.eq).
    - exact IA.(IdRedTyPack.lhsRed).
    - exact IA.(IdRedTyPack.rhsRed).
    - exact IA.(IdRedTyPack.tyPER).
  Defined.

  Definition toPack@{i j k l} {Γ l A B} (IA : @IdRedTy@{i j k l} Γ l A B) : IdRedTyPack@{k} Γ A B.
  Proof.
    unshelve econstructor; try (exact IA.(IdRedTy.redL) + exact IA.(IdRedTy.redR)).
    - apply IA.(tyRed).
    - exact IA.(eq).
    - exact IA.(lhsRed).
    - exact IA.(rhsRed).
    - exact IA.(IdRedTy.tyPER).
  Defined.

  Definition to@{i j k l} {Γ l A B} (IA : @IdRedTy@{i j k l} Γ l A B) : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) (toPack IA).
  Proof.
    econstructor; apply IA.(tyRed).
  Defined.

  Lemma beta_pack@{i j k l} {Γ l A B} {IA : IdRedTyPack@{k} Γ A B} (IAad : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) IA) :
    toPack (from IAad) = IA.
  Proof. reflexivity. Qed.

  Lemma beta_ad@{i j k l} {Γ l A B} {IA : IdRedTyPack@{k} Γ A B} (IAad : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) IA) :
    to (from IAad) = IAad.
  Proof. reflexivity. Qed.

  Lemma eta@{i j k l} {Γ l A B} (IA : @IdRedTy@{i j k l} Γ l A B) : from  (to IA) = IA.
  Proof. reflexivity. Qed.

  Definition IdRedTmEq {Γ l A B} (IA : @IdRedTy Γ l A B) := IdRedTmEq (toPack IA).
  Definition IdPropEq {Γ l A B} (IA : @IdRedTy Γ l A B) := IdPropEq (toPack IA).

  Definition LRId'@{i j k l} {l Γ A B} (IA : @IdRedTy@{i j k l} Γ l A B)
    : [ LogRel@{i j k l} l | Γ ||- A ≅ B] :=
    LRbuild (LRId (LogRelRec l) _ (to IA)).
End IdRedTy.

Arguments IdRedTy {_ _ _ _ _ _ _ _ _}.

  Definition whredL `{GenericTypingProperties} {l Γ A B} : IdRedTy Γ l A B -> [Γ |- A ↘ ].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition whredR `{GenericTypingProperties} {l Γ A B} : IdRedTy Γ l A B -> [Γ |- B ↘ ].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition outTy `{GenericTypingProperties} {l Γ A B} (IA : IdRedTy Γ l A B) := IdRedTyPack.outTy (toPack IA).

End IdRedTy.

Export IdRedTy(IdRedTy, Build_IdRedTy,IdRedTmEq,IdPropEq,LRId').
Arguments IdRedTy.outTy _ /.

Notation "[ Γ ||-Id< l > A ≅ B ]" := (IdRedTy Γ l A B) (at level 0, Γ, l,  A, B at level 50).
Notation "[ Γ ||-Id< l > t : A | RA ]" := (IdRedTmEq (Γ:=Γ) (l:=l) (A:=A) RA t t) (at level 0, Γ, l, t, A, RA at level 50).
Notation "[ Γ ||-Id< l > t ≅ u : A | RA ]" := (IdRedTmEq (Γ:=Γ) (l:=l) (A:=A) RA t u) (at level 0, Γ, l, t, u, A, RA at level 50).

#[program]
Instance IdRedTyWhRed `{GenericTypingProperties} {Γ l} : WhRedTyRel Γ (IdRedTy Γ l) :=
  {| whredtyL := fun A B RAB => IdRedTy.whredL RAB ;
     whredtyR := fun A B RAB => IdRedTy.whredR RAB ; |}.
Next Obligation. now destruct h. Qed.

#[program]
Instance IdRedTmWhRedRel `{GenericTypingProperties} {Γ l A B} (IA : [Γ ||-Id<l> A ≅ B])
  : WhRedTmRel Γ (IdRedTy.outTy IA) (IdRedTmEq IA) :=
  {| whredtmL := fun t u Rtu => IdRedTmEq.whredL Rtu ;
     whredtmR := fun t u Rtu => IdRedTmEq.whredR Rtu ; |}.
Next Obligation. now destruct h. Qed.

#[program]
Instance URedTmEqWhRedRel  `{GenericTypingProperties} {Γ l A B} (UA : [Γ ||-U<l> A ≅ B])
  : WhRedTmRel Γ U (URedTmEq (LogRelRec l) Γ _ _ UA) :=
  {| whredtmL := fun t u Rtu => URedTm.whredL Rtu ;
     whredtmR := fun t u Rtu => URedTm.whredR Rtu ; |}.
Next Obligation. now destruct h. Qed.










