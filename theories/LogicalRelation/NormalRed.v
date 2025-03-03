From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Weakening Neutral Transitivity Reduction.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Ltac redSubst t :=
  repeat lazymatch goal with
  | [H : [_ |- ?X :⤳*: ?Y] |- _] =>
    try (unify t X;
      assert (eeqsubst : X = Y) by (eapply redtywf_whnf ; gen_typing);
      try (injection eeqsubst; intros); subst); block H
  end; unblock.

Section Normalization.
Context `{GenericTypingProperties}.

Program Definition normRedNe0 {Γ A B} (h : [Γ ||-ne A ≅ B]) (wh : whne A) :
  [Γ ||-ne A ≅ B] :=
  {| neRedTy.tyL := A ; neRedTy.tyR := h.(neRedTy.tyR)|}.
Next Obligation.
  pose proof (LRne_ zero h); escape; now eapply redtywf_refl.
Qed.
Next Obligation. now destruct h. Qed.
Next Obligation. destruct h; cbn; now redSubst A. Qed.


Program Definition normRedΠl {Γ F G B l} (h : [Γ ||-Π<l> tProd F G ≅ B])
  : [Γ ||-Π<l> tProd F G ≅ B] :=
  {| ParamRedTy.domL := F ;
     ParamRedTy.codL := G ;
     ParamRedTy.domR := h.(ParamRedTy.domR) ;
     ParamRedTy.codR := h.(ParamRedTy.codR) ; |}.
Solve All Obligations with
  (intros ; destruct h as [???? [] ?]; tea; cbn; redSubst (tProd F G); tea ;
    constructor; tea; eapply redtywf_refl; gtyping).

Program Definition normRedΠr {Γ A F G l} (h : [Γ ||-Π<l> A ≅ tProd F G ])
  : [Γ ||-Π<l> A ≅ tProd F G] :=
  {| ParamRedTy.domR := F ;
     ParamRedTy.codR := G ;
     ParamRedTy.domL := h.(ParamRedTy.domL) ;
     ParamRedTy.codL := h.(ParamRedTy.codL) ; |}.
Solve All Obligations with
  (intros ; destruct h as [???? ? []]; tea; cbn; redSubst (tProd F G); tea ;
    constructor; tea; eapply redtywf_refl; gtyping).

Program Definition normRedΣl {Γ F G B l} (h : [Γ ||-Σ<l> tSig F G ≅ B])
  : [Γ ||-Σ<l> tSig F G ≅ B] :=
  {| ParamRedTy.domL := F ;
     ParamRedTy.codL := G ;
     ParamRedTy.domR := h.(ParamRedTy.domR) ;
     ParamRedTy.codR := h.(ParamRedTy.codR) ; |}.
Solve All Obligations with
  (intros ; destruct h as [???? [] ?]; tea; cbn; redSubst (tSig F G); tea ;
    constructor; tea; eapply redtywf_refl; gtyping).

Program Definition normRedΣr {Γ F G B l} (h : [Γ ||-Σ<l> B ≅ tSig F G])
  : [Γ ||-Σ<l> B ≅ tSig F G ] :=
  {| ParamRedTy.domR := F ;
     ParamRedTy.codR := G ;
     ParamRedTy.domL := h.(ParamRedTy.domL) ;
     ParamRedTy.codL := h.(ParamRedTy.codL) ; |}.
Solve All Obligations with
  (intros ; destruct h as [???? ? []]; tea; cbn; redSubst (tSig F G); tea ;
    constructor; tea; eapply redtywf_refl; gtyping).


Definition normRedΠ {Γ F F' G G' l} (h : [Γ ||-<l> tProd F G ≅ tProd F' G']) : [Γ ||-Π<l> tProd F G ≅ tProd F' G'] :=
  normRedΠr (normRedΠl (invLRΠ h)).

Definition normRedΣ {Γ F F' G G' l} (h : [Γ ||-<l> tSig F G ≅ tSig F' G']) : [Γ ||-Σ<l> tSig F G ≅ tSig F' G'] :=
  normRedΣr (normRedΣl (invLRΣ h)).


#[program]
Definition normRedIdl {Γ A x y B l} (h : [Γ ||-Id<l> tId A x y ≅ B])
  : [Γ ||-Id<l> tId A x y ≅ B] :=
  {| IdRedTy.tyL := A ; IdRedTy.lhsL := x ; IdRedTy.rhsL := y ;
     IdRedTy.tyR := h.(IdRedTy.tyR) ; IdRedTy.lhsR := h.(IdRedTy.lhsR) ; IdRedTy.rhsR := h.(IdRedTy.rhsR) ; |}.
Solve All Obligations with
  intros ; destruct h ; tea; cbn; redSubst (tId A x y);
  tea; first [now eapply irrLR | eapply redtywf_refl; gtyping].

#[program]
Definition normRedIdr {Γ A x y B l} (h : [Γ ||-Id<l> B ≅ tId A x y])
  : [Γ ||-Id<l> B ≅ tId A x y] :=
  {| IdRedTy.tyR := A ; IdRedTy.lhsR := x ; IdRedTy.rhsR := y ;
     IdRedTy.tyL := h.(IdRedTy.tyL) ; IdRedTy.lhsL := h.(IdRedTy.lhsL) ; IdRedTy.rhsL := h.(IdRedTy.rhsL) ; |}.
Solve All Obligations with
  intros ; destruct h ; tea; cbn; redSubst (tId A x y);
  tea; first [now eapply irrLR | eapply redtywf_refl; gtyping].


Definition normRedId {Γ A A' x x' y y' l} (h : [Γ ||-<l> tId A x y ≅ tId A' x' y']) : [Γ ||-Id<l> tId A x y ≅ tId A' x' y'] :=
  normRedIdr (normRedIdl (invLRId h)).

End Normalization.
