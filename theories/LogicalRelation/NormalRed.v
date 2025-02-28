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

(* #[program]
Definition normLambda {Γ F Fl Fr G tl tr l RΠ}
  (Rlam : [Γ ||-<l> tLambda Fl tl ≅ tLambda Fr tr : tProd F G | normRedΠ RΠ ]) :
  [Γ ||-<l> tLambda Fl tl ≅ tLambda Fr tr : tProd F G | normRedΠ RΠ ] :=
  {|
    PiRedTmEq.redL := {| PiRedTmEq.nf := tLambda Fl tl |} ;
    PiRedTmEq.redR := {| PiRedTmEq.nf := tLambda Fr tr |}
  |}.
Solve All Obligations with
  intros;
  pose proof (eL := redtmwf_whnf (PiRedTmEq.red Rlam.(PiRedTmEq.redL)) whnf_tLambda);
  pose proof (eR := redtmwf_whnf (PiRedTmEq.red Rlam.(PiRedTmEq.redR)) whnf_tLambda);
  destruct Rlam as [[] [] app eqq]; cbn in *; subst;
  first [eapply app | now eapply eqq| eassumption].


#[program]
Definition normPair {Γ F Fl Fr G Gl Gr fl fr gl gr l RΣ}
  (Rp : [Γ ||-<l> tPair Fl Gl fl gl ≅ tPair Fr Gr fr gr : tSig F G | normRedΣ RΣ ]) :
  [Γ ||-<l> tPair Fl Gl fl gl ≅ tPair Fr Gr fr gr : tSig F G | normRedΣ RΣ ] :=
  {| SigRedTmEq.redL := {| SigRedTmEq.nf := tPair Fl Gl fl gl |} ;
     SigRedTmEq.redR := {| SigRedTmEq.nf := tPair Fr Gr fr gr |} |}.
Solve All Obligations with
  intros;
  pose proof (eL := redtmwf_whnf (SigRedTmEq.red (SigRedTmEq.redL Rp)) whnf_tPair);
  pose proof (eR := redtmwf_whnf (SigRedTmEq.red (SigRedTmEq.redR Rp)) whnf_tPair);
  destruct Rp as [[] [] ? fstRed sndRed]; cbn in *; subst;
  first [eapply fstRed | irrelevanceRefl; now unshelve eapply sndRed| eassumption].

Definition invLRcan {Γ l A} (lr : [Γ ||-<l> A]) (w : isType A) : [Γ ||-<l> A] :=
  match w as w in isType A return forall (lr : [Γ ||-<l> A]), invLRTy lr (reflexivity A) w -> [Γ ||-<l> A] with
  | UnivType => fun _ x => LRU_ x
  | ProdType => fun _ x => LRPi' (normRedΠ0 x)
  | NatType => fun _ x => LRNat_ _ x
  | EmptyType => fun _ x => LREmpty_  _ x
  | SigType => fun _ x => LRSig' (normRedΣ0 x)
  | IdType => fun _ x => LRId' x
  | NeType wh => fun _ x => LRne_ _ (normRedNe0 x wh)
  end lr (invLR lr (reflexivity A) w). *)

End Normalization.

(** ** Tactics for normalizing the proof relevant components of a reducible type *)

(* Normalizes a term reducible at a Π type *)

(* Ltac normRedΠin X :=
  let g := type of X in
  match g with
  (* | [ LRAd.pack ?R | _ ||- ?t : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRPi' (normRedΠ0 (invLRΠ R))]) by irrelevance; clear X' *)
  | [ LRAd.pack ?R | _ ||- _ ≅ ?B] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> _ ≅ B | LRPi' (normRedΠ0 (invLRΠ R))]) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- ?t ≅ ?u : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t ≅ u : _ | LRPi' (normRedΠ0 (invLRΠ R))]) by irrelevance; clear X'
  end.

Goal forall `{GenericTypingProperties} Γ A B l R f X
  (RABX : [Γ ||-<l> arr A B ≅ X | R])
  (* (Rf : [Γ ||-<l> f : arr A B | R]) *)
  (Rff : [Γ ||-<l> f ≅ f : arr A B | R])
, True.
Proof.
  intros.
  (* normRedΠin Rf. *)
  normRedΠin Rff.
  normRedΠin RABX.
  constructor.
Qed.

(* Normalizes a goal reducible at a Π type *)

Ltac normRedΠ id :=
  let G := fresh "G" in
  set (G := _);
  let g := eval unfold G in G in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t ≅ ?u : _] =>
    pose (id := normRedΠ0 (invLRΠ R)); subst G;
    enough [_ ||-<_> t ≅ u : _ | LRPi' id] by irrelevance
  end.

(* Normalizes a term reducible at a Σ type *)

Ltac normRedΣin X :=
  let g := type of X in
  match g with
  (* | [ LRAd.pack ?R | _ ||- ?t : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRSig' (normRedΣ0 (invLRΣ R))]) by irrelevance; clear X' *)
  | [ LRAd.pack ?R | _ ||- _ ≅ ?B] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> _ ≅ B | LRSig' (normRedΣ0 (invLRΣ R))]) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- ?t ≅ ?u : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t ≅ u : _ | LRSig' (normRedΣ0 (invLRΣ R))]) by irrelevance; clear X'
  end. *)