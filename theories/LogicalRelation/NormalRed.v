
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction EqRedRight.

Set Universe Polymorphism.

Ltac redSubst :=
  match goal with
  | [H : [_ |- ?X :⤳*: ?Y] |- _] =>
    assert (X = Y)by (eapply redtywf_whnf ; gen_typing); subst; clear H
  end.


Section Normalization.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Program Definition normRedNe0 {Γ A} (h : [Γ ||-ne A]) (wh : whne A) :
  [Γ ||-ne A] :=
  {| neRedTy.ty := A |}.
Next Obligation.
  pose proof (LRne_ zero h); escape; now eapply redtywf_refl.
Qed.
Next Obligation. destruct h; now redSubst. Qed.


Program Definition normRedΠ0 {Γ F G l} (h : [Γ ||-Π<l> tProd F G])
  : [Γ ||-Π<l> tProd F G] :=
  {| PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with
  intros; pose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tProd);
  symmetry in e; injection e; clear e;
  destruct h ; intros; cbn in *; subst; eassumption.

Program Definition normRedΣ0 {Γ F G l} (h : [Γ ||-Σ<l> tSig F G])
  : [Γ ||-Σ<l> tSig F G] :=
  {| PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with
  intros; pose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tSig);
  symmetry in e; injection e; clear e;
  destruct h ; intros; cbn in *; subst; eassumption.

Definition normRedΠ {Γ F G l} (h : [Γ ||-<l> tProd F G]) : [Γ ||-<l> tProd F G] :=
  LRPi' (normRedΠ0 (invLRΠ h)).

#[program]
Definition normEqRedΠ {Γ F F' G G' l} (h : [Γ ||-<l> tProd F G])
  (heq : [Γ ||-<l> _ ≅ tProd F' G' | h]) : [Γ ||-<l> _ ≅ tProd F' G' | normRedΠ h] :=
  {|
    PiRedTyEq.dom := F';
    PiRedTyEq.cod := G';
  |}.
Solve All Obligations with
  intros; assert[Γ ||-<l> _ ≅ tProd F' G' | normRedΠ h] as [?? red] by irrelevance;
  pose proof (e := redtywf_whnf red whnf_tProd);
  symmetry in e; injection e; clear e;
  destruct h ; intros; cbn in *; subst; eassumption.

Definition normRedΣ {Γ F G l} (h : [Γ ||-<l> tSig F G]) : [Γ ||-<l> tSig F G] :=
  LRSig' (normRedΣ0 (invLRΣ h)).

#[program]
Definition normEqRedΣ {Γ F F' G G' l} (h : [Γ ||-<l> tSig F G])
  (heq : [Γ ||-<l> _ ≅ tSig F' G' | h]) : [Γ ||-<l> _ ≅ tSig F' G' | normRedΣ h] :=
  {|
    PiRedTyEq.dom := F';
    PiRedTyEq.cod := G';
  |}.
Solve All Obligations with
  intros; assert[Γ ||-<l> _ ≅ tSig F' G' | normRedΣ h] as [?? red] by irrelevance;
  pose proof (e := redtywf_whnf red whnf_tSig);
  symmetry in e; injection e; clear e;
  destruct h ; intros; cbn in *; subst; eassumption.

#[program]
Definition normRedId0 {Γ A x y l} (h : [Γ ||-Id<l> tId A x y])
  : [Γ ||-Id<l> tId A x y] :=
  mkIdRedTy A x y _ _ _ _.
Solve All Obligations with
  intros; pose proof (e := redtywf_whnf (IdRedTy.red h) whnf_tId);
  symmetry in e; injection e; clear e;
  destruct h ; intros; cbn in *; subst;
  first [eassumption | irrelevance].

Definition normRedId {Γ A x y l} (h : [Γ ||-<l> tId A x y]) : [Γ ||-<l> tId A x y] :=
  LRId' (normRedId0 (invLRId h)).

#[program]
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
  end lr (invLR lr (reflexivity A) w).

End Normalization.

(** ** Tactics for normalizing the proof relevant components of a reducible type *)

(* Normalizes a term reducible at a Π type *)

Ltac normRedΠin X :=
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

(* Normalizes a term reducible at a Π type *)

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
  end.
