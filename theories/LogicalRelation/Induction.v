(** * LogRel.LogicalRelation.Induction: good induction principles for the logical relation. *)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.

Set Universe Polymorphism.

(** As Coq is not currently able to define induction principles for nested inductive types
as our LR, we need to prove them by hand. We use this occasion to write down principles which
do not directly correspond to what LR would give us. More precisely, our induction principles:
- handle the two levels uniformly, rather than having to do two separate
  proofs, one at level zero and one at level one;
- apply directly to an inhabitant of the bundled logical relation, rather than the raw LR;
- give a more streamlined minor premise to prove for the case of Π type reducibility,
  which hides the separation needed in LR between the reducibility data and its adequacy
  (ie the two ΠA and ΠAad arguments to constructor LRPi).
Also, and crucially, all induction principles are universe-polymorphic, so that their usage
does not create global constraints on universes. *)

Section Inductions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

(** ** Embedding *)

(** Reducibility at a lower level implies reducibility at a higher level, and their decoding are the
same. Both need to be proven simultaneously, because of contravariance in the product case. *)

  Fixpoint LR_embedding@{i j k l} {l l'} (l_ : l << l')
    {Γ A B tmeq} (lr : LogRel@{i j k l} l Γ A B tmeq) {struct lr}
    : (LogRel@{i j k l} l' Γ A B tmeq) :=
    let embedPolyAd {Γ A A' B B'} {PA : PolyRedPack Γ A A' B B'} (PAad : PolyRedPackAdequate _ PA) :=
        {|
          PolyRedPack.shpAd (Δ : context) (ρ : Δ ≤ _) (h : [  |- Δ]) :=
            LR_embedding l_ (PAad.(PolyRedPack.shpAd) ρ h) ;
          PolyRedPack.posAd (Δ : context) (a b : term) (ρ : Δ ≤ _) (h : [  |- Δ])
              (ha : [PolyRedPack.shpRed PA ρ h | Δ ||- a ≅ b : _]) :=
            LR_embedding l_ (PAad.(PolyRedPack.posAd) ρ h ha)
        |}
    in
    match lr with
    | LRU _ H =>
        match
          (match l_ with Oi => fun H' => elim H'.(URedTy.lt) end H)
        with end
    | LRne _ neA => LRne _ neA
    | LRPi _ ΠA ΠAad => LRPi _ ΠA (embedPolyAd ΠAad)
    | LRNat _ NA => LRNat _ NA
    | LREmpty _ NA => LREmpty _ NA
    | LRSig _ PA PAad => LRSig _ PA (embedPolyAd PAad)
    | LRId _ IA IAad =>
      let embedIdAd :=
        {| IdRedTyPack.tyAd := LR_embedding l_ IAad.(IdRedTyPack.tyAd) ;
          (* IdRedTyPack.tyKripkeAd (Δ : context) (ρ : Δ ≤ _) (wfΔ : [  |- Δ]) :=
            LR_embedding l_ (IAad.(IdRedTyPack.tyKripkeAd) ρ wfΔ) *)
             |}
      in LRId _ IA embedIdAd
    end.

  (** A basic induction principle, that handles only the first point in the list above *)

  Notation PolyHyp P Γ ΠA HAad G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (HAad.(PolyRedPack.shpAd) ρ h)) ->
      (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
        (ha : [ ΠA.(PolyRedPack.shpRed) ρ h | Δ ||- a ≅ b: _ ]),
        P (HAad.(PolyRedPack.posAd) ρ h ha)) -> G).

  Theorem LR_rect@{i j k o}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {Γ A B tmeq}, LR@{i j k} rec Γ A B tmeq  -> Type@{o}) :

    (forall (Γ : context) A B (h : [Γ ||-U<l> A ≅ B]),
      P (LRU rec h)) ->

    (forall (Γ : context) (A B : term) (neA : [Γ ||-ne A ≅ B]),
      P (LRne rec neA)) ->

    (forall (Γ : context) (A B : term) (ΠA : PiRedTyPack@{j} Γ A B) (HAad : PiRedTyAdequate (LR rec) ΠA),
      PolyHyp P Γ ΠA HAad (P (LRPi rec ΠA HAad))) ->

    (forall Γ A B (NA : [Γ ||-Nat A ≅ B]), P (LRNat rec NA)) ->

    (forall Γ A B (NA : [Γ ||-Empty A ≅ B]), P (LREmpty rec NA)) ->

    (forall (Γ : context) (A B : term) (ΠA : SigRedTyPack@{j} Γ A B) (HAad : SigRedTyAdequate (LR rec) ΠA),
      PolyHyp P Γ ΠA HAad (P (LRSig rec ΠA HAad))) ->

    (forall Γ A B (IA : IdRedTyPack@{j} Γ A B) (IAad : IdRedTyAdequate (LR rec) IA),
      P IAad.(IdRedTyPack.tyAd) ->
      (* (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IAad.(IdRedTyPack.tyKripkeAd) ρ wfΔ)) -> *)
      P (LRId rec IA IAad)) ->

    forall (Γ : context) (A B : term) (tmeq  : term -> term -> Type@{j}) (lr : LR@{i j k} rec Γ A B tmeq),
      P lr.
  Proof.
    cbn.
    intros HU Hne HPi HNat HEmpty HSig HId.
    fix HRec 5.
    destruct lr.
    - eapply HU.
    - eapply Hne.
    - eapply HPi.
      all: intros ; eapply HRec.
    - eapply HNat.
    - eapply HEmpty.
    - eapply HSig.
      all: intros; eapply HRec.
    - eapply HId; intros; eapply HRec.
  Defined.

  Definition LR_rec@{i j k} := LR_rect@{i j k Set}.

  Notation PolyHypLogRel P Γ ΠA G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PolyRed.shpRed) ρ h).(LRAd.adequate)) ->
    (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ Δ ||-< _ > a ≅ b : _ |  ΠA.(PolyRed.shpRed) ρ h ]),
      P (ΠA.(PolyRed.posRed) ρ h ha).(LRAd.adequate)) -> G).

  (** Induction principle specialized to LogRel as the reducibility relation on lower levels *)
  Theorem LR_rect_LogRelRec@{i j k l o}
    (P : forall {l Γ A B tmeq}, LogRel@{i j k l} l Γ A B tmeq -> Type@{o}) :

    (forall l (Γ : context) A B (h : [Γ ||-U<l> A ≅ B]),
      P (LRU (LogRelRec l) h)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (neA : [Γ ||-ne A ≅ B]),
      P (LRne (LogRelRec l) neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : PiRedTy@{i j k l} Γ l A B),
      PolyHypLogRel P Γ ΠA (P (LRPi' ΠA).(LRAd.adequate ))) ->

    (forall l Γ A B (NA : [Γ ||-Nat A ≅ B]), P (LRNat (LogRelRec l) NA)) ->

    (forall l Γ A B (NA : [Γ ||-Empty A ≅ B]), P (LREmpty (LogRelRec l) NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : SigRedTy@{i j k l} Γ l A B),
      PolyHypLogRel P Γ ΠA (P (LRSig' ΠA).(LRAd.adequate ))) ->

    (forall l Γ A B (IA :  [Γ ||-Id<l> A ≅ B]),
      P (IA.(IdRedTy.tyRed).(LRAd.adequate)) ->
      (* (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IA.(IdRedTy.tyKripke) ρ wfΔ).(LRAd.adequate)) -> *)

      P (LRId' IA).(LRAd.adequate)) ->

    forall (l : TypeLevel) (Γ : context) (A B : term) (tmeq  : term -> term -> Type@{k})
      (lr : LR@{j k l} (LogRelRec@{i j k} l) Γ A B tmeq),
      P lr.
  Proof.
    intros ?? HPi ?? HSig HId **; eapply LR_rect@{j k l o}.
    1,2,4,5: auto.
    - intros; eapply (HPi _ _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HSig _ _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HId _ _ _ _ (IdRedTy.from IAad)) ; eauto.
  Defined.

  Notation PolyHypTyUr P Γ ΠA G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PolyRed.shpRed) ρ h)) ->
    (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ ΠA.(PolyRed.shpRed) ρ h | Δ ||- a ≅ b : _ ]),
      P (ΠA.(PolyRed.posRed) ρ h ha)) -> G).

  Theorem LR_rect_TyUr@{i j k l o}
    (P : forall {l Γ A B}, [LogRel@{i j k l} l | Γ ||- A ≅ B] -> Type@{o}) :

    (forall l (Γ : context) A B (h : [Γ ||-U<l> A ≅ B]),
      P (LRU_ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (neA : [Γ ||-ne A ≅ B]),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : PiRedTy@{i j k l} Γ l A B),
      PolyHypTyUr P Γ ΠA (P (LRPi' ΠA))) ->

    (forall l Γ A B (NA : [Γ ||-Nat A ≅ B]), P (LRNat_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-Empty A ≅ B]), P (LREmpty_ l NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : SigRedTy@{i j k l} Γ l A B),
      PolyHypTyUr P Γ ΠA (P (LRSig' ΠA))) ->

    (forall l Γ A B (IA :  [Γ ||-Id<l> A ≅ B]),
      P (IA.(IdRedTy.tyRed)) ->
      (* (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IA.(IdRedTy.tyKripke) ρ wfΔ)) -> *)
      P (LRId' IA)) ->

    forall (l : TypeLevel) (Γ : context) (A B : term) (lr : [LogRel@{i j k l} l | Γ ||- A ≅ B]),
      P lr.
  Proof.
    intros HU Hne HPi HNat HEmpty HSig HId l Γ A B lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l Γ A B _ lr => P l Γ A B (LRbuild lr))).
    all: auto.
  Defined.

  Theorem LR_case_TyUr@{i j k l o}
    (P : forall {l Γ A B}, [LogRel@{i j k l} l | Γ ||- A ≅ B] -> Type@{o}) :

    (forall l (Γ : context) A B (h : [Γ ||-U<l> A ≅ B]),
      P (LRU_ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (neA : [Γ ||-ne A ≅ B]),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : PiRedTy@{i j k l} Γ l A B),
      P (LRPi' ΠA)) ->

    (forall l Γ A B (NA : [Γ ||-Nat A ≅ B]), P (LRNat_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-Empty A ≅ B]), P (LREmpty_ l NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : SigRedTy@{i j k l} Γ l A B),
      P (LRSig' ΠA)) ->

    (forall l Γ A B (IA :  [Γ ||-Id<l> A ≅ B]),
      P (LRId' IA)) ->

    forall (l : TypeLevel) (Γ : context) (A B : term) (lr : [LogRel@{i j k l} l | Γ ||- A ≅ B]),
      P lr.
  Proof. intros; now apply LR_rect_TyUr. Defined.

  (* Specialized version for level 0, used in the general version

  Theorem LR_rect_TyUr0@{i j k l o} (l:=zero)
    (P : forall {Γ A}, [LogRel@{i j k l} l | Γ ||- A] -> Type@{o}) :

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]), P (LRne_ l neA)) ->

    (forall (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tProd Γ l A),
      PolyHypTyUr P Γ ΠA (P (LRPi' ΠA))) ->

    (forall Γ A (NA : [Γ ||-Nat A]), P (LRNat_ l NA)) ->

    (forall Γ A (NA : [Γ ||-Empty A]), P (LREmpty_ l NA)) ->

    (forall (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tSig Γ l A),
      PolyHypTyUr P Γ ΠA (P (LRSig' ΠA))) ->

    (forall Γ A (IA :  [Γ ||-Id<l> A]),
      P (IA.(IdRedTy.tyRed)) ->
      (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IA.(IdRedTy.tyKripke) ρ wfΔ)) ->
      P (LRId' IA)) ->

    forall (Γ : context) (A : term) (lr : [LogRel@{i j k l} l | Γ ||- A]),
      P lr.
  Proof.
    intros HU Hne HPi HNat HEmpty HSig Γ A lr.
    change _ with (match l as l return [Γ ||-<l> A] -> Type@{o} with zero => P Γ A | one => fun _ => unit end lr).
    generalize l Γ A lr.
    eapply LR_rect_TyUr; intros [] *; constructor + auto.
    exfalso. pose (x := URedTy.lt h). inversion x.
  Defined.

  (* Induction principle with inductive hypothesis for the universe at lower levels *)

  Theorem LR_rect_TyUrGen@{i j k l o}
    (P : forall {l Γ A}, [LogRel@{i j k l} l | Γ ||- A] -> Type@{o}) :

    (forall l (Γ : context) A (h : [Γ ||-U<l> A]),
     (forall X (RX : [Γ ||-< URedTy.level h > X ]), P RX) -> P (LRU_ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tProd Γ l A),
      PolyHypTyUr P Γ ΠA (P (LRPi' ΠA))) ->

    (forall l Γ A (NA : [Γ ||-Nat A]), P (LRNat_ l NA)) ->

    (forall l Γ A (NA : [Γ ||-Empty A]), P (LREmpty_ l NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tSig Γ l A),
      PolyHypTyUr P Γ ΠA (P (LRSig' ΠA))) ->

    (forall l Γ A (IA :  [Γ ||-Id<l> A]),
       P (IA.(IdRedTy.tyRed)) ->
      (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IA.(IdRedTy.tyKripke) ρ wfΔ)) ->
      P (LRId' IA)) ->

    forall (l : TypeLevel) (Γ : context) (A : term) (lr : [LogRel@{i j k l} l | Γ ||- A]),
      P lr.
  Proof.
    intros HU Hne HPi HNat HEmpty HSig HId.
    apply LR_rect_TyUr; tea; intros l Γ A h ; pose proof (x :=URedTy.lt h); inversion x ; subst.
    eapply HU. rewrite <- H0. clear h H0 x. revert Γ. eapply LR_rect_TyUr0; auto.
  Defined. *)

End Inductions.

(* induction lr using LR_rect_TyUr fails with "Cannot recognize the conclusion of an induction scheme" *)
(* the tactic indLR lr expects an identifier lr : [Γ ||-<l> A ≅ B]  and applies the induction principle *)
Ltac indLR lr :=
  match type of lr with
  | [ ?Γ ||-< ?l > ?A ≅ ?B ] =>
    pattern l, Γ, A, B, lr; apply LR_rect_TyUr; clear l Γ A B lr; intros l Γ A B
  end.

Ltac caseLR lr :=
  match type of lr with
  | [ ?Γ ||-< ?l > ?A ≅ ?B ] =>
    pattern l, Γ, A, B, lr; apply LR_case_TyUr; clear l Γ A B lr; intros l Γ A B
  end.

From Equations Require Import Equations.

Derive NoConfusion for term.
Derive Signature for whne.
Derive Signature for isType.

Definition whne_uniq {t} (w1 w2 : whne t) : w1 = w2.
Proof.
  induction w1; depelim w2; f_equal; eauto.
Qed.

Definition isType_uniq {A} (w1 w2 : isType A) : w1 = w2.
Proof.
  destruct w1; depelim w2; try reflexivity; try solve [inv_whne].
  f_equal; now eapply whne_uniq.
Qed.


(** ** Inversion principles *)

Section Inversions.
  Context `{GenericTypingProperties}.

  Definition whredL  {Γ l A B } (lr : [Γ ||-<l> A ≅ B]) : [Γ |- A ↘ ].
  Proof. indLR lr; intros h **; try now refine (whredtyL h).  Defined.

  Definition whredR  {Γ l A B } (lr : [Γ ||-<l> A ≅ B]) : [Γ |- B ↘ ].
  Proof. indLR lr; intros h **; try now refine (whredtyR h). Defined.

  Definition whred_conv  {Γ l A B } (lr : [Γ ||-<l> A ≅ B]) : [Γ |- (whredL lr).(tyred_whnf) ≅ (whredR lr).(tyred_whnf)].
  Proof. indLR lr; intros h **; try now refine (whredty_conv h). Defined.

  Lemma whredL_conv {Γ l A B} (lr : [Γ ||-<l> A ≅ B]) : [Γ |- A ≅ (whredL lr).(tyred_whnf)].
  Proof.
    pose proof (whred_conv lr); destruct (whredL lr); cbn in *.
    eapply convty_exp.
    1: gtyping.
    1: eapply redty_refl; gtyping.
    now eapply lrefl.
  Qed.

  Definition pidom (A : term) :=
    match A with | tProd dom _ => dom | _ => A end.

  Definition picod (A : term) :=
    match A with | tProd _ cod => cod | _ => A end.

  Definition sigdom (A : term) :=
    match A with | tSig dom _ => dom | _ => A end.

  Definition sigcod (A : term) :=
    match A with | tSig _ cod => cod | _ => A end.

  Definition idparam (A : term) :=
    match A with | tId P _ _ => P | _ => A end.

  Definition idlhs (A : term) :=
    match A with | tId _ lhs _ => lhs | _ => A end.

  Definition idrhs (A : term) :=
    match A with | tId _ _ rhs => rhs | _ => A end.

  Definition invLRTyEqL {Γ l A B A'} (lr : [Γ ||-<l> A ≅ B]) (w : isType A') :=
    match w return Type with
    | UnivType => ∑ (h : [Γ ||-U<l> A ≅ B]), lr = LRU_ h
    | ProdType => ∑ (h : [Γ ||-Π<l> A ≅ B]), [× lr = LRPi' h, h.(ParamRedTy.domL) = pidom A' & h.(ParamRedTy.codL) = picod A']
    | NatType => ∑ (h : [Γ ||-Nat A ≅ B]), lr = LRNat_ l h
    | EmptyType => ∑ (h : [Γ ||-Empty A ≅ B]), lr = LREmpty_ l h
    | SigType => ∑ (h : [Γ ||-Σ<l> A ≅ B]), [× lr = LRSig' h, h.(ParamRedTy.domL) = sigdom A' & h.(ParamRedTy.codL) = sigcod A']
    | IdType => ∑ (h : [Γ||-Id<l> A ≅ B]), [× lr = LRId' h, h.(IdRedTy.tyL) = idparam A', h.(IdRedTy.lhsL) = idlhs A' & h.(IdRedTy.rhsL) = idrhs A']
    | NeType _ => ∑ (h : [Γ ||-ne A ≅ B]), lr = LRne_ l h × h.(neRedTy.tyL) = A'
    end.

  Lemma invLREqL {Γ l A B A'} (lr : [Γ ||-<l> A ≅ B]) (r : [A ⤳* A']) (w : isType A') : invLRTyEqL lr w.
  Proof.
    assert (A' = (whredL lr).(tyred_whnf)); subst.
    1: eapply whred_det; try apply isType_whnf; tea; gtyping.
    rewrite (isType_uniq w (whredL lr).(tyred_whnf_isType)).
    clear r w;  indLR lr; cbn; intros ; repeat esplit.
  Qed.

  Definition invLRTyEqR {Γ l A B A'} (lr : [Γ ||-<l> A ≅ B]) (w : isType A') :=
    match w return Type with
    | UnivType => ∑ (h : [Γ ||-U<l> A ≅ B]), lr = LRU_ h
    | ProdType => ∑ (h : [Γ ||-Π<l> A ≅ B]), [× lr = LRPi' h, h.(ParamRedTy.domR) = pidom A' & h.(ParamRedTy.codR) = picod A']
    | NatType => ∑ (h : [Γ ||-Nat A ≅ B]), lr = LRNat_ l h
    | EmptyType => ∑ (h : [Γ ||-Empty A ≅ B]), lr = LREmpty_ l h
    | SigType => ∑ (h : [Γ ||-Σ<l> A ≅ B]), [× lr = LRSig' h, h.(ParamRedTy.domR) = sigdom A' & h.(ParamRedTy.codR) = sigcod A']
    | IdType => ∑ (h : [Γ||-Id<l> A ≅ B]), [× lr = LRId' h, h.(IdRedTy.tyR) = idparam A', h.(IdRedTy.lhsR) = idlhs A' & h.(IdRedTy.rhsR) = idrhs A']
    | NeType _ => ∑ (h : [Γ ||-ne A ≅ B]), lr = LRne_ l h × h.(neRedTy.tyR) = A'
    end.

  Lemma invLREqR {Γ l A B B'} (lr : [Γ ||-<l> A ≅ B]) (r : [B ⤳* B']) (w : isType B') : invLRTyEqR lr w.
  Proof.
    assert (B' = (whredR lr).(tyred_whnf)); subst.
    1: eapply whred_det; try apply isType_whnf; tea; gtyping.
    rewrite (isType_uniq w (whredR lr).(tyred_whnf_isType)).
    clear r w;  indLR lr; cbn; intros ; repeat esplit.
  Qed.

  Lemma invLREqBothL_whred {Γ l lA lB A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (lrA : [Γ ||-<lA> A ≅ A']) (lrB : [Γ ||-<lB> B ≅ B']) :
    invLRTyEqL lrA (whredL RAB).(tyred_whnf_isType) × invLRTyEqL lrB (whredR RAB).(tyred_whnf_isType).
  Proof. split; apply invLREqL; gtyping. Qed.

  Lemma invLREqBothR_whred {Γ l lA lB A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (lrA : [Γ ||-<lA> A' ≅ A]) (lrB : [Γ ||-<lB> B' ≅ B]) :
    invLRTyEqR lrA (whredL RAB).(tyred_whnf_isType) × invLRTyEqR lrB (whredR RAB).(tyred_whnf_isType).
  Proof. split; apply invLREqR; gtyping. Qed.

  Lemma invLREqL_whred {Γ l l' A A' B} (RAA' : [Γ ||-<l'> A ≅ A']) (lr : [Γ ||-<l> A ≅ B]) : invLRTyEqL lr (whredL RAA').(tyred_whnf_isType).
  Proof. apply invLREqL; gtyping. Qed.

  Lemma invLREqL_whred' {Γ l l' A B C} (RAB : [Γ ||-<l> A ≅ B]) (lr : [Γ ||-<l'> B ≅ C]) : invLRTyEqL lr (whredR RAB).(tyred_whnf_isType).
  Proof. apply invLREqL; gtyping. Qed.

  Lemma invLREqR_whred {Γ l l' A B B'} (RBB' : [Γ ||-<l'> B ≅ B']) (lr : [Γ ||-<l> A ≅ B]) : invLRTyEqR lr (whredL RBB').(tyred_whnf_isType).
  Proof. apply invLREqR; gtyping. Qed.


  Definition invLRTy {Γ l A B A'} (lr : [Γ ||-<l> A ≅ B]) (w : isType A') :=
    match w return Type with
    | UnivType => [Γ ||-U<l> A ≅ B]
    | ProdType => [Γ ||-Π<l> A ≅ B]
    | NatType => [Γ ||-Nat A ≅ B]
    | EmptyType => [Γ ||-Empty A ≅ B]
    | SigType => [Γ ||-Σ<l> A ≅ B]
    | IdType => [Γ||-Id<l> A ≅ B]
    | NeType _ => [Γ ||-ne A ≅ B]
    end.


  Lemma invLR {Γ l A B A'} (lr : [Γ ||-<l> A ≅ B]) (r : [A ⤳* A']) (w : isType A') : invLRTy lr w.
  Proof. pose proof (h := invLREqL lr r w); destruct w; exact h.π1. Qed.

   Lemma invLR_whred {Γ l l' A A' B} (RAA' : [Γ ||-<l'> A ≅ A']) (lr : [Γ ||-<l> A ≅ B]) : invLRTy lr (whredL RAA').(tyred_whnf_isType).
  Proof. apply invLR; gtyping. Qed.

  Lemma invLRr {Γ l A B B'} (lr : [Γ ||-<l> A ≅ B]) (r : [B ⤳* B']) (w : isType B') : invLRTy lr w.
  Proof. pose proof (h := invLREqR lr r w); destruct w; exact h.π1. Qed.

  Lemma invLRr_whred {Γ l l' A B B'} (RBB' : [Γ ||-<l'> B ≅ B']) (lr : [Γ ||-<l> A ≅ B]) : invLRTy lr (whredL RBB').(tyred_whnf_isType).
  Proof. apply invLRr; gtyping. Qed.


  Lemma invLRU {Γ l B} : [Γ ||-<l> U ≅ B] -> [Γ ||-U<l> U ≅ B].
  Proof.
    intros.
    now unshelve eapply (invLR _ redIdAlg UnivType).
  Qed.

  Lemma invLRne {Γ l A B} : whne A -> [Γ ||-<l> A ≅ B] -> [Γ ||-ne A ≅ B].
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg (NeType _)).
  Qed.

  Lemma invLRΠ {Γ l dom cod B} : [Γ ||-<l> tProd dom cod ≅ B] -> [Γ ||-Π<l> tProd dom cod ≅ B].
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg ProdType).
  Qed.

  Lemma invLRΣ {Γ l dom cod B} : [Γ ||-<l> tSig dom cod ≅ B] -> [Γ ||-Σ<l> tSig dom cod ≅ B].
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg SigType).
  Qed.

  Lemma invLRId {Γ l A x y B} : [Γ ||-<l> tId A x y ≅ B] -> [Γ ||-Id<l> tId A x y ≅ B].
  Proof.
    intros.
    now unshelve eapply (invLR _ redIdAlg IdType).
  Qed.

  (* invLRNat is useless *)

  Lemma invLRConvU {Γ l A B} : [Γ ||-U<l> A ≅ B] -> [Γ |- A ≅ U].
  Proof. intros []; gen_typing. Qed.

  Lemma invLRConvNe {Γ A B} (RA : [Γ ||-ne A ≅ B]) : [Γ |- A ≅ RA.(neRedTy.tyL)].
  Proof.
    destruct RA; cbn in *.
    eapply convty_exp.
    2: apply redtywf_refl; gen_typing.
    1: gen_typing.
    apply convty_term; apply convtm_convneu.
    1: constructor.
    now eapply lrefl.
  Qed.

  Lemma invLRConvPi {Γ l A B} (RA : [Γ ||-Π<l> A ≅ B]) :  [Γ |- A ≅ PiRedTy.outTy RA].
  Proof.
    destruct RA as [???? []]; cbn in *.
    eapply convty_exp.
    1: gtyping.
    2: now eapply lrefl.
    eapply redty_refl; gtyping.
  Qed.

  Lemma invLRConvSig {Γ l A B} (RA : [Γ ||-Σ<l> A ≅ B]) :  [Γ |- A ≅ SigRedTy.outTy RA].
  Proof.
    destruct RA as [???? []]; cbn in *.
    eapply convty_exp.
    1: gtyping.
    2: now eapply lrefl.
    apply redtywf_refl; gtyping.
  Qed.

  Lemma invLRConvNat {Γ A B} (RA : [Γ ||-Nat A ≅ B]) : [Γ |- A ≅ tNat].
  Proof. destruct RA; eapply convty_exp; gtyping. Qed.

  Lemma invLRConvEmpty {Γ A B} (RA : [Γ ||-Empty A ≅ B]) : [Γ |- A ≅ tEmpty].
  Proof. destruct RA; eapply convty_exp ; gtyping. Qed.

    Arguments IdRedTy.outTy _ /.
  Lemma invLRConvId {Γ l A B} (RA: [Γ ||-Id<l> A ≅ B]) : [Γ |- A ≅ IdRedTy.outTy RA].
  Proof.
    destruct RA; cbn; eapply convty_exp.
    1: gtyping.
    2: now eapply lrefl.
    gtyping.
  Qed.


End Inversions.
