(** * LogRel.LogicalRelation.Induction: good induction principles for the logical relation. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
GenericTyping LogicalRelation.

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
    {Γ A rEq rTeEq} (lr : LogRel@{i j k l} l Γ A rEq rTeEq) {struct lr}
    : (LogRel@{i j k l} l' Γ A rEq rTeEq) :=
    let embedPolyAd {Γ A B} {PA : PolyRedPack Γ A B} (PAad : PolyRedPackAdequate _ PA) :=
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
          IdRedTyPack.tyKripkeAd (Δ : context) (ρ : Δ ≤ _) (wfΔ : [  |- Δ]) :=
            LR_embedding l_ (IAad.(IdRedTyPack.tyKripkeAd) ρ wfΔ) |}
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
    (P : forall {c t rEq rTeEq},
      LR@{i j k} rec c t rEq rTeEq  -> Type@{o}) :

    (forall (Γ : context) A (h : [Γ ||-U<l> A]),
      P (LRU rec h)) ->

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne rec neA)) ->

    (forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
      PolyHyp P Γ ΠA HAad (P (LRPi rec ΠA HAad))) ->

    (forall Γ A (NA : [Γ ||-Nat A]), P (LRNat rec NA)) ->

    (forall Γ A (NA : [Γ ||-Empty A]), P (LREmpty rec NA)) ->

    (forall (Γ : context) (A : term) (ΠA : SigRedTy@{j} Γ A) (HAad : SigRedTyAdequate (LR rec) ΠA),
      PolyHyp P Γ ΠA HAad (P (LRSig rec ΠA HAad))) ->

    (forall Γ A (IA : IdRedTyPack@{j} Γ A) (IAad : IdRedTyAdequate (LR rec) IA),
      P IAad.(IdRedTyPack.tyAd) ->
      (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IAad.(IdRedTyPack.tyKripkeAd) ρ wfΔ)) ->
      P (LRId rec IA IAad)) ->

    forall (Γ : context) (t : term) (rEq : term -> Type@{j})
      (rTeEq  : term -> term -> Type@{j}) (lr : LR@{i j k} rec Γ t rEq rTeEq),
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
      (ha : [ Δ ||-< _ > a ≅ b : ΠA.(ParamRedTy.dom)⟨ρ⟩ |  ΠA.(PolyRed.shpRed) ρ h ]),
      P (ΠA.(PolyRed.posRed) ρ h ha).(LRAd.adequate)) -> G).

  (** Induction principle specialized to LogRel as the reducibility relation on lower levels *)
  Theorem LR_rect_LogRelRec@{i j k l o}
    (P : forall {l Γ t rEq rTeEq},
    LogRel@{i j k l} l Γ t rEq rTeEq -> Type@{o}) :

    (forall l (Γ : context) A (h : [Γ ||-U<l> A]),
      P (LRU (LogRelRec l) h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne (LogRelRec l) neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tProd Γ l A),
      PolyHypLogRel P Γ ΠA (P (LRPi' ΠA).(LRAd.adequate ))) ->

    (forall l Γ A (NA : [Γ ||-Nat A]), P (LRNat (LogRelRec l) NA)) ->

    (forall l Γ A (NA : [Γ ||-Empty A]), P (LREmpty (LogRelRec l) NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tSig Γ l A),
      PolyHypLogRel P Γ ΠA (P (LRSig' ΠA).(LRAd.adequate ))) ->

    (forall l Γ A (IA :  [Γ ||-Id<l> A]),
      P (IA.(IdRedTy.tyRed).(LRAd.adequate)) ->
      (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IA.(IdRedTy.tyKripke) ρ wfΔ).(LRAd.adequate)) ->

      P (LRId' IA).(LRAd.adequate)) ->

    forall (l : TypeLevel) (Γ : context) (t : term) (rEq : term -> Type@{k})
      (rTeEq  : term -> term -> Type@{k}) (lr : LR@{j k l} (LogRelRec@{i j k} l) Γ t rEq rTeEq),
      P lr.
  Proof.
    intros ?? HPi ?? HSig HId **; eapply LR_rect@{j k l o}.
    1,2,4,5: auto.
    - intros; eapply (HPi _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HSig _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HId _ _ _ (IdRedTy.from IAad)) ; eauto.
  Defined.

  Notation PolyHypTyUr P Γ ΠA G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PolyRed.shpRed) ρ h)) ->
    (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ ΠA.(PolyRed.shpRed) ρ h | Δ ||- a ≅ b : ΠA.(ParamRedTy.dom)⟨ρ⟩ ]),
      P (ΠA.(PolyRed.posRed) ρ h ha)) -> G).

  Theorem LR_rect_TyUr@{i j k l o}
    (P : forall {l Γ A}, [LogRel@{i j k l} l | Γ ||- A] -> Type@{o}) :

    (forall l (Γ : context) A (h : [Γ ||-U<l> A]),
      P (LRU_ h)) ->

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
    intros HU Hne HPi HNat HEmpty HSig HId l Γ A lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l Γ A _ _ lr => P l Γ A (LRbuild lr))).
    all: auto.
  Defined.

  (* Specialized version for level 0, used in the general version *)

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
  Defined.

End Inductions.

(** ** Inversion principles *)

Section Inversions.
  Context `{GenericTypingProperties}.

  Definition invLRTy {Γ l A A'} (lr : [Γ ||-<l> A]) (r : [A ⤳* A']) (w : isType A') :=
    match w return Type with
    | UnivType => [Γ ||-U<l> A]
    | ProdType => [Γ ||-Π<l> A]
    | NatType => [Γ ||-Nat A]
    | EmptyType => [Γ ||-Empty A]
    | SigType => [Γ ||-Σ<l> A]
    | IdType => [Γ||-Id<l> A]
    | NeType _ => [Γ ||-ne A]
    end.

  Lemma invLR {Γ l A A'} (lr : [Γ ||-<l> A]) (r : [A ⤳* A']) (w : isType A') : invLRTy lr r w.
  Proof.
    unfold invLRTy.
    revert A' r w.
    pattern l, Γ, A, lr ; eapply LR_rect_TyUr; clear l Γ A lr.
    - intros * h ? red whA.
      assert (A' = U) as ->.
      {
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, h.
      }
      dependent inversion whA.
      1: assumption.
      exfalso.
      gen_typing.
    - intros * ? A' red whA.
      enough ({w' & whA = NeType w'}) as [? ->] by easy.
      destruct neA as [A'' redA neA''].
      apply convneu_whne in neA''.
      assert (A' = A'') as <-.
      + eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
      + dependent inversion whA ; subst.
        all: inv_whne.
        all: now eexists.
    - intros ??? PiA _ _ A' red whA.
      enough (∑ dom cod, A' = tProd cod dom) as (?&?&->).
      + dependent inversion whA ; subst.
        2: exfalso ; gen_typing.
        assumption.
      + destruct PiA as [?? redA].
        do 2 eexists.
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
    - intros ??? [redA] ???.
      enough (A' = tNat) as ->.
      + dependent inversion w.
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
    - intros ??? [redA] ???.
      enough (A' = tEmpty) as ->.
      + dependent inversion w.
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
    - intros ??? PA _ _ A' red whA.
      enough (∑ dom cod, A' = tSig cod dom) as (?&?&->).
      + dependent inversion whA ; subst.
        2: inv_whne.
        assumption.
      + destruct PA as [?? redA].
        do 2 eexists.
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
    - intros ??? IA _ _ A' red whA'.
      enough (∑ B x y, A' = tId B x y) as [?[?[? ->]]].
      + dependent inversion whA'; tea; inv_whne.
      + destruct IA; do 3 eexists; eapply whred_det.
        1-3: gen_typing.
        now eapply redtywf_red.
  Qed.

  Lemma invLRU {Γ l} : [Γ ||-<l> U] -> [Γ ||-U<l> U].
  Proof.
    intros.
    now unshelve eapply (invLR _ redIdAlg UnivType).
  Qed.

  Lemma invLRne {Γ l A} : whne A -> [Γ ||-<l> A] -> [Γ ||-ne A].
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg (NeType _)).
  Qed.

  Lemma invLRΠ {Γ l dom cod} : [Γ ||-<l> tProd dom cod] -> [Γ ||-Π<l> tProd dom cod].
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg ProdType).
  Qed.

  Lemma invLRΣ {Γ l dom cod} : [Γ ||-<l> tSig dom cod] -> [Γ ||-Σ<l> tSig dom cod].
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg SigType).
  Qed.

  Lemma invLRId {Γ l A x y} : [Γ ||-<l> tId A x y] -> [Γ ||-Id<l> tId A x y].
  Proof.
    intros.
    now unshelve eapply (invLR _ redIdAlg IdType).
  Qed.

  (* invLRNat is useless *)

  Lemma invLRConvU {Γ l A} : [Γ ||-U<l> A] -> [Γ |- A ≅ U].
  Proof. intros []; gen_typing. Qed.

  Lemma invLRConvNe {Γ A} (RA : [Γ ||-ne A]) : [Γ |- A ≅ RA.(neRedTy.ty)].
  Proof.
    destruct RA; cbn in *.
    eapply convty_exp.
    2: apply redtywf_refl; gen_typing.
    1: gen_typing.
    apply convty_term; apply convtm_convneu.
    all: gen_typing.
  Qed.

  Lemma invLRConvPi {Γ l A} (RA : [Γ ||-Π<l> A]) :  [Γ |- A ≅ RA.(PiRedTy.outTy)].
  Proof.
    destruct RA as [?? []]. cbn in *.
    eapply convty_exp; tea.
    now apply redtywf_refl.
  Qed.

  Lemma invLRConvSig {Γ l A} (RA : [Γ ||-Σ<l> A]) :  [Γ |- A ≅ RA.(SigRedTy.outTy)].
  Proof.
    destruct RA as [?? []]. cbn in *.
    eapply convty_exp; tea.
    now apply redtywf_refl.
  Qed.

  Lemma invLRConvNat {Γ A} (RA : [Γ ||-Nat A]) : [Γ |- A ≅ tNat].
  Proof. destruct RA; gen_typing. Qed.

  Lemma invLRConvEmpty {Γ A} (RA : [Γ ||-Empty A]) : [Γ |- A ≅ tEmpty].
  Proof. destruct RA; gen_typing. Qed.

  Lemma invLRConvId {Γ l A} (RA: [Γ ||-Id<l> A]) : [Γ |- A ≅ RA.(IdRedTy.outTy)].
  Proof. destruct RA; unfold IdRedTy.outTy; cbn; gen_typing. Qed.

End Inversions.
