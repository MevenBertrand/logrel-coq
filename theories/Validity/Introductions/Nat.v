From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction  Escape Irrelevance Reflexivity Irrelevance Weakening Neutral Transitivity Reduction EqRedRight.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion SingleSubst Reflexivity Reduction Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.

Section Nat.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma natRed {Γ l} : [|- Γ] -> [Γ ||-<l> tNat].
Proof.
  intros; eapply LRNat_; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma natValid {Γ l} (VΓ : [||-v Γ]) : [Γ ||-v<l> tNat | VΓ].
Proof.
  unshelve econstructor; intros.
  + now eapply natRed.
  + cbn; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma natconvValid {Γ l} (VΓ : [||-v Γ]) (VNat : [Γ ||-v<l> tNat | VΓ]) :
  [Γ ||-v<l> tNat ≅ tNat | VΓ | VNat].
Proof.
  constructor; intros.
  enough [Δ ||-<l> tNat ≅ tNat | natRed wfΔ] by irrelevance.
  constructor; cbn; eapply redtywf_refl; gen_typing.
Qed.

Lemma natURedTm {Δ} (wfΔ : [|-Δ]) : URedTm (LogRelRec one) Δ tNat U (redUOneCtx wfΔ).
Proof.
  exists tNat; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma natTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tNat : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve eexists (natURedTm wfΔ) (natURedTm wfΔ) _; cbn.
  1,3: now eapply (natRed (l:=zero)).
  1: gen_typing.
  apply reflLRTyEq.
Defined.

Lemma natTermValid {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tNat : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply natTermRed.
Qed.

Lemma zeroRed {Γ l} {NN : [Γ ||-Nat tNat]} (wfΓ : [|- Γ]): [Γ ||-<l> tZero : _ | LRNat_ l NN].
Proof.
  exists tZero tZero.
  1-3: gen_typing.
  constructor.
Defined.

Lemma zeroRedEq {Γ l} {NN : [Γ ||-Nat tNat]} (wfΓ : [|- Γ]): [Γ ||-<l> tZero ≅ tZero : _ | LRNat_ l NN].
Proof. now apply zeroRed. Defined.

Lemma zeroValid {Γ l} (VΓ : [||-v Γ]):
  [Γ ||-v<l> tZero : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; unshelve eapply zeroRed; tea.
Qed.

Lemma succRedEq {Γ l n n'} {NN : [Γ ||-Nat tNat]} :
  [Γ ||-<l> n ≅ n' : _ | LRNat_ l NN] ->
  [Γ ||-<l> tSucc n ≅ tSucc n' : _ | LRNat_ l NN].
Proof.
  intros h; pose proof (h' :=h); inversion h'; subst.
  escape; exists (tSucc n) (tSucc n').
  1,2: eapply redtmwf_refl; eapply ty_succ; gen_typing.
  + eapply convtm_succ; eapply convtm_exp; gen_typing.
  + now constructor.
Defined.

Lemma succRed {Γ l n} {NN : [Γ ||-Nat tNat]} :
  [Γ ||-<l> n : _ | LRNat_ l NN] ->
  [Γ ||-<l> tSucc n : _ | LRNat_ l NN].
Proof. eapply succRedEq. Defined.


Lemma succRedInv {Γ l n m } {NN : [Γ ||-Nat tNat]} :
  [Γ ||-<l> tSucc n ≅ tSucc m : _ | LRNat_ l NN] ->
  [Γ ||-<l> n ≅ m : _ | LRNat_ l NN].
Proof.
  intros RSn; inversion RSn; subst.
  unshelve epose proof (redtmwf_whnf redL _); try constructor.
  unshelve epose proof (redtmwf_whnf redR _); try constructor.
  subst. inversion prop; subst; tea.
  match goal with H : [ _ ||-NeNf _ ≅ _ : _] |- _ => destruct H as [?? refl] end.
  apply convneu_whne in refl; inv_whne.
Qed.


Lemma succcongValid {Γ l n n'} (VΓ : [||-v Γ])
  (Veqn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; instValid Vσσ'; now unshelve eapply succRedEq.
Qed.

Lemma succValid {Γ l n} (VΓ : [||-v Γ])
  (Vn : [Γ ||-v<l> n : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tSucc n : tNat | VΓ | natValid VΓ].
Proof. now eapply lreflValidTm, succcongValid, reflValidTm. Qed.

Lemma elimSuccHypTy_subst {P} σ :
  elimSuccHypTy P[up_term_term σ] = (elimSuccHypTy P)[σ].
Proof.
  unfold elimSuccHypTy.
  cbn. rewrite shift_up_eq.
  rewrite liftSubstComm. cbn.
  now rewrite up_liftSubst_eq.
Qed.

Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Section NatElimRedEq.
  Context {Γ l P Q hs hs' hz hz'}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Nat tNat])
    (RN := LRNat_ _ NN)
    (RP : [Γ,, tNat ||-<l> P])
    (RQ : [Γ,, tNat ||-<l> Q])
    (eqPQ : [Γ,, tNat |- P ≅ Q])
    (RPpt : forall n n', [Γ ||-<l> n ≅ n' : _ | RN] -> [Γ ||-<l> P[n..]])
    (* (RQpt : forall n n', [Γ ||-<l> n ≅ n': _ | RN] -> [Γ ||-<l> Q[n..]]) *)
    (RPQext : forall n n' (Rn : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ Q[n'..] | RPpt _ _ Rn])
    (RPz := RPpt _ _ (zeroRed wfΓ))
    (RPQz := RPQext _ _ (zeroRedEq wfΓ))
    (Rhz : [Γ ||-<l> hz ≅ hz' : _ | RPz])
    (RPs : [Γ ||-<l> elimSuccHypTy P])
    (RQs : [Γ ||-<l> elimSuccHypTy Q])
    (RPQs : [Γ ||-<l> elimSuccHypTy P ≅ elimSuccHypTy Q | RPs])
    (Rhs : [Γ ||-<l> hs ≅ hs' : _ | RPs ])
    .

  #[local]
  Lemma RQpt : forall n n', [Γ ||-<l> n ≅ n': _ | RN] -> [Γ ||-<l> Q[n..]].
  Proof. intros; now unshelve eapply LRTyEqRedRight, RPQext. Qed.

  Let RQz := RQpt _ _ (zeroRed wfΓ).

  #[local]
  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ _ Rn].
  Proof.
    intros; eapply transEq; [| eapply LRTyEqSym ].
    all: unshelve (eapply RPQext; cycle 1; tea); now eapply urefl.
    Unshelve. 2: eapply RQpt; now symmetry.
  Qed.

  Lemma natElimRedEqAux :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]), [Γ ||-<l> n ≅ n' : _ | RN] ->
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ _ Rnn' ]) ×
    (forall n n' (Rnn' : NatPropEq NN n n') (RP : [Γ ||-<l> P[n..]]),
    (* (Rn : [Γ ||-<l> n ≅ n' : _ | RN]), *)
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RP (*RPpt _ _ Rn*) ]).
  Proof.
    apply NatRedEqInduction.
    - intros ?? nfL nfR redL redR ? prop ih Rtu ; destruct (NatPropEq_whnf prop).
      eapply redSubstTmEq.
      + eapply LRTmEqConv, ih; unshelve eapply RPext.
        eapply redTmEqFwd; tea; now eapply lrefl.
      + escape; eapply redtm_natelim; tea; gen_typing.
      + escape; eapply redtm_natelim; tea; [..| gen_typing].
        1,2: now eapply ty_conv.
      + now unshelve eapply escapeEq, RPQext.
    - intros. eapply redSubstTmEq.
      + irrelevanceRefl; eapply Rhz.
      + escape; eapply redtm_natElimZero; tea.
      + escape; eapply redtm_natElimZero; tea.
        1,2: now eapply ty_conv.
      + now escape.
    - intros n n' Rn ih ?; change [Γ ||-<l> n ≅ n' : _ | RN] in Rn.
      eapply redSubstTmEq; cycle 1.
      + escape; eapply redtm_natElimSucc; tea.
      + escape; eapply redtm_natElimSucc; tea.
        1,2: now eapply ty_conv.
      + unshelve eapply escapeEq, RPQext.
        now eapply succRedEq.
      + assert [Γ ||-<l> arr P[n..] P[(tSucc n)..]].
        1: now (eapply ArrRedTy; eapply RPpt; [| eapply succRedEq]).
        unshelve eapply simple_appcongTerm; [..| eauto]; tea.
        unshelve (irrelevance0; [| eapply appcongTerm; tea]).
        all: now rewrite subst_arr, liftSubst_singleSubst_eq.
    - intros n n' Rn RP0.
      pose proof (neNfTermEq RN Rn).
      eapply neuTermEq. 2: eapply ty_conv ; [| eapply escapeEq; eapply LRTyEqSym].
      + escape; now eapply ty_natElim.
      + escape; eapply ty_natElim; tea.
        all: now eapply ty_conv.
      + now unshelve eapply RPQext.
      + escape ; destruct Rn; now eapply convneu_natElim.
      Unshelve. 2: eapply RQpt; now eapply urefl.
  Qed.

  Lemma natElimRedEq :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ _ Rnn' ]).
  Proof. intros; now apply (fst natElimRedEqAux). Qed.
End NatElimRedEq.


Section NatElimValid.
  Context {Γ l}
    (VΓ : [||-v Γ])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN).

  Lemma elimSuccHypTyValid {P}
    (VP : [Γ ,, tNat ||-v<l> P | VΓN]) :
    [Γ ||-v<l> elimSuccHypTy P | VΓ].
  Proof.
    unfold elimSuccHypTy.
    unshelve eapply PiValid.
    1: exact VN.
    eapply simpleArrValid; tea.
    eapply substLiftS; tea.
    eapply irrelevanceTm.
    eapply succValid.
    eapply irrelevanceTm.
    change tNat with tNat⟨@wk1 Γ tNat⟩ at 2.
    eapply var0Valid.
    Unshelve. all: tea.
  Defined.

  Lemma elimSuccHypTyCongValid {P P'}
      (VP : [Γ ,, tNat ||-v<l> P | VΓN])
      (VeqP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN | VP ]) :
      [Γ ||-v<l> elimSuccHypTy P ≅ elimSuccHypTy P' | VΓ | elimSuccHypTyValid VP].
  Proof.
    unfold elimSuccHypTy.  pose proof (ureflValidTy VeqP).
    eapply irrelevanceTyEq.
    assert [Γ,, tNat ||-v< l > P'[tSucc (tRel 0)]⇑ | validSnoc VΓ VN]. 1:{
      eapply substLiftS; tea.
      eapply irrelevanceTm.
      eapply succValid.
      eapply irrelevanceTm.
      change tNat with tNat⟨@wk1 Γ tNat⟩ at 2.
      eapply var0Valid.
    }
    eapply PiCong.
    - eapply simpleArrValid; tea.
    - eapply reflValidTy.
    - eapply simpleArrCongValid; tea.
      eapply substLiftSEq; tea.
    Unshelve. all: tea.
    unshelve eapply irrelevanceTm; tea.
    2: eapply succValid.
    unshelve eapply irrelevanceTm'; cycle -1.
    1: unshelve eapply var0Valid.
    1,2 : tea.
    now bsimpl.
  Qed.



  Context { P P' hz hz' hs hs'}
    (VP : [Γ ,, tNat ||-v<l> P | VΓN])
    (VPP' : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN | VP ])
    (VP' := ureflValidTy VPP')
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VP]).

  (* Lemma elimSuccHypTyCongValid ? *)

  Lemma natElimCongValid {n n'}
    (Vn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : _ | VΓ | VPn].
  Proof.
    pose proof (elimSuccHypTyValid VP).
    pose proof (elimSuccHypTyValid VP').
    pose proof (elimSuccHypTyCongValid VP VPP').
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubstEq' VN Vσσ').
    instValid Vuσ; cbn -[elimSuccHypTy elimSuccHypTyValid] in *; escape.
    irrelevance0. 1: now rewrite singleSubstComm'.
    eapply natElimRedEq; rewrite ?elimSuccHypTy_subst; tea.
    + intros; irrelevance0; rewrite up_single_subst; [reflexivity|].
      unshelve eapply validTyEq; cycle 1 ; tea.
      now unshelve eapply consSubstEq.
    + irrelevance0; [exact (singleSubstComm' _ tZero σ)|]; tea.
    + irrelevance0; [now rewrite elimSuccHypTy_subst|]; tea.
    + irrelevance0; [now rewrite elimSuccHypTy_subst|]; tea.
    Unshelve.
      2,3: tea.
      2: now rewrite elimSuccHypTy_subst.
      intros ?? Rn; rewrite up_single_subst.
      unshelve eapply validTy.
      5: tea.
      3: unshelve eapply consSubstEq; tea.
  Qed.
End NatElimValid.

Lemma natElimValid {Γ l P hz hz' hs hs' n n'}
    (VΓ : [||-v Γ])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN])
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VΓ VP])
    (Vn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn):
    [Γ ||-v<l> tNatElim P hz hs n : _ | VΓ | VPn].
Proof.
  eapply lreflValidTm , natElimCongValid; tea.
  now eapply reflValidTy.
Qed.

Section NatElimRedValid.
  Context {Γ l}
    (VΓ : [||-v Γ])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    { P P' hz hz' hs hs'}
    (VP : [Γ ,, tNat ||-v<l> P | VΓN])
    (VPP' : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN | VP ])
    (VP' := ureflValidTy VPP')
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VΓ VP]).

  Lemma natElimZeroValid  :
    [Γ ||-v<l> tNatElim P hz hs tZero ≅ hz : _ | VΓ | VPz].
  Proof.
    eapply redSubstValid. 2: now eapply lreflValidTm.
    constructor; intros; cbn; rewrite singleSubstComm'.
    instValid Vσσ'; instValid (liftSubstEq' VN Vσσ'); escape.
    eapply redtm_natElimZero; tea.
    + now rewrite <- (singleSubstComm' _ tZero σ).
    + now rewrite elimSuccHypTy_subst.
  Qed.

  Lemma natElimSuccValid {n}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN])
    (VPSn := substS VP (succValid _ Vn)) :
    [Γ ||-v<l> tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : _ | VΓ | VPSn].
  Proof.
    eapply redSubstValid.
    * constructor; intros; rewrite singleSubstComm'.
      instValid Vσσ'; instValid (liftSubstEq' VN Vσσ'); escape.
      eapply redtm_natElimSucc; tea; refold.
      + now rewrite <- (singleSubstComm' _ tZero σ).
      + now rewrite elimSuccHypTy_subst.
    * eapply simple_appValid.
      2: now unshelve (eapply natElimValid; tea).
      eapply irrelevanceTm'; [| exact (appValid (lreflValidTm _ Vhs) Vn)].
      clear; now bsimpl.
      Unshelve.
        eapply simpleArrValid; eapply substS; tea.
        now eapply succValid.
  Qed.

End NatElimRedValid.

End Nat.
