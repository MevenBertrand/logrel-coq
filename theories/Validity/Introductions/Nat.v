From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Nat.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma natRedTy {Γ} : [|- Γ] -> [Γ ||-Nat tNat ≅ tNat].
Proof.
  constructor; eapply redtywf_refl; gen_typing.
Qed.

Definition natRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-<l> tNat] :=
  LRNat_ l (natRedTy wfΓ).

Lemma natValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tNat | VΓ].
Proof.
  unshelve econstructor; intros; now eapply natRed.
Defined.

Lemma natURedTm {Δ} (wfΔ : [|-Δ]) : URedTm zero Δ tNat.
Proof.
  exists tNat; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma natTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tNat : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve econstructor; try now eapply natURedTm.
  1: cbn; gtyping.
  eapply redTyRecBwd; now eapply natRed.
Defined.

Lemma natTermValid {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tNat : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply natTermRed.
Qed.

Lemma zeroRed {Γ l A B} {NN : [Γ ||-Nat A ≅ B]} : [Γ ||-<l> tZero : _ | LRNat_ l NN].
Proof.
  assert [|-Γ] by (pose (LRNat_ l NN); escape; gtyping).
  exists tZero tZero.
  1-3: gtyping.
  constructor.
Defined.

Lemma zeroValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']):
  [Γ ||-v<l> tZero : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; unshelve eapply zeroRed; tea.
  3: now eapply natRedTy.
Qed.

Lemma succRed {Γ l A A' n n'} {NN : [Γ ||-Nat A ≅ A']} :
  [Γ ||-<l> n ≅ n' : _ | LRNat_ l NN] ->
  [Γ ||-<l> tSucc n ≅ tSucc n' : _ | LRNat_ l NN].
Proof.
  intros h; pose proof (h' :=h); inversion h'; subst.
  escape; exists (tSucc n) (tSucc n').
  1,2: eapply redtmwf_refl; eapply ty_succ; gen_typing.
  + eapply convtm_succ; eapply convtm_exp; gen_typing.
  + now constructor.
Defined.

(* Lemma succRed {Γ A A' l n} {NN : [Γ ||-Nat A ≅ A']} :
  [Γ ||-<l> n : _ | LRNat_ l NN] ->
  [Γ ||-<l> tSucc n : _ | LRNat_ l NN].
Proof. eapply succRedEq. Defined. *)


(* Lemma succRedInv {Γ l n m } {NN : [Γ ||-Nat tNat]} :
  [Γ ||-<l> tSucc n ≅ tSucc m : _ | LRNat_ l NN] ->
  [Γ ||-<l> n ≅ m : _ | LRNat_ l NN].
Proof.
  intros RSn; inversion RSn; subst.
  unshelve epose proof (redtmwf_whnf redL _); try constructor.
  unshelve epose proof (redtmwf_whnf redR _); try constructor.
  subst. inversion prop; subst; tea.
  match goal with H : [ _ ||-NeNf _ ≅ _ : _] |- _ => destruct H as [?? refl] end.
  apply convneu_whne in refl; inv_whne.
Qed. *)


Lemma succValid' {Γ Γ' A A' l n n'} (VΓ : [||-v Γ ≅ Γ'])
  (VN : [Γ ||-v<l> A ≅ A' | VΓ])
  (eqA : A = tNat)
  (Veqn : [Γ ||-v<l> n ≅ n' : A | VΓ | VN]) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : A | VΓ | VN].
Proof.
  subst.
  constructor; intros; cbn; instValid Vσσ'; eapply irrLR.
  unshelve eapply succRed, irrLR; cycle 4; tea; cbn; eapply natRedTy; tea.
  Unshelve. tea.
Qed.

Lemma succValid {Γ Γ' l n n'} (VΓ : [||-v Γ ≅ Γ'])
  (Veqn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; instValid Vσσ'.
  unshelve eapply succRed; cycle 3; first [eapply natRedTy| tea].
Qed.

Lemma elimSuccHypTy_subst {P} σ :
  elimSuccHypTy P[up_term_term σ] = (elimSuccHypTy P)[σ].
Proof.
  unfold elimSuccHypTy.
  cbn. rewrite shift_up_eq.
  erewrite liftSubstComm.
  rewrite up_liftSubst_eq.
  now rewrite wk1_ren.
  Unshelve. all: tea; constructor.
Qed.

Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Section NatElimRedEq.
  Context {Γ l P Q hs hs' hz hz'}
    (* (wfΓ : [|- Γ]) *)
    (NN : [Γ ||-Nat tNat ≅ tNat])
    (RN := LRNat_ _ NN)
    (* (RP : [Γ,, tNat ||-<l> P])
    (RQ : [Γ,, tNat ||-<l> Q]) *)
    (WtP : [Γ ,, tNat |- P])
    (WtQ : [Γ ,, tNat |- Q])
    (eqPQ : [Γ,, tNat |- P ≅ Q])
    (RPQext : forall n n' (Rn : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ Q[n'..]])
    (RPQz := RPQext _ _ zeroRed)
    (Rhz : [Γ ||-<l> hz ≅ hz' : _ | RPQz])
    (RPQs : [Γ ||-<l> elimSuccHypTy P ≅ elimSuccHypTy Q])
    (Rhs : [Γ ||-<l> hs ≅ hs' : _ | RPQs ]) .

  #[local]
  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ P[n'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.

  Lemma natElimRedEqAux :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPQext _ _ Rnn' ]) ×
    (forall n n' (Rnn' : NatPropEq Γ n n') (RP : [Γ ||-<l> P[n..] ≅ Q[n'..]]),
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RP ]).
  Proof.
    apply NatRedEqInduction.
    - intros t u  nfL nfR redL redR ? prop ih.
      set (Rtu := Build_NatRedTmEq _ _ _ _ _ _ : [Γ ||-<l> t ≅ u : _ | RN]).
      pose proof (redTmFwd' Rtu) as []; eapply redSubstTmEq.
      + unshelve eapply irrLRConv, ih;
        first [eapply RPQext| eapply RPext]; tea; now symmetry.
      + escape; eapply redtm_natelim; tea; gen_typing.
      + escape; eapply redtm_natelim; tea; [..| gtyping].
        1,2: now eapply ty_conv.
    - intros; eapply redSubstTmEq.
      + eapply irrLR, Rhz.
      + escape; eapply redtm_natElimZero; tea.
      + escape; eapply redtm_natElimZero; tea.
        1,2: now eapply ty_conv.
    - intros n n' Rn ih ?; change [Γ ||-<l> n ≅ n' : _ | RN] in Rn.
      eapply redSubstTmEq; cycle 1.
      + escape; eapply redtm_natElimSucc; tea.
      + escape; eapply redtm_natElimSucc; tea.
        1,2: now eapply ty_conv.
      + assert [Γ ||-<l> arr P[n..] P[(tSucc n)..] ≅ arr Q[n'..] Q[(tSucc n')..]].
        1: now eapply ArrRedTy; eapply RPQext;[|eapply succRed].
        unshelve eapply simple_appcongTerm; [..| eauto]; tea.
        unshelve (eapply irrLREq, appcongTerm; tea; now rewrite subst_arr, liftSubst_singleSubst_eq).
        now rewrite 2!subst_arr, 2!liftSubst_singleSubst_eq.
    - intros n n' Rn RP0.
      pose proof (neNfTermEq RN Rn).
      eapply reflectLR.
      + escape; now eapply ty_natElim.
      + eapply ty_conv ; [| eapply escapeEq; now symmetry].
        escape; eapply ty_natElim; tea.
        all: now eapply ty_conv.
      + escape ; destruct Rn; now eapply convneu_natElim.
  Qed.

  Lemma natElimRedEq :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPQext _ _ Rnn' ]).
  Proof. intros; now apply (fst natElimRedEqAux). Qed.
End NatElimRedEq.


Section NatElimValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN).

  Lemma elimSuccHypTyValid {P Q}
    (VP : [Γ ,, tNat ||-v<l> P ≅ Q| VΓN]) :
    [Γ ||-v<l> elimSuccHypTy P  ≅ elimSuccHypTy Q | VΓ].
  Proof.
    unfold elimSuccHypTy.
    unshelve eapply PiValid.
    1: exact VN.
    eapply simpleArrValid; tea.
    eapply substLiftS; tea.
    eapply succValid'; [now rewrite wk1_ren_on|].
    eapply var0Valid.
  Qed.

  Lemma natElimCongValid {P P' hz hz' hs hs'}
    (VP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN ])
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VP])
    {n n'}
    (Vn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : _ | VΓ | VPn].
  Proof.
    pose proof (elimSuccHypTyValid VP).
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubst' VN Vσσ').
    instValid Vuσ; cbn -[elimSuccHypTy elimSuccHypTyValid] in *.
    eapply irrLREq. 1: now rewrite singleSubstComm'.
    unshelve eapply natElimRedEq; tea.
    4-6: now escape.
    + now eapply natRedTy.
    + intros ?? Rn; rewrite 2!up_single_subst; unshelve eapply validTyExt; cycle 3; tea.
      now unshelve econstructor.
    + now rewrite 2!elimSuccHypTy_subst.
    + eapply irrLREq; tea; now rewrite singleSubstComm'.
    + eapply irrLREq; tea; now rewrite elimSuccHypTy_subst.
  Qed.
End NatElimValid.

Lemma natElimValid {Γ Γ' l P hz hz' hs hs' n n'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN])
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VΓ VP])
    (Vn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn):
    [Γ ||-v<l> tNatElim P hz hs n : _ | VΓ | VPn].
Proof. now eapply lrefl, natElimCongValid. Qed.

Section NatElimRedValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    { P P' hz hz' hs hs'}
    (* (VP : [Γ ,, tNat ||-v<l> P | VΓN]) *)
    (VP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN ])
    (* (VP' := ureflValidTy VPP') *)
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VΓ VP]).

  Lemma natElimZeroValid  :
    [Γ ||-v<l> tNatElim P hz hs tZero ≅ hz : _ | VΓ | VPz].
  Proof.
    eapply redSubstValid. 2: now eapply lrefl.
    constructor; intros; cbn; rewrite singleSubstComm'.
    instValid Vσσ'; instValid (liftSubst' VN Vσσ'); escape.
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
      instValid Vσσ'; instValid (liftSubst' VN Vσσ'); escape.
      eapply redtm_natElimSucc; tea; refold.
      + now rewrite <- (singleSubstComm' _ tZero σ).
      + now rewrite elimSuccHypTy_subst.
    * eapply lrefl, simple_appValid.
      2: now eapply natElimCongValid.
      eapply appcongValid'; tea.
      1: eapply irrValidTm; tea; now eapply natValid.
      now rewrite subst_arr, liftSubst_singleSubst_eq.
      Unshelve. 2,4: tea. 2: now eapply lrefl.
        eapply simpleArrValid; tea; now eapply substS.
  Qed.

End NatElimRedValid.

End Nat.
