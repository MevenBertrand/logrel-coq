
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application.

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

Lemma zeroRed {Γ l A B} {NN : [Γ ||-Nat A ≅ B]} : [Γ ||-<l> tZero : _ | LRNat_ l NN].
Proof.
  assert [|-Γ] by (pose (LRNat_ l NN); escape; gtyping).
  exists tZero tZero.
  1-3: gtyping.
  constructor.
Defined.

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
    (NN : [Γ ||-Nat tNat ≅ tNat])
    (RN := LRNat_ _ NN)
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



End Nat.
