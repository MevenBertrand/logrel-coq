From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application Nat.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Nat.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma natValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tNat | VΓ].
Proof.
  unshelve econstructor; intros; now eapply natRed.
Defined.

Lemma natValidU {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tNat : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply natTermRed.
Qed.

Lemma zeroValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']):
  [Γ ||-v<l> tZero : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; unshelve eapply zeroRed; tea.
  3: now eapply natRedTy.
Qed.

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
    (VP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN ])
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
