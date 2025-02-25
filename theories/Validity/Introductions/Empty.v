From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import  Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application.
From Equations Require Import Equations.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Empty.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma emptyRedTy {Γ} : [|- Γ] -> [Γ ||-Empty tEmpty ≅ tEmpty].
Proof. intros; constructor; eapply redtywf_refl; gen_typing. Defined.

Lemma emptyRed {Γ l} : [|- Γ] -> [Γ ||-<l> tEmpty].
Proof. intros; now apply LREmpty_, emptyRedTy. Defined.

Lemma emptyValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tEmpty | VΓ].
Proof.
  constructor; intros; now apply emptyRed.
Defined.

Lemma emptyURedTm {Δ l} (wfΔ : [|-Δ]) : URedTm l Δ tEmpty.
Proof.
  exists tEmpty; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma emptyTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tEmpty : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve eexists (emptyURedTm wfΔ) (emptyURedTm wfΔ); cbn.
  1: gtyping.
  now eapply (emptyRed (l:=zero)).
Defined.

Lemma emptyTermValid {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']):  [Γ ||-v<one> tEmpty : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply emptyTermRed.
Qed.


(* TODO : move *)
Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Section EmptyElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Empty tEmpty ≅ tEmpty])
    (RN := LREmpty_ _ NN)
    (WtP : [Γ,, tEmpty |- P])
    (WtQ : [Γ,, tEmpty |- Q])
    (eqPQ : [Γ,, tEmpty |- P ≅ Q])
    (RPQext : forall n n', [Γ ||-<l> n ≅ n' : _ | RN] -> [Γ ||-<l> P[n..] ≅ Q[n'..]]).

  #[local]
  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ P[n'..] ].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.

  Lemma emptyElimRedEq n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]) :
    [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPQext _ _ Rnn' ].
  Proof.
    pose proof (redTmFwd' Rnn') as [].
    depelim Rnn' ; eapply redSubstTmEq; cycle 1.
    + eapply redtm_emptyelim; tea; gen_typing.
    + eapply redtm_emptyelim; tea; gen_typing.
    + destruct eq; eapply irrLRConv.
      (* gtyping/gen_typing not working well here... *)
      2: eapply neNfTermEq; constructor; [now eapply ty_emptyElim |..].
      - eapply RPext; now symmetry.
      - eapply ty_conv; [now eapply ty_emptyElim|].
        symmetry; now eapply escapeEq, RPQext.
      - now eapply convneu_emptyElim.
      Unshelve. now eapply lrefl, RPQext.
  Qed.
End EmptyElimRedEq.


Section EmptyElimValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    { P P' }
    (VP : [Γ ,, tEmpty ||-v<l> P ≅ P' | VΓN]).

  Lemma emptyElimCongValid {n n'}
    (Vn : [Γ ||-v<l> n ≅ n' : tEmpty | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tEmptyElim P n ≅ tEmptyElim P' n' : _ | VΓ | VPn].
  Proof.
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubst' VN Vσσ').
    instValid Vuσ; cbn in *; escape.
    eapply irrLREq. 1: now rewrite singleSubstComm'.
    unshelve eapply emptyElimRedEq; rewrite ?elimSuccHypTy_subst; tea.
    + now apply emptyRedTy.
    + intros ; rewrite 2!up_single_subst; eapply validTyExt; tea.
      now unshelve econstructor.
  Qed.
End EmptyElimValid.

Lemma emptyElimValid {Γ l P n n'}
    (VΓ : [||-v Γ])
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tEmpty ||-v<l> P | VΓN])
    (Vn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn):
    [Γ ||-v<l> tEmptyElim P n : _ | VΓ | VPn].
Proof.
  eapply lrefl , emptyElimCongValid; tea.
Qed.

End Empty.
