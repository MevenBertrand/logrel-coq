From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import  Induction  Escape Irrelevance Reflexivity Irrelevance Weakening Neutral Transitivity Reduction EqRedRight.
From LogRel.LogicalRelation.Introductions Require Import Application Universe.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion SingleSubst Reflexivity Reduction Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.

Section Empty.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma emptyRed {Γ l} : [|- Γ] -> [Γ ||-<l> tEmpty].
Proof.
  intros; eapply LREmpty_; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma emptyValid {Γ l} (VΓ : [||-v Γ]) : [Γ ||-v<l> tEmpty | VΓ].
Proof.
  unshelve econstructor; intros.
  + now eapply emptyRed.
  + cbn; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma emptyconvValid {Γ l} (VΓ : [||-v Γ]) (VEmpty : [Γ ||-v<l> tEmpty | VΓ]) :
  [Γ ||-v<l> tEmpty ≅ tEmpty | VΓ | VEmpty].
Proof.
  constructor; intros.
  enough [Δ ||-<l> tEmpty ≅ tEmpty | emptyRed wfΔ] by irrelevance.
  constructor; cbn; eapply redtywf_refl; gen_typing.
Qed.

Lemma emptyURedTm {Δ} (wfΔ : [|-Δ]) : URedTm (LogRelRec one) Δ tEmpty U (redUOneCtx wfΔ).
Proof.
  exists tEmpty; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma emptyTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tEmpty : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve eexists (emptyURedTm wfΔ) (emptyURedTm wfΔ) _; cbn.
  1,3: now eapply (emptyRed (l:=zero)).
  1: gen_typing.
  apply reflLRTyEq.
Defined.

Lemma emptyTermValid {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tEmpty : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply emptyTermRed.
Qed.

Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

(* TODO: move in Neutral *)
Lemma NeNfRed {Γ l A n n'} (RA : [Γ ||-<l> A]) : [Γ ||-NeNf n ≅ n' : A] -> [RA | Γ ||- n ≅ n' : A].
Proof.  intros []; now eapply neuTermEq. Qed.

Section EmptyElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Empty tEmpty])
    (RN := LREmpty_ _ NN)
    (RP : [Γ,, tEmpty ||-<l> P])
    (RQ : [Γ,, tEmpty ||-<l> Q])
    (eqPQ : [Γ,, tEmpty |- P ≅ Q])
    (RPpt : forall n n', [Γ ||-<l> n ≅ n' : _ | RN] -> [Γ ||-<l> P[n..]])
    (RPQext : forall n n' (Rn : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ Q[n'..] | RPpt _ _ Rn]).

  #[local]
  Lemma RQpt : forall n n', [Γ ||-<l> n ≅ n': _ | RN] -> [Γ ||-<l> Q[n..]].
  Proof. intros; now unshelve eapply LRTyEqRedRight, RPQext. Qed.

  #[local]
  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ _ Rn].
  Proof.
    intros; eapply transEq; [| eapply LRTyEqSym ].
    all: unshelve (eapply RPQext; cycle 1; tea); now eapply urefl.
    Unshelve. 2: eapply RQpt; now symmetry.
  Qed.

  Lemma emptyElimRedEq n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]) :
    [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPpt _ _ Rnn' ].
  Proof.
    inversion Rnn'  as [??????? prop]; subst.
    inversion prop as [?? h]; pose proof h as [?? conv]; subst.
    pose proof (convneu_whne conv); pose proof (convneu_whne (symmetry conv)).
    pose proof (Rne := neNfTermEq RN h); pose proof (Rnne := redwfSubstTmEq _ (lrefl Rne) redL).
    pose proof (RPQext _ _ Rne).
    escape.
    eapply redSubstTmEq; cycle 1.
    + eapply redtm_emptyelim; tea; gen_typing.
    + eapply redtm_emptyelim; tea; gen_typing.
    + now unshelve eapply escapeEq, RPQext.
    + eapply LRTmEqConv; [unshelve eapply RPext;[|now symmetry]|].
      eapply neuTermEq.
      * eapply ty_emptyElim; tea.
      * eapply ty_conv; [now eapply ty_emptyElim|now symmetry].
      * now eapply convneu_emptyElim.
  Qed.
End EmptyElimRedEq.


Section EmptyElimValid.
  Context {Γ l}
    (VΓ : [||-v Γ])
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    { P P' }
    (VP : [Γ ,, tEmpty ||-v<l> P | VΓN])
    (VPP' : [Γ ,, tEmpty ||-v<l> P ≅ P' | VΓN | VP ])
    (VP' := ureflValidTy VPP').

  Lemma emptyElimCongValid {n n'}
    (Vn : [Γ ||-v<l> n ≅ n' : tEmpty | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tEmptyElim P n ≅ tEmptyElim P' n' : _ | VΓ | VPn].
  Proof.
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubstEq' VN Vσσ').
    instValid Vuσ; cbn in *; escape.
    irrelevance0. 1: now rewrite singleSubstComm'.
    eapply emptyElimRedEq; rewrite ?elimSuccHypTy_subst; tea.
    + intros; irrelevance0; rewrite up_single_subst; [reflexivity|].
      unshelve eapply validTyEq; cycle 1 ; tea.
      now unshelve eapply consSubstEq.
    Unshelve.
      2: tea.
      intros ?? Rn; rewrite up_single_subst.
      unshelve eapply validTy.
      5: tea.
      3: unshelve eapply consSubstEq; tea.
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
  eapply lreflValidTm , emptyElimCongValid; tea.
  now eapply reflValidTy.
Qed.

End Empty.
