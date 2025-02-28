From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application.
From Equations Require Import Equations.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Empty.
Context `{GenericTypingProperties}.


Lemma emptyRedTy {Γ} : [|- Γ] -> [Γ ||-Empty tEmpty ≅ tEmpty].
Proof. intros; constructor; eapply redtywf_refl; gen_typing. Defined.

Lemma emptyRed {Γ l} : [|- Γ] -> [Γ ||-<l> tEmpty].
Proof. intros; now apply LREmpty_, emptyRedTy. Defined.

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

End Empty.

