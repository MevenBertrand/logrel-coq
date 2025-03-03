From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import  Properties.
From LogRel.LogicalRelation.Introductions Require Import Empty.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Empty.
Context `{GenericTypingProperties}.

Lemma emptyValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tEmpty | VΓ].
Proof.
  constructor; intros; now apply emptyRed.
Defined.

Lemma emptyValidU {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']):  [Γ ||-v<one> tEmpty : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply emptyTermRed.
Qed.


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
