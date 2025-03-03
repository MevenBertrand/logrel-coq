(** * LogRel.Introductions.Var : Validity of variables. *)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe.
From LogRel.Validity Require Import Validity Irrelevance Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Var.
  Context `{GenericTypingProperties}.

  Lemma var0Valid {Γ Γ' l A A'} (VΓ : [||-v Γ ≅ Γ']) (VA : [Γ ||-v<l> A ≅ A'| VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | validSnoc VΓ VA | wk1ValidTy _ VA ].
  Proof.
    constructor; intros; cbn; epose (eqHead Vσσ').
    eapply irrLREq; tea; now bsimpl.
  Qed.

  Lemma var0Valid' {Γ Γ' l A A'} (VΓ : [||-v Γ,,A ≅ Γ']) (VA : [Γ,,A ||-v<l> A⟨↑⟩ ≅ A' | VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | VΓ | VA ].
  Proof.
    pose proof (invValidity VΓ) as (?&?&?&?&?&?&h) ; subst; cbn in h; subst.
    constructor; intros; cbn; eapply irrLREqCum;[| exact (eqHead Vσσ')].
    now asimpl.
  Qed.

  Lemma in_ctx_valid {Γ A n} (hin : in_ctx Γ n A)
    : forall {Γ'} (VΓ : [||-v Γ ≅ Γ']), ∑ l B, [Γ ||-v<l> A ≅ B | VΓ].
  Proof.
    induction hin as [| ???? hin ih] ; intros ? VΓ;
    pose proof (invValidity VΓ) as (?&?&?&VΓ'&VA &?&?); subst; cbn in *; subst.
    2: destruct (ih _ VΓ') as (?&?&?).
    all: eexists _, _; erewrite <- wk1_ren_on; now eapply wk1ValidTy.
  Qed.


  Lemma varnValid {Γ A n} (hin : in_ctx Γ n A) :  forall l {Γ' A'} (VΓ : [||-v Γ ≅ Γ']) (VA : [Γ ||-v<l> A ≅ A' | VΓ]),
    [Γ ||-v<l> tRel n : _ | VΓ | VA ].
  Proof.
    induction hin as [| ???? hin ih]; intros l ?? VΓ VA.
    1: eapply var0Valid'.
    pose proof (invValidity VΓ) as  (?&?&?&VΓ'&VA'&?&h) ; subst; cbn in h; subst.
    destruct (in_ctx_valid hin VΓ') as (?&?&h).
    pose proof (h' := wk1ValidTm VA' _ (ih _ _ _ _ h)).
    cbn -[wk1] in h'; rewrite wk1_ren in h'; unfold shift in h'.
    eapply irrValidTm; tea; change (ren_term ↑ d) with d⟨↑⟩.
    erewrite <- wk1_ren_on; eapply wk1ValidTy.
    eapply irrValidTy; tea; now eapply lrefl.
    Unshelve. 3: now eapply lrefl, convValidTy. now eapply lrefl.
  Qed.

  Lemma var1Valid {Γ l A B} (VΓ : [||-v (Γ,, A) ,, B]) (VA : [_ ||-v<l> A⟨↑⟩⟨↑⟩ | VΓ]) :
    [(Γ,, A) ,, B ||-v<l> tRel 1 : _ | VΓ | VA ].
  Proof.
    eapply varnValid; do 2 constructor.
  Qed.

End Var.