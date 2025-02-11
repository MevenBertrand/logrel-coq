(** * LogRel.Introductions.Var : Validity of variables. *)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Introductions.Universe Weakening Neutral Induction NormalRed.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion Reflexivity SingleSubst Escape.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Var.
  Context `{GenericTypingProperties}.

  Lemma var0Valid {Γ l A} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | validSnoc VΓ VA | wk1ValidTy _ VA ].
  Proof.
    constructor; intros; cbn; epose (eqHead Vσσ'); irrelevance.
  Qed.

  Lemma var0Valid' {Γ l A} (VΓ : [||-v Γ,,A]) (VA : [Γ,,A ||-v<l> A⟨↑⟩ | VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | VΓ | VA ].
  Proof.
    pose proof (invValiditySnoc VΓ) as [? [? [? ]]]; subst.
    constructor; intros; cbn; epose (eqHead Vσσ'); irrelevance.
  Qed.

  Lemma in_ctx_valid {Γ A n} (hin : in_ctx Γ n A) : forall (VΓ : [||-v Γ]), ∑ l, [Γ ||-v<l> A | VΓ].
  Proof.
    induction hin as [| ???? hin ih]; intros VΓ;
    pose proof (invValiditySnoc VΓ) as [? [VΓ' [? ]]]; subst.
    2: destruct (ih VΓ').
    all: eexists; erewrite <- wk1_ren_on; now eapply wk1ValidTy.
  Qed.

  Lemma varnValid {Γ A n} (hin : in_ctx Γ n A) :  forall l (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]),
    [Γ ||-v<l> tRel n : _ | VΓ | VA ].
  Proof.
    induction hin as [| ???? hin ih]; intros l VΓ VA.
    1: eapply var0Valid'.
    pose proof (invValiditySnoc VΓ) as [? [VΓ' [VA' ]]]; subst.
    destruct (in_ctx_valid hin VΓ') as [? h].
    pose proof (h' := wk1ValidTm VA' _ (ih _ _ h)).
    cbn zeta in h'; rewrite wk1_ren_on in h'.
    eapply irrelevanceTm'; tea.
    now rewrite wk1_ren_on.
  Qed.

  Lemma var1Valid {Γ l A B} (VΓ : [||-v (Γ,, A) ,, B]) (VA : [_ ||-v<l> A⟨↑⟩⟨↑⟩ | VΓ]) :
    [(Γ,, A) ,, B ||-v<l> tRel 1 : _ | VΓ | VA ].
  Proof.
    eapply varnValid; do 2 constructor.
  Qed.

End Var.