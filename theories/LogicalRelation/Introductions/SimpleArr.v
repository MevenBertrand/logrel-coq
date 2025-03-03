From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrow.
  Context `{GenericTypingProperties}.

  Lemma shiftPolyRed {Γ l A A' B B'} : [Γ ||-<l> A ≅ A'] -> [Γ ||-<l> B ≅ B'] -> PolyRed Γ l A A' B⟨↑⟩ B'⟨↑⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros; now eapply wkLR.
    - intros; rewrite 2!shift_subst_scons; now eapply wkLR.
  Qed.

  Lemma ArrRedTy0 {Γ l A A' B B'} : [Γ ||-<l> A ≅ A'] -> [Γ ||-<l> B ≅ B'] -> [Γ ||-Π<l> arr A B ≅ arr A' B'].
  Proof.
    intros RA RB.
    eapply LRPiPoly0, shiftPolyRed; tea; escape; gtyping.
  Qed.

  Lemma ArrRedTy {Γ l A A' B B'} : [Γ ||-<l> A ≅ A'] -> [Γ ||-<l> B ≅ B'] -> [Γ ||-<l> arr A B ≅ arr A' B'].
  Proof. intros; eapply LRPi'; now eapply ArrRedTy0. Qed.

  Lemma polyRedArrExt {Γ l A A' B B' C C'} : PolyRed Γ l A A' B B' -> PolyRed Γ l A A' C C' -> PolyRed Γ l A A' (arr B C) (arr B' C').
  Proof.
    intros [RA RB] [RA' RC]; unshelve econstructor; tea.
    now unshelve (intros; rewrite 2!subst_arr; eapply ArrRedTy; [eapply RB|eapply RC]; tea; now eapply irrLR).
  Qed.

  Lemma simple_appcongTerm {Γ t t' u u' F F' G G' l}
    {RF : [Γ ||-<l> F ≅ F']}
    (RG : [Γ ||-<l> G ≅ G'])
    (RΠ : [Γ ||-<l> arr F G ≅ arr F' G'])
    (Rtt' : [Γ ||-<l> t ≅ t' : _ | RΠ])
    (Ruu' : [Γ ||-<l> u ≅ u' : F | RF ]) :
      [Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    unshelve (eapply irrLREq, appcongTerm; tea);
    erewrite !shift_subst1; tea; reflexivity.
  Qed.

End SimpleArrow.
