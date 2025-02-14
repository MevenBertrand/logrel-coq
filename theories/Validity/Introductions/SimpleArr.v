From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity Irrelevance Properties Pi Application Lambda Var.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrValidity.

  Context `{GenericTypingProperties}.

  Lemma simpleArrValid {l Γ Γ' F F' G G'} (VΓ : [||-v Γ ≅ Γ'])
    (VF : [Γ ||-v< l > F ≅ F' | VΓ ])
    (VG : [Γ ||-v< l > G ≅ G' | VΓ]) :
    [Γ ||-v<l> arr F G ≅ arr F' G' | VΓ].
  Proof.
    unshelve eapply PiValid; tea.
    erewrite <-2!wk1_ren_on.
    now eapply wk1ValidTy.
  Qed.

  Lemma simple_appValid {Γ Γ' t t' u u' F F' G G' l}
    (VΓ : [||-v Γ ≅ Γ'])
    {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
    (VG : [Γ ||-v<l> G ≅ G' | VΓ])
    (VΠ : [Γ ||-v<l> arr F G ≅ arr F' G' | VΓ])
    (Vt : [Γ ||-v<l> t ≅ t' : arr F G | _ | VΠ])
    (Vu : [Γ ||-v<l> u ≅ u' : F | _ | VF]) :
    [Γ ||-v<l> tApp t u ≅ tApp t' u' : G| _ | VG].
  Proof.
    unshelve (eapply irrValidTmRfl;[|now eapply appcongValid]).
    1: now eapply irrValidTmRfl.
    now bsimpl.
  Qed.

End SimpleArrValidity.
