From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.

Lemma codSubst {Γ u u' F F' G G' l l'}
  (RΠ : [Γ ||-<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-<l'> F ≅ F']}
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ]) :
  [Γ ||-<l> G[u..] ≅ G'[u'..]].
Proof.
  set (RΠ' :=normRedΠ RΠ).
  eapply instKripkeSubst; [|now eapply irrLR].
  intros; eapply RΠ'.(PolyRed.posRed); now eapply irrLR.
  Unshelve.
  3: eapply instKripke.
  2,4: eapply RΠ'.(PolyRed.shpRed).
  2: tea.
  escape; gtyping.
Qed.

Lemma appcongTerm {Γ t t' u u' F F' G G' l l'}
  (RΠ : [Γ ||-<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-<l'> F ≅ F']}
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ])
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> G[u..] ≅ G'[u'..]]) :
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu].
Proof.
  set (RΠ' :=normRedΠ RΠ).
  assert [LRPi' RΠ' | _ ||- t ≅ t' : _ ] as [Rt Rt' ? app] by now eapply irrLREq.
  assert (wfΓ : [|-Γ]) by (escape ; gtyping).
  eapply redSubstTmEq.
  + unshelve (eapply irrLREqCum, app; cbn; now erewrite eq_subst_scons); [|tea|].
    2: rewrite wk_id_ren_on; eapply irrLREqCum; tea; now rewrite wk_id_ren_on.
  + rewrite 2!wk_id_ren_on; eapply redtm_app; [now destruct (PiRedTmEq.red Rt)| now escape].
  + rewrite wk_id_ren_on; eapply redtm_app.
    2: eapply ty_conv; now escape.
    1: eapply redtm_conv; [now destruct (PiRedTmEq.red Rt')| now escape].
Qed.

End Application.


