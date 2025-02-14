From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.


(* Section AppTerm.
  Context {Γ t u F G l l' l''}
    (hΠ : [Γ ||-Π<l> tProd F G])
    {RF : [Γ ||-<l'> F]}
    (Rt : [Γ ||-<l> t : tProd F G | LRPi' (normRedΠ0 hΠ)])
    (Ru : [Γ ||-<l'> u : F | RF])
    (RGu : [Γ ||-<l''> G[u..]]).

  Lemma app_id : [Γ ||-<l''> tApp (PiRedTmEq.nf Rt) u : G[u..] | RGu].
  Proof.
    assert (wfΓ := wfc_wft (escape RF)).
    replace (PiRedTm.nf _) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    irrelevance0.  2: eapply (PiRedTm.app Rt).
    cbn; now bsimpl.
    Unshelve. 1: eassumption.
    cbn; irrelevance0; tea; now bsimpl.
  Qed.

  Lemma appTerm0 :
      [Γ ||-<l''> tApp t u : G[u..] | RGu]
      × [Γ ||-<l''> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G[u..] | RGu].
  Proof.
    eapply redwfSubstTerm.
    1: unshelve eapply app_id; tea.
    escape.
    eapply redtmwf_app.
    1: apply Rt.
    easy.
  Qed.

End AppTerm. *)

(* Lemma appTerm {Γ t u F G l}
  (RΠ : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<l> F]}
  (Rt : [Γ ||-<l> t : tProd F G | RΠ])
  (Ru : [Γ ||-<l> u : F | RF])
  (RGu : [Γ ||-<l> G[u..]]) :
  [Γ ||-<l> tApp t u : G[u..]| RGu].
Proof.
  unshelve eapply appTerm0.
  7:irrelevance.
  3: exact (invLRΠ RΠ).
  all: tea.
  irrelevance.
Qed.

Lemma appTerm' {Γ t u F G l X}
  (RΠ : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<l> F]}
  (Rt : [Γ ||-<l> t : tProd F G | RΠ])
  (Ru : [Γ ||-<l> u : F | RF])
  (eq : X = G[u..])
  (RX : [Γ ||-<l> X]) :
  [Γ ||-<l> tApp t u : X | RX].
Proof.
  irrelevance0; [symmetry; tea|].
  unshelve eapply appTerm; cycle 1; tea.
  Unshelve. now rewrite <- eq.
Qed.  *)

(* eq_subst_scons *)
(* Lemma scons_wk_id {Γ t u} : t[u .: wk_id (Γ:=Γ) >> tRel] = t[u..].
Proof. now bsimpl. Qed. *)

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

(* Lemma appcongTerm' {Γ t t' u u' F F' G l l' X}
  (RΠ : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<l'> F]}
  {RF' : [Γ ||-<l'> F']}
  (RFF' : [Γ ||-<l'> F ≅ F' | RF])
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ])
  (Ru : [Γ ||-<l'> u : F | RF])
  (Ru' : [Γ ||-<l'> u' : F' | RF'])
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> X])
   : X = G[u..] ->
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : X | RGu].
Proof.
  intros eq.
  irrelevance0 ; [symmetry; apply eq|].
  unshelve eapply appcongTerm; cycle 2; tea.
  Unshelve. now rewrite <- eq.
Qed. *)

End Application.


