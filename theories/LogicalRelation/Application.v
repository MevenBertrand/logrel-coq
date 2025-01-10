From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Reflexivity Weakening Neutral Transitivity Reduction NormalRed.

Set Universe Polymorphism.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

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

Lemma scons_wk_id {Γ t u} : t[u .: wk_id (Γ:=Γ) >> tRel] = t[u..].
Proof. now bsimpl. Qed.

Lemma codSubst {Γ u u' F G l l'}
  (RΠ : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<l'> F]}
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> G[u..]]) :
  [RGu | Γ ||- G[u..] ≅ G[u'..]].
Proof.
  pose (RΠ' := invLRcan RΠ ProdType); cbn in RΠ'.
  set (h := normRedΠ0 _) in RΠ'.
  assert (wfΓ : [|-Γ]) by (escape; gen_typing).
  unshelve epose proof (PolyRed.posExt h wk_id wfΓ _).
  3:cbn; irrelevance.
  cbn -[wk_id] in *. rewrite scons_wk_id in X.
  irrelevance.
Qed.

Lemma appcongTerm {Γ t t' u u' F G l l'}
  (RΠ : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<l'> F]}
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ])
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> G[u..]]) :
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu].
Proof.
  pose proof (codSubst RΠ Ruu' RGu).
  normRedΠin Rtt'; destruct Rtt' as [Rt Rt' ? app].
  assert (wfΓ : [|-Γ]) by gen_typing.
  unshelve epose proof (hX := app Γ u u' (@wk_id Γ) wfΓ _).
  1: abstract (irrelevance0; [| exact Ruu']; cbn; now bsimpl).
  pose proof (PiRedTmEq.red Rt); pose proof (PiRedTmEq.red Rt').
  unshelve epose proof (redSubstTmEq (A':=G[u'..]) (tl:=tApp t u) (tr:=tApp t' u')  _ hX _ _ _).
  all: rewrite ?wk_id_ren_on, ?scons_wk_id; escape; cbn in *; tea.
  1,2: gen_typing.
  irrelevance.
Qed.

Lemma appcongTerm' {Γ t t' u u' F F' G l l' X}
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
Qed.

End Application.


