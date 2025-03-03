From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Poly.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaRed.

Context `{GenericTypingProperties}.

Lemma redΣdom {Γ F F' G G' l} : [Γ ||-<l> tSig F G ≅ tSig F' G'] -> [Γ ||-<l> F ≅ F'].
Proof.
  intros RΣ0; unshelve eapply (instKripke _ (normRedΣ RΣ0).(PolyRed.shpRed)).
  escape; gtyping.
Qed.

Lemma redΣcod {Γ F F' G G' l} : [Γ ||-<l> tSig F G ≅ tSig F' G'] -> [Γ,, F ||-<l> G ≅ G'].
Proof.
  intros RΣ0; unshelve eapply (instKripkeFam _ (normRedΣ RΣ0).(PolyRed.posRed)).
  escape; gtyping.
Qed.

Lemma redΣcodfst {Γ F F' G G' l} (RΣ: [Γ ||-<l> tSig F G ≅ tSig F' G']) [RA : [Γ ||-<l> F ≅ F']] [a a'] :
  [_ ||-<l> a ≅ a' : _ | RA] -> [Γ ||-<l> G[a..] ≅ G'[a'..]].
Proof.
  intros Ra.
  unshelve now eapply (instKripkeSubst (normRedΣ RΣ).(PolyRed.posRed)); eapply irrLR.
  apply (redΣdom (LRSig' (normRedΣ RΣ))).
Qed.


Import SigRedTmEq.

Lemma isLRPair_isWfPair {Γ A A' B B' l p} (ΣA : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣ := (normRedΣ ΣA))
  (Rp : isLRPair RΣ p) :
    isWfPair Γ A B p.
Proof.
  assert (wfΓ: [|- Γ]) by (escape ; gen_typing).
  destruct Rp as [???? wtdom convtydom wtcod convtycod rfst rsnd|].
  2: now econstructor.
  pose proof (Ra := instKripkeTm wfΓ rfst).
  pose proof (instKripkeSubst RΣ.(PolyRed.posRed) _ Ra).
  epose proof (hb := rsnd _ wk_id wfΓ).
  cbn -[wk_id] in *.
  escape; rewrite <-eq_subst_scons,wk_id_ren_on in EscLhb.
  now econstructor.
Qed.

Section Helpers.
Context {Γ l A A'} (RA : [Γ ||-Σ<l> A ≅ A'])
  {t u} (Rt : SigRedTm RA t) (Ru : SigRedTm RA u).

Lemma build_sigRedTmEq
  (eqnf : [Γ |- nf Rt ≅ nf Ru : ParamRedTy.outTyL RA])
  (wfΓ : [|- Γ])
  (Rfst : [ instKripke wfΓ RA.(PolyRed.shpRed) | _ ||- tFst (nf Rt) ≅ tFst (nf Ru) : _ ])
  (Rsnd : [ instKripkeSubst RA.(PolyRed.posRed) _ Rfst | _ ||- tSnd (nf Rt) ≅ tSnd (nf Ru) : _ ]) :
  [LRSig' RA | _ ||- t ≅ u : _].
Proof.
  unshelve eexists Rt Ru _; tea.
  - intros; now unshelve now eapply irrLR; rewrite 2!wk_fst; eapply wkLR.
  - intros; eapply irrLREq.
    2: now unshelve now rewrite 2!wk_snd; eapply wkLR.
    rewrite wk_fst; clear; now bsimpl.
Qed.

Lemma redtmwf_fst {F G f f'} :
  [ Γ |- f :⤳*: f' : tSig F G ] ->
  [ Γ |- tFst f :⤳*: tFst f' : F ].
Proof.
  intros [] ; constructor; [| now eapply redtm_fst].
  timeout 1 gen_typing.
Qed.

Lemma redtmwf_snd {F G f f'} :
  [ Γ |- f :⤳*: f' : tSig F G ] ->
  [ Γ |- G[(tFst f)..] ≅ G[(tFst f')..]] ->
  [ Γ |- tSnd f :⤳*: tSnd f' : G[(tFst f)..] ].
Proof.
  intros [] ? ; constructor; [| now eapply redtm_snd].
  eapply ty_conv; [| now symmetry]; timeout 1 gen_typing.
Qed.
End Helpers.


Lemma build_sigRedTmEq' {Γ l F F' G G'}
  (RΣ0 : [Γ ||-<l> tSig F G ≅ tSig F' G'])
  (RΣ := normRedΣ RΣ0)
  {t u} (Rt : SigRedTm RΣ t) (Ru : SigRedTm RΣ u)
  (Rdom := redΣdom RΣ0)
  (Rfst : [ Rdom | _ ||- tFst (nf Rt) ≅ tFst (nf Ru) : _ ])
  (Rcod := instKripkeSubst RΣ.(PolyRed.posRed) _ Rfst)
  (Rsnd : [ Rcod | _ ||- tSnd (nf Rt) ≅ tSnd (nf Ru) : _ ]) :
  [LRSig' RΣ | _ ||- t ≅ u : _].
Proof.
  unshelve eapply (build_sigRedTmEq _ Rt Ru).
  1: escape; gtyping.
  1,3: eapply irrLREq; tea; reflexivity.
  pose proof (redΣcod RΣ0); escape.
  eapply convtm_eta_sig; cbn in *; tea; destruct Rt, Ru; cbn in *.
  all: first [now eapply isLRPair_isWfPair| gtyping].
Qed.

Lemma fstRed {l Δ F F' G G' p p'}
  (RΣ : [Δ ||-<l> tSig F G ≅ tSig F' G'])
  (RF : [Δ ||-<l> F ≅ F'])
  (Rp : [Δ ||-<l> p ≅ p' : _ | LRSig' (normRedΣ RΣ)]) :
  [Δ ||-<l> tFst p ≅ tFst p' : _ | RF].
Proof.
  eapply redSubstTmEq; cycle 1.
  + eapply redtm_fst, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
  + eapply redtm_fst, tmr_wf_red.
    eapply redtmwf_conv.
    1:exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    now escape.
  + unshelve eapply irrLR, instKripkeTm; cycle -1.
    1: intros; rewrite <- 2!wk_fst; now unshelve eapply (SigRedTmEq.eqFst Rp).
    escape; gtyping.
Qed.

Lemma sndRed {l Δ F F' G G'} {p p'}
  (RΣ : [Δ ||-<l> tSig F G ≅ tSig F' G'])
  (RΣn := LRSig' (normRedΣ RΣ))
  (Rp : [Δ ||-<l> p ≅ p' : _ | RΣn])
  (RGfstp : [Δ ||-<l> G[(tFst p)..] ≅ G'[(tFst p')..]]) :
  [Δ ||-<l> tSnd p ≅ tSnd p' : _ | RGfstp].
Proof.
  eapply redSubstTmEq; cycle 1.
  + eapply redtm_snd, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
  + eapply redtm_snd, tmr_wf_red, redtmwf_conv.
    1: exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    now escape.
  + assert (wfΔ : [|- Δ]) by (escape; gen_typing).
    erewrite <-wk_id_ren_on, <-(wk_id_ren_on _ (tSnd (nf (redL _)))).
    eapply irrLRConv, (SigRedTmEq.eqSnd Rp wk_id wfΔ).
    erewrite eq_subst_scons; eapply kripkeLRlrefl.
    1: intros; eapply (normRedΣ RΣ).(PolyRed.posRed); tea.
    symmetry; rewrite wk_fst, 2!wk_id_ren_on.
    eapply irrLREq; [now rewrite wk_id_ren_on|].
    eapply fstRed; now pose proof (redTmFwd' Rp) as [].
    Unshelve. 1: tea. now eapply redΣdom.
Qed.

Lemma pairFstRed {Γ A A' B B' a a' b b' l}
  (RA : [Γ ||-<l> A ≅ A'])
  (RB : [Γ ,, A ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [Γ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [Γ ||-<l> a ≅ a' : A | RA])
  (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA].
Proof.
  escape.
  eapply redSubstTmEq; tea.
  1,2: eapply redtm_fst_beta; tea; now eapply ty_conv.
Qed.

Lemma pairFstRed' {Γ A A' B B' a a' b b' l}
  (RA : [Γ ||-<l> A ≅ A'])
  (RB : [Γ ,, A ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [Γ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [Γ ||-<l> a ≅ a' : A | RA])
  (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA]
  × [Γ ||-<l> tFst (tPair A B a b) ≅ a : _ | lrefl RA]
  × [Γ ||-<l> tFst (tPair A' B' a' b') ≅ a' : _ | urefl RA ].
Proof.
  escape.
  eapply redSubstTmEq'; tea.
  1,2: eapply redtm_fst_beta; tea; now eapply ty_conv.
Qed.

Lemma pairSndRed {Γ A A' B B' a a' b b' l}
  (RA : [Γ ||-<l> A ≅ A'])
  (RB : [Γ ,, A ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [Γ ||-<l> B[a..] ≅ B'[a'..] ])
  (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ≅ B'[(tFst (tPair A' B' a' b'))..]])
  (RBfsta : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..]])
  (Ra : [Γ ||-<l> a ≅ a' : A | RA])
  (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-<l> tSnd (tPair A B a b) ≅ tSnd (tPair A' B' a' b') : _ | RBfst ].
Proof.
  escape.
  eapply redSubstTmEq; tea.
  1: now eapply irrLRConv.
  1,2: eapply redtm_snd_beta; tea; now eapply ty_conv.
Qed.


Lemma sigEtaRed {Γ A A' B B' l p p'}
  (RΣ0 : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣn := normRedΣ RΣ0)
  (RΣ := LRSig' RΣn)
  (RA : [Γ ||-<l> A ≅ A'])
  (RBfst : [Γ ||-<l> B[(tFst p)..] ≅ B'[(tFst p')..]])
  (Rp : [Γ ||-<l> p : _ | RΣ])
  (Rp' : [Γ ||-<l> p' : _ | RΣ])
  (Rfstpp' : [Γ ||-<l> tFst p ≅ tFst p' : _ | RA])
  (Rsndpp' : [Γ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]) :
  [Γ ||-<l> p ≅ p' : _ | RΣ].
Proof.
  pose proof (redTmFwd' Rp) as [Rpnf _ _ _ _]; pose proof (Rpnf1 := fstRed _ RA Rpnf).
  pose proof (redTmFwd' Rp') as [Rpnf' _ _ _ _]; pose proof (Rpnf1' := fstRed _ RA Rpnf').
  unshelve eapply (build_sigRedTmEq' _ Rp.(redL) Rp'.(redL)).
  - transitivity (tFst p); [symmetry|transitivity (tFst p')]; now eapply irrLR.
  - pose proof (RBB' := instKripkeSubst RΣn.(PolyRed.posRed)).
    pose proof (RB := instKripkeSubst (kripkeLRlrefl RΣn.(PolyRed.posRed))).
    pose proof (RB' := instKripkeSubst (kripkeLRurefl RΣn.(PolyRed.posRed))).
    pose proof (RBpnf1 := RBB' _ _ _ Rpnf1); pose proof (sndRed _ Rpnf RBpnf1).
    pose proof (RBpnf1' := RBB' _ _ _ Rpnf1'); pose proof (sndRed _ Rpnf' RBpnf1').
    cbn in *; eapply irrLR.
    eapply ((transLR _ _).(transRedTm) _ (tSnd p)).
    1: symmetry; eapply irrLRConv; tea; exact (RB _ _ _ Rpnf1).
    eapply ((transLR _ _).(transRedTm) _ (tSnd p')); tea.
    eapply irrLRConv; [|tea].
    eapply RBB', urefl; tea.
    Unshelve.
    3: eapply RB', urefl; tea.
    eapply RB; now symmetry.
Qed.


Lemma mkPair_isLRPair {Γ A A' A1 B B' B1 a1 b1 l}
  (RΣ0 : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣ := normRedΣ RΣ0)
  (RA1 : [Γ ||-<l> A ≅ A1])
  (RB1 : [Γ ||-<l> B[a1..] ≅ B1[a1..]])
  (Ra1 : [Γ ||-<l> a1 : _ | RA1])
  (Rb1 : [Γ ||-<l> b1 : _ | RB1])
: isLRPair RΣ (tPair A1 B1 a1 b1).
Proof.
  escape.
  unshelve eapply PairLRPair; tea; intros.
  - now unshelve now eapply irrLR, wkLR.
  - now unshelve now eapply irrLREq, wkLR; tea; rewrite subst_ren_subst_mixed.
Qed.

Definition pairSigRedTm {Γ A A' A1 B B' B1 a1 b1 l}
  (RΣ0 : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣ1 : [Γ ||-<l> tSig A B ≅ tSig A1 B1])
  (RΣ := normRedΣ RΣ0)
  (Ra1 : [Γ ||-<l> a1 : _ | redΣdom RΣ0])
  (Rb1 : [Γ ||-<l> b1 : _ | redΣcodfst RΣ0 Ra1])
: SigRedTm RΣ (tPair A1 B1 a1 b1).
Proof.
  exists (tPair A1 B1 a1 b1); pose proof (RA := redΣdom RΣ1);
    pose proof (RB := redΣcodfst RΣ1 (fst (irrLR _ RA _ _) Ra1)).
  + eapply redtmwf_refl; cbn.
    assert (wfΓ : [|- Γ]) by (escape ; gtyping).
    assert [_ ||-<l> a1 : _ | urefl RA ] by now eapply irrLRConv.
    pose proof (instKripkeFamConv wfΓ (normRedΣ RΣ1).(PolyRed.posRed)).
    assert [_ ||-<l> b1 : _ | urefl RB ] by now eapply irrLRConv.
    escape.
    eapply ty_conv; [ eapply ty_pair; tea| now symmetry].
  + now unshelve now eapply mkPair_isLRPair; eapply irrLR.
Defined.

Lemma pairCongRed {Γ A A' B B' a a' b b' l}
  (RΣ0 : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣ := normRedΣ RΣ0)
  (RΣ' := LRSig' RΣ)
  (RA : [Γ ||-<l> A ≅ A'])
  (RBa : [Γ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [Γ ||-<l> a ≅ a' : A | RA])
  (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-<l> tPair A B a b ≅ tPair A' B' a' b' : _ | RΣ'].
Proof.
  assert (wfΓ : [|-Γ]) by (escape; gtyping).
  pose proof (convtyB := redΣcod RΣ').
  pose proof (wtB' := escape (symmetry (instKripkeFamConv wfΓ RΣ.(PolyRed.posRed)))).
  unshelve epose proof (pairFstRed' RA convtyB wtB' RBa Ra Rb) as (ff'&fa&fa').
  pose proof (RBconv := instKripkeSubst (kripkeLRlrefl RΣ.(PolyRed.posRed)) RA (fst (irrLR _ _ _ _) fa)).

  unshelve eapply build_sigRedTmEq'.
  + unshelve eapply pairSigRedTm; eapply lrefl; tea; now eapply irrLR.
  + unshelve eapply pairSigRedTm; tea; eapply urefl. now eapply irrLR.
    eapply irrLRConv; tea; eapply (instKripkeSubst (kripkeLRlrefl RΣ.(PolyRed.posRed)) RA Ra).
  + cbn; eapply irrLR, pairFstRed; tea.
  + unshelve now cbn; eapply irrLR; eapply pairSndRed; tea; symmetry.
    now eapply (instKripkeSubst RΣ.(PolyRed.posRed)).
Qed.

End SigmaRed.





