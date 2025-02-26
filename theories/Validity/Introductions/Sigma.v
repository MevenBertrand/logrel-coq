From Coq Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Poly.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly ValidityTactics.


Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaCongRed.

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

Lemma validΣdom {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΣ : [Γ ||-v<l> tSig F G ≅ tSig F' G' | VΓ]) :
  [Γ ||-v<l> F ≅ F' | VΓ].
Proof.
  constructor; intros ? wfΔ ?? Vσ; eapply redΣdom, (validTyExt VΣ wfΔ Vσ).
Qed.

Lemma validΣcod {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΣ : [Γ ||-v<l> tSig F G ≅ tSig F' G' | VΓ]) :
  [Γ,, F ||-v<l> G ≅ G' | validSnoc VΓ (validΣdom VΣ)].
Proof.
  constructor; intros ? wfΔ ?? [Vσ hd].
  pose proof (RΠ := validTyExt VΣ wfΔ Vσ).
  rewrite 2!subst_sig in RΠ.
  generalize (instKripkeSubst (normRedΣ RΠ).(PolyRed.posRed) _ hd).
  cbn -[wk1]; now rewrite 2!eta_up_single_subst.
Qed.

Lemma substSΣ {Γ Γ' F F' G G' t u l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΣ : [Γ ||-v<l> tSig F G ≅ tSig F' G' | VΓ])
  (Vt : [Γ ||-v<l> t ≅ u : F | VΓ | validΣdom VΣ]) :
  [_ ||-v<l> G[t..] ≅ G'[u..] | VΓ].
Proof. eapply substS ; tea; eapply validΣcod. Qed.

Lemma SigRed {Γ Γ' F G F' G' l}
  (VΓ : [||-v Γ ≅ Γ'])
  (VF : [ Γ ||-v< l > F ≅ F' | VΓ ])
  (VG : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF ])
  {Δ σ σ'} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ])
  : [ Δ ||-< l > (tSig F G)[σ] ≅ (tSig F' G')[σ'] ].
Proof.
  rewrite 2!subst_sig; eapply LRSig', substParamRedTy; tea; intros; gtyping.
Qed.

Lemma SigValid {Γ Γ' F G F' G' l}
  (VΓ : [||-v Γ ≅ Γ'])
  (VF : [ Γ ||-v< l > F ≅ F' | VΓ ])
  (VG : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF ])
  : [Γ ||-v< l > tSig F G ≅ tSig F' G' | VΓ].
Proof. constructor; intros; now eapply SigRed. Qed.
End SigmaCongRed.

(* Lemma up_single_subst {t σ u} : t[up_term_term σ][u..] = t[u .:  σ].
Lemma up_subst_single {t σ a} : t[up_term_term σ][a..] = t[a .: σ].
Proof. now asimpl. Qed. *)

(* Lemma subst_wk_id_tail Γ P t : P[t .: @wk_id Γ >> tRel] = P[t..]. *)
(* Lemma wk_id_shift {t a Γ} : t[a .: @wk_id Γ >> tRel] = t[a..].
Proof. now bsimpl. Qed. *)

(* Lemma eta_up_single_subst A σ : A[up_term_term (↑ >> σ)][(σ var_zero)..] = A[σ].
Lemma split_valid_subst_wk_id {Γ G σ} :
 G[σ] = G[up_term_term (↑ >> σ)][σ var_zero .: (@wk_id Γ) >> tRel].
Proof.  now rewrite wk_id_shift, up_subst_single, scons_eta'. Qed. *)


Section SigTmValidity.
  Context `{GenericTypingProperties}.

  Section Lemmas.
  Context {Γ Γ' F  F' G  G'} {VΓ : [||-v Γ ≅ Γ']}
    {VF : [ Γ ||-v< one > F ≅ F' | VΓ ]}
    (VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ])
    (VFeqU : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ])
    (VGeqU : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc VΓ VF | VU ]).


  Lemma sigTmEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ ])
    : [Δ |-[ ta ] tSig F[σ] G[up_term_term σ] ≅ tSig F'[σ'] G'[up_term_term σ'] : U].
  Proof.
    pose proof (Vuσ := liftSubst' VF Vσσ').
    instValid Vσσ'; instValid Vuσ; escape.
    eapply convtm_sig; tea.
  Qed.


  Lemma SigURedTm {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
    : URedTm zero Δ (tSig F G)[σ].
  Proof.
    exists (tSig F G)[σ].
    2: constructor.
    pose proof (Vuσσ := liftSubst' VF Vσ); instValid Vσ ; instValid Vuσσ; escape;
      eapply redtmwf_refl; cbn; now eapply ty_sig.
  Defined.
  End Lemmas.

  Context {Γ Γ' F  F' G  G'} {VΓ : [||-v Γ ≅ Γ']}
    {VF : [ Γ ||-v< one > F ≅ F' | VΓ ]}
    {VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ]}
    (VFU : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ])
    (VGU : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc VΓ VF | VU ]).

  Lemma SigCongRedU {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
    : [ Δ ||-< one > (tSig F G)[σ] ≅ (tSig F' G')[σ'] : U | validTyExt (UValid VΓ) tΔ Vσ ].
  Proof.
    set (RΣ := SigURedTm VU VFU VGU tΔ Vσ).
    pose (v := validSnoc VΓ (urefl VF)).
    unshelve epose (RΣ' := @SigURedTm _ _ F' F' G' G' _ _ _ _ _ _ _ _ _ (urefl Vσ)).
    1-4: ltac2:(Control.enter irrValid).
    unshelve eexists RΣ RΣ'.
    - cbn; instValid Vσ; instValid (liftSubst' VF Vσ); escape; cbn in *; gtyping.
    - unshelve (eapply redTyRecBwd, cumLR, SigRed; tea).
      all: unshelve (eapply univValid; tea; irrValid).
      eapply UValid.
  Qed.

  Lemma SigCongValidU : [ Γ ||-v< one > tSig F G ≅ tSig F' G' : U | VΓ | UValid VΓ ].
  Proof. econstructor; intros Δ tΔ  σ σ' Vσσ'; eapply SigCongRedU. Qed.

End SigTmValidity.


Section SigRedTmEqHelper.
  Import SigRedTmEq.
  Context `{GenericTypingProperties}.

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


  Context {Γ l A A'} (RA : [Γ ||-Σ<l> A ≅ A'])
    {t u} (Rt : SigRedTm RA t) (Ru : SigRedTm RA u).

  (* Let Rout : [Γ ||-Σ<l> RA.(ParamRedTy.outTy)].
  Proof.
    apply normRedΣ0.
    econstructor; [eapply redtywf_refl|..]; destruct RA; tea.
    cbn in *; gen_typing.
  Defined. *)

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


End SigRedTmEqHelper.

Section SigRedTmEqHelper.
  Context `{GenericTypingProperties}.
  Import SigRedTmEq.

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

End SigRedTmEqHelper.

Section ProjRed.
  Import SigRedTmEq.
  Context `{GenericTypingProperties}.

  (* Lemma redSigRedTm {l Δ F G} {p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (Rp : SigRedTm ΣA p) :
    [Δ ||-<l> p ≅ p' : _ | LRSig' (normRedΣ0 RΣ)] ->
    [Δ ||-<l> p ≅  : _ | LRSig' (normRedΣ0 RΣ)] ->

SigRedTmEq.whnf *)

  (* Lemma sigRedTmEqNf {l Δ F G p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (Rp : [Δ ||-<l> p ≅ p' : _ | LRSig' (normRedΣ0 RΣ)]) :
    [Δ ||-<l> p ≅ Rp.(redL).(nf) : _ | LRSig' (normRedΣ0 RΣ)].
  Proof.
    symmetry; eapply redTmEqFwd.
    + eapply lrefl; irrelevance.
    + eapply Rp.(redL).(red).
    + eapply whnf.
  Qed. *)


  Lemma fstRed {l Δ F F' G G' p p'}
    (RΣ : [Δ ||-<l> tSig F G ≅ tSig F' G'])
    (RF : [Δ ||-<l> F ≅ F'])
    (Rp : [Δ ||-<l> p ≅ p' : _ | LRSig' (normRedΣ RΣ)]) :
    [Δ ||-<l> tFst p ≅ tFst p' : _ | RF].
  Proof.
    (* pose proof (redTmFwd' Rp) as []. *)
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

  Context {l Γ Γ' F F' G G' } (VΓ : [||-v Γ ≅ Γ'])
    (VF : [Γ ||-v< l > F ≅ F' | VΓ ])
    (VG : [Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF])
    (VΣ := SigValid VΓ VF VG).

  Lemma fstValid {p p'} (Vp : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ]):
    [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VF].
  Proof.
    constructor; intros; cbn; instValid Vσσ'.
    (unshelve now eapply fstRed; eapply irrLR); refold; now rewrite <-?subst_sig.
  Qed.

  Lemma subst_fst {t σ} : tFst t[σ] = (tFst t)[σ].
  Proof. reflexivity. Qed.

  Lemma sndValid {p p'} (Vp : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ])
    (VGfst := substS VG (fstValid Vp)) :
    [Γ ||-v<l> tSnd p ≅ tSnd p' : _ | VΓ | VGfst].
  Proof.
    constructor; intros; cbn; instValid Vσσ'.
    unshelve (eapply irrLREq; [|now eapply sndRed, irrLR]); refold.
    4: exact RVΣ.
    + refold; now rewrite 2!subst_fst, <-2!singleSubstComm'.
    + now rewrite subst_fst, singleSubstComm'.
  Qed.

End ProjRed.



Section PairRed.
  Context `{GenericTypingProperties}.

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
    (* pose proof (LRTyEqRedRight _ RBBfst). *)
    escape.
    eapply redSubstTmEq; tea.
    1: now eapply irrLRConv.
    1,2: eapply redtm_snd_beta; tea; now eapply ty_conv.
  Qed.

  Import SigRedTmEq.

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

  Lemma subst_sig {A B σ} : (tSig A B)[σ] = (tSig A[σ] B[up_term_term σ]).
  Proof. reflexivity. Qed.

  Lemma subst_pair {A B a b σ} : (tPair A B a b)[σ] = (tPair A[σ] B[up_term_term σ] a[σ] b[σ]).
  Proof. reflexivity. Qed.

  Lemma subst_snd {p σ} : (tSnd p)[σ] = tSnd p[σ].
  Proof. reflexivity. Qed.

  Lemma up_subst_single' t a σ : t[up_term_term σ][(a[σ])..] = t[a..][σ].
  Proof. now bsimpl. Qed.

  Lemma pairFstValid {Γ Γ' A B a b l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tFst (tPair A B a b) ≅ a : _ | VΓ | VA].
  Proof.
    eapply redSubstValid; tea.
    constructor; intros; rewrite <-subst_fst, subst_pair.
    instValid Vσσ'; instValid (liftSubst' VA Vσσ'); escape.
    eapply redtm_fst_beta; tea.
    now rewrite up_subst_single'.
  Qed.

  Lemma pairSndValid {Γ Γ' A B a b l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa])
    (Vfstall := pairFstValid VΓ VA VB Va Vb)
    (VBfst := substS VB Vfstall) :
    [Γ ||-v<l> tSnd (tPair A B a b) ≅ b : _ | VΓ | VBfst].
  Proof.
    eapply redSubstValid; cycle 1.
    + irrValid.
    + constructor; intros.
      rewrite <-up_subst_single', subst_snd, <-subst_fst, subst_pair.
      instValid Vσσ'; instValid (liftSubst' VA Vσσ'); escape.
      eapply redtm_snd_beta; tea.
      now rewrite up_subst_single'.
  Qed.


  Lemma pairCongValid {Γ Γ' A A' B B' a a' b b' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A ≅ A' | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B ≅ B' | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a ≅ a' : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b ≅ b' : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tPair A B a b ≅ tPair A' B' a' b' : _ | VΓ | VΣ].
  Proof.
    constructor; intros; rewrite 2!subst_pair.
    instValid Vσσ'; instValid (liftSubst' VA Vσσ').
    eapply irrLREq; [now rewrite subst_sig|].
    eapply pairCongRed; tea.
    now eapply irrLRConv; tea; rewrite up_subst_single'; eapply lrefl.
    Unshelve.
    1: now rewrite <-2!subst_sig.
    now rewrite 2!up_subst_single'.
  Qed.

  Lemma pairValid {Γ Γ' A A' B B' a a' b b' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A ≅ A' | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B ≅ B' | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a ≅ a' : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b ≅ b' : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tPair A B a b : _ | VΓ | VΣ].
  Proof. now eapply lrefl, pairCongValid. Qed.

  Lemma sigEtaEqValid {Γ A B p p' l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ])
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ])
    (Vfstpp' : [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VA])
    (Vfst := fstValid VΓ VA VB Vp)
    (VBfst := substS VB Vfst)
    (Vsndpp' : [Γ ||-v<l> tSnd p ≅ tSnd p' : _| VΓ | VBfst]) :
    [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ].
  Proof.
    constructor; intros.
    pose proof (substS VB Vfstpp').
    instValid Vσσ'.
    eapply irrLREq; [now rewrite subst_sig|].
    eapply sigEtaRed.
    + now eapply lrefl, irrLR.
    + now eapply urefl, irrLR.
    + tea.
    + eapply irrLREq; tea.
      now rewrite subst_fst, up_subst_single'.
    Unshelve.
    2: now erewrite <-2!subst_sig.
    now rewrite 2!subst_fst, 2!up_subst_single'.
  Qed.


  Lemma sigEtaValid {Γ A B p l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]) :
    [Γ ||-v<l> tPair A B (tFst p) (tSnd p) ≅ p : _ | VΓ | VΣ].
  Proof.
    pose (Vfst := fstValid _ _ _ Vp).
    pose (Vsnd := sndValid _ _ _ Vp).
    pose proof (pairFstValid _ _ _ Vfst Vsnd).
    pose proof (pairSndValid _ _ _ Vfst Vsnd).
    pose proof (pairValid _ _ _ Vfst Vsnd).
    unshelve eapply sigEtaEqValid; tea.
    cbn in * ; irrValid.
  Qed.

End PairRed.




