From Coq Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Reflexivity Irrelevance Weakening Neutral Transitivity Reduction EqRedRight NormalRed InstKripke.
From LogRel.LogicalRelation.Introductions Require Import Application Universe Poly.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion SingleSubst Reflexivity Reduction Universe Poly.


Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaCongRed.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G' l}
    (VΓ : [||-v Γ])
    (VF : [ Γ ||-v< l > F | VΓ ])
    (VG : [ Γ ,, F ||-v< l > G | validSnoc VΓ VF ])
    (VF' : [ Γ ||-v< l > F' | VΓ ])
    (VG' : [ Γ ,, F' ||-v< l > G' | validSnoc VΓ VF' ])
    (VFF' : [ Γ ||-v< l > F ≅ F' | VΓ | VF ])
    (VGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF | VG ]).

  Lemma SigRed {Δ σ σ'} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ])
    : [ Δ ||-< l > (tSig F G)[σ] ].
  Proof.
    eapply LRSig'.
    pose (p := substPolyRed VΓ VF VG _ Vσ).
    set (pid := polyRedId p).
    set (peq := polyRedEqId p (substPolyRedEq VΓ VF VG _ Vσ p)).
    econstructor; tea.
    - eapply redtywf_refl, wft_sig; refold; destruct pid; now escape.
    - eapply lrefl; destruct peq; now escape.
    - destruct pid, peq; escape; eapply convty_sig; tea; now eapply lrefl.
  Defined.


  Lemma SigCongRed {Δ σ σ'} (wfΔ : [|- Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ])
    : [ Δ ||-< l > (tSig F G)[σ] ≅ (tSig F' G')[σ'] | SigRed wfΔ Vσ ].
  Proof.
    pose (p := substPolyRed VΓ VF VG _ Vσ).
    pose (p' := substPolyRed VΓ VF' VG' _ Vσ).
    pose (peq := substEqPolyRedEq VΓ VF VG _ Vσ VF' VG' VFF' VGG' p).
    destruct (polyRedId p); destruct (polyRedId p'); destruct (polyRedEqId p peq).
    escape; econstructor; cbn; tea.
    - apply redtywf_refl; eapply wft_sig; tea.
      eapply escape; now instValid (liftSubstEq' VF' (urefl Vσ)).
    - now eapply convty_sig.
  Qed.

End SigmaCongRed.

Section SigmaCongValidity.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G' l}
    (VΓ : [||-v Γ])
    (VF : [ Γ ||-v< l > F | VΓ ])
    (VG : [ Γ ,, F ||-v< l > G | validSnoc VΓ VF ])
    (VF' : [ Γ ||-v< l > F' | VΓ ])
    (VG' : [ Γ ,, F' ||-v< l > G' | validSnoc VΓ VF' ])
    (VFF' : [ Γ ||-v< l > F ≅ F' | VΓ | VF ])
    (VGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF | VG ]).

  Lemma SigValid : [Γ ||-v< l > tSig F G | VΓ].
  Proof.
    unshelve econstructor; intros; [now eapply SigRed|].
    eapply SigCongRed; tea; now eapply reflValidTy.
  Qed.

  Lemma SigCong : [ Γ ||-v< l > tSig F G ≅ tSig F' G' | VΓ | SigValid ].
  Proof. econstructor; intros; irrelevanceRefl; now unshelve now eapply SigCongRed. Qed.

End SigmaCongValidity.

Lemma up_subst_single {t σ a} : t[up_term_term σ][a..] = t[a .: σ].
Proof. now asimpl. Qed.

Lemma wk_id_shift {t a Γ} : t[a .: @wk_id Γ >> tRel] = t[a..].
Proof. now bsimpl. Qed.

Lemma split_valid_subst_wk_id {Γ G σ} :
 G[σ] = G[up_term_term (↑ >> σ)][σ var_zero .: (@wk_id Γ) >> tRel].
Proof.  now rewrite wk_id_shift, up_subst_single, scons_eta'. Qed.

Section SigInjValid.
  Context `{GenericTypingProperties}.
  Context {l Γ F G} (VΓ : [||-v Γ]) (VΣ : [Γ ||-v<l> tSig F G | VΓ]).

  Lemma domSigValid : [Γ ||-v<l> F | VΓ].
  Proof.
    unshelve econstructor.
    - intros ???? Vσ; instValid Vσ.
      apply (polyRedId (normRedΣ0 (invLRΣ RVΣ))).
    - intros ???? Vσσ' ; instValid Vσσ'.
      set (P := (polyRedId _)); destruct P.
      pose (X := normEqRedΣ _ REVΣ); fold subst_term in *.
      irrelevanceRefl; apply (polyRedEqId _ X).
  Qed.

  Lemma codSigValid : [Γ,, F ||-v<l> G | validSnoc VΓ domSigValid ].
  Proof.
    pose (domSigValid).
    assert (h : forall (Δ : context) (wfΔ : [ |-[ ta ] Δ]) (σ σ' : nat -> term),
      [validSnoc VΓ domSigValid | Δ ||-v σ ≅ σ' : Γ,, F | wfΔ] -> [Δ ||-< l > G[σ]]).
    1:{
      intros ? wfΔ ?? Vσ; instValid (eqTail Vσ).
      pose (p := normRedΣ0 (invLRΣ RVΣ)); fold subst_term in *.
      erewrite split_valid_subst_wk_id.
      unshelve eapply (PolyRed.posRed p (wk_id) wfΔ).
      2: irrelevance0; [|exact (eqHead Vσ)]; now rewrite wk_id_ren_on.
    }
    unshelve econstructor; tea.
    intros ? wfΔ ?? Vσσ' ; instValid (eqTail Vσσ').
    pose (p := normRedΣ0 (invLRΣ RVΣ));
    pose (q := normEqRedΣ _ REVΣ); fold subst_term in *.
    irrelevance0.
    1: now erewrite split_valid_subst_wk_id.
    assert [PolyRed.shpRed p wk_id wfΔ | Δ ||- σ' var_zero : (ParamRedTy.dom p)⟨wk_id⟩].
    1:{
      eapply LRTmEqConv.
      2: exact (urefl (eqHead Vσσ')).
      rewrite wk_id_ren_on; cbn.
      now eapply reflLRTyEq.
    }
    eapply transEq; cycle 1.
    + erewrite split_valid_subst_wk_id.
      unshelve eapply (PolyRedEq.posRed q wk_id wfΔ).
      2: irrelevance.
    + unshelve eapply (PolyRed.posExt p wk_id wfΔ); tea.
      irrelevance0; [|exact (eqHead Vσσ')]; now rewrite wk_id_ren_on.
  Qed.

End SigInjValid.



Section SigTmValidity.
  Context `{GenericTypingProperties}.

  Section Lemmas.
  Context {Γ F  F' G  G'} {VΓ : [||-v Γ]}
    {VF : [ Γ ||-v< one > F | VΓ ]}
    (VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ])
    (VFeqU : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ])
    (VGeqU : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc VΓ VF | VU ]).


  Lemma sigTmEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ ])
    : [Δ |-[ ta ] tSig F[σ] G[up_term_term σ] ≅ tSig F'[σ'] G'[up_term_term σ'] : U].
  Proof.
    pose proof (Vuσ := liftSubstEq' VF Vσσ').
    instValid Vσσ'; instValid Vuσ; escape.
    eapply convtm_sig; tea.
  Qed.


  Lemma SigURedTm {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
    : URedTm (LogRelRec _) Δ (tSig F G)[σ] U (redUOneCtx tΔ).
  Proof.
    pose proof (Vuσσ := liftSubstEq' VF Vσ); instValid Vσ ; instValid Vuσσ; escape.
    econstructor; [eapply redtmwf_refl; cbn; now eapply ty_sig|constructor].
  Defined.
  End Lemmas.

  Context {Γ F  F' G  G'} {VΓ : [||-v Γ]}
    {VF : [ Γ ||-v< one > F | VΓ ]}
    {VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ]}
    (VFeqU : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ])
    (VFU := lreflValidTm _ VFeqU)
    (VGeqU : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc VΓ VF | VU ])
    (VGU := lreflValidTm _ VGeqU).

  Lemma SigCongRedU {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
    : [ Δ ||-< one > (tSig F G)[σ] ≅ (tSig F' G')[σ'] : U | validTy (UValid VΓ) tΔ Vσ ].
  Proof.
    pose proof (Vuσσ := liftSubstEq' VF Vσ); instValid Vσ ; instValid Vuσσ; escape.
    set (RΣ := SigURedTm VU VFeqU VGeqU tΔ Vσ).
    pose proof (symValidTmEq VFeqU).
    epose proof (VF' := univValid _ _ (ureflValidTm VFeqU)).
    epose proof (VFF' := univEqValid _ _ VF VFeqU).
    epose proof (VGU' := convTmEqCtx1 _ _ (validSnoc VΓ VF') VF _ (UValid _) VFF' (ureflValidTm VGeqU)).
    set (RΣ' := SigURedTm (UValid _) (ureflValidTm VFeqU) VGU' tΔ (urefl Vσ)).
    unshelve eexists RΣ RΣ' _.
    - unshelve (eapply RedTyRecBwd, LRCumulative, SigRed; [| tea]).
      all: unshelve (eapply univValid, lreflValidTm; irrValid); eapply UValid.
    - eapply convtm_sig; refold; tea; now eapply lrefl.
    - unshelve (eapply RedTyRecBwd, LRCumulative, SigRed; [| now eapply urefl]).
      all: unshelve (eapply univValid, lreflValidTm; irrValid); eapply UValid.
    - irrelevanceCum0; [reflexivity|].
      unshelve (eapply SigCongRed; tea; [now eapply univValid| now eapply univEqValid]); tea.
      unshelve (eapply univValid, lreflValidTm; irrValid); eapply UValid.
  Qed.

  Lemma SigCongValidU : [ Γ ||-v< one > tSig F G ≅ tSig F' G' : U | VΓ | UValid VΓ ].
  Proof. econstructor; intros Δ tΔ  σ σ' Vσσ'; eapply SigCongRedU. Qed.

End SigTmValidity.


Section SigRedTmEqHelper.
  Import SigRedTmEq.
  Context `{GenericTypingProperties}.

  Lemma isLRPair_isWfPair {Γ A B l p} (ΣA : [Γ ||-Σ<l> tSig A B])
    (RA : [Γ ||-<l> A])
    (RΣ := (normRedΣ0 ΣA))
    (Rp : isLRPair RΣ p) :
      isWfPair Γ A B p.
  Proof.
    assert (wfΓ: [|- Γ]) by (escape ; gen_typing).
    destruct Rp as [???? eqA eqB rfst rsnd|].
    2: now econstructor.
    pose proof (RFA := instKripkeEq wfΓ eqA).
    pose proof (LRTyEqRedRight _ RFA).
    pose proof (instKripkeSubstConv wfΓ eqA (PolyRed.posRed RΣ)).
    pose proof (instKripkeSubstConvEq wfΓ eqA eqB).
    pose proof (Ra := instKripkeTmEq wfΓ rfst).
    pose proof (instKripkeSubstEq wfΓ eqB).
    pose proof (polyCodSubstRed _ RΣ _ _ Ra).
    unshelve epose proof (hB:=eqB _ _ _ (@wk_id Γ) wfΓ _).
    3: irrelevance0; [| exact Ra]; now rewrite wk_id_ren_on.
    pose proof (polyCodSubstExtRed _ RΣ _ _ Ra).
    epose proof (hb := rsnd _ wk_id wfΓ).
    cbn -[wk_id] in *.
    escape.
    rewrite 2!subst_wk_id_tail in EschB.
    rewrite subst_wk_id_tail in EscRhB, Rlhb.
    rewrite 2!wk_id_ren_on in Rlhb.
    now econstructor.
  Qed.


  Context {Γ l A} (RA : [Γ ||-Σ<l> A])
    {t u} (Rt : SigRedTm RA t) (Ru : SigRedTm RA u).

  (* Let Rout : [Γ ||-Σ<l> RA.(ParamRedTy.outTy)].
  Proof.
    apply normRedΣ0.
    econstructor; [eapply redtywf_refl|..]; destruct RA; tea.
    cbn in *; gen_typing.
  Defined. *)

  Lemma build_sigRedTmEq
    (eqnf : [Γ |- nf Rt ≅ nf Ru : ParamRedTy.outTy RA])
    (Rdom := fst (polyRedId RA))
    (Rfst : [ Rdom | _ ||- tFst (nf Rt) ≅ tFst (nf Ru) : _ ])
    (Rcod := polyCodSubstRed Rdom RA _ _ Rfst)
    (Rsnd : [ Rcod | _ ||- tSnd (nf Rt) ≅ tSnd (nf Ru) : _ ]) :
    [LRSig' RA | _ ||- t ≅ u : _].
  Proof.
    unshelve eexists Rt Ru _; tea.
    - intros; unshelve (irrelevanceRefl; rewrite 2!wk_fst; now eapply wkTermEq); tea.
    - intros; irrelevance0.
      2: unshelve (rewrite 2!wk_snd; now eapply wkTermEq); tea.
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

  (* Lemma build_sigRedTmEq'
    (eqnf : [Γ |- nf Rt ≅ nf Ru : ParamRedTy.outTy RA])
    (Rdom := fst (polyRedId RA))
    (Rfst : [ Rdom | _ ||- tFst t ≅ tFst u : _ ])
    (Rcod := polyCodSubstRed Rdom RA _ _ Rfst)
    (Rsnd : [ Rcod | _ ||- tSnd t ≅ tSnd u : _ ]) :
    [LRSig' RA | _ ||- t ≅ u : _].
  Proof.
    unshelve eapply build_sigRedTmEq; tea.
    - dependent inversion Rt; dependent inversion Ru; eapply redTmEqFwdBoth.
      2,3: cbn in *; now eapply redtmwf_fst.
      1: tea.
      cbn; constructor.
      3:{ cbn in *. tea. }
    try solve [constructor]. *)

End SigRedTmEqHelper.

Section SigRedTmEqHelper.
  Context `{GenericTypingProperties}.
  Import SigRedTmEq.

  Lemma build_sigRedTmEq' {Γ l F G}
    (RΣ0 : [Γ ||-Σ<l> tSig F G])
    (RΣ := normRedΣ0 RΣ0)
    {t u} (Rt : SigRedTm RΣ t) (Ru : SigRedTm RΣ u)
    (Rdom := fst (polyRedId RΣ))
    (Rfst : [ Rdom | _ ||- tFst (nf Rt) ≅ tFst (nf Ru) : _ ])
    (Rcod := polyCodSubstRed Rdom RΣ _ _ Rfst)
    (Rsnd : [ Rcod | _ ||- tSnd (nf Rt) ≅ tSnd (nf Ru) : _ ]) :
    [LRSig' RΣ | _ ||- t ≅ u : _].
  Proof.
    eapply build_sigRedTmEq; tea.
    cbn; destruct (polyRedId RΣ); escape; eapply convtm_eta_sig; tea.
    2,4: eapply isLRPair_isWfPair; [| eapply ispair]; tea.
    + destruct Rt; cbn in *; gen_typing.
    + destruct Ru; cbn in *; gen_typing.
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

  Lemma sigRedTmEqNf {l Δ F G p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (Rp : [Δ ||-<l> p ≅ p' : _ | LRSig' (normRedΣ0 RΣ)]) :
    [Δ ||-<l> p ≅ Rp.(redL).(nf) : _ | LRSig' (normRedΣ0 RΣ)].
  Proof.
    symmetry; eapply redTmEqFwd.
    + eapply lrefl; irrelevance.
    + eapply Rp.(redL).(red).
    + eapply whnf.
  Qed.


  Lemma fstRed {l Δ F G p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (RF : [Δ ||-<l> F])
    (Rp : [Δ ||-<l> p ≅ p' : _ | LRSig' (normRedΣ0 RΣ)]) :
    [Δ ||-<l> tFst p ≅ tFst p' : _ | RF].
  Proof.
    eapply redSubstTmEq; cycle 1.
    + eapply redtm_fst, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
    + eapply redtm_fst, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    + cbn; now unshelve eapply escapeEq, reflLRTyEq.
    + irrelevanceRefl; eapply instKripkeTmEq.
      intros ? ρ h; rewrite <- 2!wk_fst; eapply (SigRedTmEq.eqFst Rp).
      Unshelve. all: escape; gen_typing.
  Qed.

  Lemma sndRed {l Δ F G} {p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (RF : [Δ ||-<l> F])
    (RΣn := LRSig' (normRedΣ0 RΣ))
    (Rp : [Δ ||-<l> p ≅ p' : _ | LRSig' (normRedΣ0 RΣ)])
    (RGfstp : [Δ ||-<l> G[(tFst p)..]]) :
    [Δ ||-<l> tSnd p ≅ tSnd p' : _ | RGfstp].
  Proof.
    eapply redSubstTmEq; cycle 1.
    + eapply redtm_snd, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
    + eapply redtm_snd, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    + epose proof (singleSubstEqΣ (fstRed RΣ RF Rp) RGfstp); cbn; now escape.
    + irrelevanceRefl.
      assert (wfΔ : [|- Δ]) by (escape; gen_typing).
      pose proof (fstRed RΣ RF (sigRedTmEqNf RΣ Rp)).
      erewrite <- wk_id_ren_on, <- (wk_id_ren_on  _ (tSnd (SigRedTmEq.nf (SigRedTmEq.redL _)))), <-2!wk_snd.
      eapply LRTmEqConv; [| eapply (SigRedTmEq.eqSnd Rp wk_id wfΔ)].
      symmetry in X.
      cbn -[wk_id]; irrelevance0.
      2: exact (singleSubstEqΣ (RFG:=LRSig' RΣ) X (singleSubstΣ1 (LRSig' RΣ) X)).
      now rewrite subst_wk_id_tail, wk_id_ren_on.
      Unshelve. 2,4: tea.
  Qed.

  Context {l Γ F G } (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ,, F ||-v< l > G | validSnoc VΓ VF])
    (VΣ := SigValid VΓ VF VG).

  Lemma fstValid {p p'} (Vp : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ]):
    [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VF].
  Proof.
    constructor; intros; cbn; instValid Vσσ'.
    unshelve (eapply fstRed; irrelevance); now apply invLRΣ.
  Qed.

  Lemma subst_fst {t σ} : tFst t[σ] = (tFst t)[σ].
  Proof. reflexivity. Qed.

  Lemma sndValid {p p'} (Vp : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ])
    (VGfst := substS VG (fstValid Vp)) :
    [Γ ||-v<l> tSnd p ≅ tSnd p' : _ | VΓ | VGfst].
  Proof.
    constructor; intros; cbn; instValid Vσσ'.
    unshelve (irrelevance0; [|eapply sndRed; [| irrelevance]; tea]).
    all:refold. 3: now rewrite singleSubstComm'.
    2: now apply invLRΣ.
    now rewrite subst_fst, <- singleSubstComm'.
  Qed.

End ProjRed.



Section PairRed.
  Context `{GenericTypingProperties}.

  Lemma pairFstRed {Γ A A' B B' a a' b b' l}
    (RA : [Γ ||-<l> A])
    (RAA : [Γ ||-<l> A ≅ A' | RA])
    (RB : [Γ ,, A ||-<l> B])
    (RB' : [Γ ,, A' ||-<l> B'])
    (RBa : [Γ ||-<l> B[a..]])
    (RBB : [Γ ||-<l> B[a..] ≅ B'[a'..] | RBa ])
    (Ra : [Γ ||-<l> a ≅ a' : A | RA])
    (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
    [Γ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA].
  Proof.
    pose proof (LRTyEqRedRight RA RAA).
    escape.
    eapply redSubstTmEq; tea.
    1,2: eapply redtm_fst_beta; tea; now eapply ty_conv.
  Qed.

  Lemma pairSndRed {Γ A A' B B' a a' b b' l}
    (RA : [Γ ||-<l> A])
    (RAA : [Γ ||-<l> A ≅ A' | RA])
    (RB : [Γ ,, A ||-<l> B])
    (RB' : [Γ ,, A' ||-<l> B'])
    (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ])
    (RBBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ≅ B'[(tFst (tPair A' B' a' b'))..] | RBfst])
    (RBa : [Γ ||-<l> B[a..]])
    (RBfsta : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa])
    (RBB : [Γ ||-<l> B[a..] ≅ B'[a'..] | RBa ])
    (Ra : [Γ ||-<l> a ≅ a' : A | RA])
    (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
    [Γ ||-<l> tSnd (tPair A B a b) ≅ tSnd (tPair A' B' a' b') : _ | RBfst ].
  Proof.
    pose proof (LRTyEqRedRight RA RAA).
    (* pose proof (LRTyEqRedRight _ RBBfst). *)
    escape.
    eapply redSubstTmEq; tea.
    1: now eapply LRTmEqConv.
    1,2: eapply redtm_snd_beta; tea; now eapply ty_conv.
  Qed.

  Import SigRedTmEq.

  (* #[program]
  Definition pairSigRedTm {Γ A B a b l}
    (RΣ0 : [Γ ||-Σ<l> tSig A B])
    (RΣ := normRedΣ0 RΣ0)
    (RA : [Γ ||-<l> A])
    (RBa : [Γ ||-<l> B[a..]])
    (Ra : [Γ ||-<l> a : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ]) :
    SigRedTm RΣ (tPair A B a b) := {| nf := tPair A B a b |}.
  Next Obligation.
    destruct (polyRedId (normRedΣ0 RΣ0)); escape.
    eapply redtmwf_refl; cbn; now eapply ty_pair.
  Qed.
  Next Obligation.
    unshelve econstructor; intros; cbn.
    * irrelevanceCumRefl; now eapply wkTermEq.
    * eapply reflLRTyEq.
    * irrelevanceRefl.
      unshelve eapply (PolyRed.posExt (normRedΣ0 RΣ0)); tea.
    * irrelevanceCum0.
      2: now eapply wkTermEq.
      clear; now bsimpl.
    Unshelve. all: tea.
  Qed. *)

  Set Printing Universes.

  Obligation Tactic :=  idtac.
  #[program]
   Definition pairSigRedTm@{i j k l} {Γ F G A B a b l}
    (RΣ0 : ParamRedTy@{i j k l} tSig Γ l (tSig F G))
    (RΣ := normRedΣ0@{i j k l} RΣ0)
    (RΣ' := LRSig'@{i j k l} RΣ)
    (RAB : [_ ||-<l> _ ≅ tSig A B | RΣ'])
    (Rdom : [LogRel@{i j k l} l | Γ ||- F])
    (Rcoda : [LogRel@{i j k l} l | Γ ||- G[a..]])
    (Rcod := snd@{l l} (polyRedId RΣ))
    (Ra : [Γ ||-<l> a : _ | Rdom])
    (Rb : [Γ ||-<l> b : _ | Rcoda ])
    (RA : [_ ||-<l> _ ≅ A | Rdom])
    (RBa : [_ ||-<l> _ ≅ B[a..] | Rcoda]) :
     SigRedTm RΣ (tPair A B a b) :=
  {| nf := tPair A B a b |}.
  Next Obligation.
    intros.
    destruct (polyRedId (normRedΣ0 (invLRΣ (LRTyEqRedRight _ RAB)))).
    eapply redtmwf_refl; cbn; eapply ty_conv.
    2: now (symmetry; eapply escapeEq).
    eapply ty_pair; first [now eapply escape| eapply ty_conv; [now eapply escapeTerm| now eapply escapeEq]].
  Qed.
  Next Obligation.
    unshelve econstructor; intros; cbn.
      1-3:irrelevanceRefl.
      * now eapply wkTermEq.
      * now eapply wkEq.
      * unshelve eapply (posRedExt (normEqRedΣ _ RAB)); tea; irrelevance.
      * irrelevance0.
        2: now eapply wkTermEq.
        clear; now bsimpl.
        Unshelve. all: tea.
  Qed.

   Definition pairSigRedTm0@{i j k l} {Γ A B a b l}
    (RΣ0 : ParamRedTy@{i j k l} tSig Γ l (tSig A B))
    (RΣ := normRedΣ0@{i j k l} RΣ0)
    (RΣ' := LRSig'@{i j k l} RΣ)
    (RA : [LogRel@{i j k l} l | Γ ||- A])
    (RBa : [LogRel@{i j k l} l | Γ ||- B[a..]])
    (* (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ]) *)
    (Ra : [Γ ||-<l> a : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ]) :
     SigRedTm RΣ (tPair A B a b).
  Proof.
    unshelve eapply pairSigRedTm; tea; eapply reflLRTyEq.
  Defined.

  Lemma pairCongRed0 {Γ A A' B B' a a' b b' l}
    (RΣ0 : [Γ ||-Σ<l> tSig A B])
    (RΣ := normRedΣ0 RΣ0)
    (RΣ' := LRSig' RΣ)
    (RΣeq : [_ ||-<l> _ ≅ tSig A' B' | RΣ'])
    (RA : [Γ ||-<l> A])
    (RA' : [Γ ||-<l> A'])
    (RBa : [Γ ||-<l> B[a..]])
    (RBconv : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ])
    (Ra : [Γ ||-<l> a ≅ a' : A | RA])
    (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
    [Γ ||-<l> tPair A B a b ≅ tPair A' B' a' b' : _ | RΣ'].
  Proof.
    pose proof (RBa' := polyCodSubstRed RA RΣ _ _ (urefl Ra)).
    destruct (polyRedId RΣ) as [_ ?].
    destruct (polyRedId (normRedΣ0 (invLRΣ (LRTyEqRedRight _ RΣeq)))).
    destruct (polyRedEqId _ (normEqRedΣ _ RΣeq)) as [? ?].
    assert (RAA' : [RA | _ ||- _ ≅ A']) by irrelevance.
    epose proof (RBaeq := polyCodSubstExtRed _ RΣ _ _ Ra).
    epose proof (polyRedEqCodSubstExt _ _ (normEqRedΣ _ RΣeq) _ _ (urefl Ra)).
    assert (RBBa' : [RBa' | _ ||- _ ≅ B'[a'..]]) by irrelevance.
    epose proof (polyRedEqCodSubstExt _ _ (normEqRedΣ _ RΣeq) _ _ Ra).
    cbn in RBaeq.
    assert (Rb' : [_ ||-<l> b' : _ | RBa']) by (eapply LRTmEqConv; tea; eapply urefl; irrelevance).
    escape.
    set (Rpair := pairSigRedTm0 RΣ0 RA RBa (lrefl Ra) (lrefl Rb)).
    set (Rpair' := pairSigRedTm RΣ0 RΣeq RA RBa' (urefl Ra) Rb' RAA' RBBa').
    assert [RA | _ ||- tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _].
    1:{
     eapply redSubstTmEq; tea.
      all: eapply redtm_fst_beta; tea; cbn; eapply ty_conv; tea.
    }
    unshelve eapply (build_sigRedTmEq' _ Rpair Rpair'); subst Rpair Rpair'; cbn.
    1: irrelevance.
    eapply redSubstTmEq.
    2,3: eapply redtm_snd_beta; tea; now eapply ty_conv.
    1: now eapply LRTmEqConv.
    cbn; unshelve eapply escapeEq, (polyRedEqCodSubstExt _ _ (normEqRedΣ _ RΣeq)); tea.
  Qed.

  (* Lemma pairRed0 {Γ A B a b l}
    (RΣ0 : [Γ ||-Σ<l> tSig A B])
    (RΣ := normRedΣ0 RΣ0)
    (RΣ' := LRSig' RΣ)
    (RA : [Γ ||-<l> A])
    (RBa : [Γ ||-<l> B[a..]])
    (RBconv : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ])
    (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ])
    (Ra : [Γ ||-<l> a : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ]) :
    [Γ ||-<l> tPair A B a b : _ | RΣ'].
  Proof.
    destruct (polyRedId RΣ) as [_ ?]; escape.
    set (Rpair := pairSigRedTm RΣ0 RA RBa Ra Rb).
    unshelve eapply (build_sigRedTmEq' _ Rpair Rpair); subst Rpair; cbn.
    + eapply redSubstTmEq.
      2,3: now eapply redtm_fst_beta.
      1: irrelevanceCum.
      now unshelve eapply escapeEq, reflLRTyEq.
    + eapply redSubstTmEq.
      2,3: now eapply redtm_snd_beta.
      1: now eapply LRTmEqConv.
      now unshelve eapply escapeEq, reflLRTyEq.
  Qed.

  Lemma pairRed {Γ A B a b l}
    (RΣ0 : [Γ ||-Σ<l> tSig A B])
    (RΣ := normRedΣ0 RΣ0)
    (RΣ' := LRSig' RΣ)
    (RA : [Γ ||-<l> A])
    (RBa : [Γ ||-<l> B[a..]])
    (Ra : [Γ ||-<l> a : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ]) :
    [Γ ||-<l> tPair A B a b : _ | RΣ'].
  Proof.
    assert [_ ||-<l> a ≅ tFst (tPair A B a b) : _ | RA].
    1:{ symmetry; eapply redSubstLeftTmEq; tea .
      destruct (polyRedId RΣ) as [_ ?]; escape.
      now eapply redtm_fst_beta. }
    eapply pairRed0; tea.
    + now unshelve now eapply singleSubstEqΣ.
    + eapply singleSubstΣ1; tea; now symmetry.
  Qed. *)

  Lemma sigEtaRed {Γ A B l p p'}
    (RΣ0 : [Γ ||-Σ<l> tSig A B])
    (RΣn := normRedΣ0 RΣ0)
    (RΣ := LRSig' RΣn)
    (RA : [Γ ||-<l> A])
    (RBfst : [Γ ||-<l> B[(tFst p)..]])
    (Rp : [Γ ||-<l> p : _ | RΣ])
    (Rp' : [Γ ||-<l> p' : _ | RΣ])
    (Rfstpp' : [Γ ||-<l> tFst p ≅ tFst p' : _ | RA])
    (Rsndpp' : [Γ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]) :
    [Γ ||-<l> p ≅ p' : _ | RΣ].
  Proof.
    assert (RBfst' : [Γ ||-<l> B[(tFst p')..]]).
    1: eapply singleSubstΣ1; tea; now symmetry.
    pose proof (Rpnf := sigRedTmEqNf _ Rp).
    pose proof (Rpnf' := sigRedTmEqNf _ Rp').
    pose proof (fstRed _ RA Rpnf).
    pose proof (fstRed _ RA Rpnf').
    unshelve eapply (build_sigRedTmEq' _ Rp.(redL) Rp'.(redL)).
    - transitivity (tFst p); [symmetry|transitivity (tFst p')]; irrelevance.
    - pose proof (sndRed _ RA Rpnf RBfst).
      pose proof (sndRed _ RA Rpnf' RBfst').
      unshelve (eapply LRTmEqConv; [cbn; now unshelve now eapply singleSubstEqΣ|]); tea.
      transitivity (tSnd p); [symmetry |transitivity (tSnd p')].
      1,2: irrelevance.
      eapply LRTmEqConv; tea.
      now unshelve (eapply singleSubstEqΣ; now symmetry).
  Qed.



  Lemma subst_sig {A B σ} : (tSig A B)[σ] = (tSig A[σ] B[up_term_term σ]).
  Proof. reflexivity. Qed.

  Lemma subst_pair {A B a b σ} : (tPair A B a b)[σ] = (tPair A[σ] B[up_term_term σ] a[σ] b[σ]).
  Proof. reflexivity. Qed.

  Lemma subst_snd {p σ} : (tSnd p)[σ] = tSnd p[σ].
  Proof. reflexivity. Qed.

  Lemma up_subst_single' t a σ : t[up_term_term σ][(a[σ])..] = t[a..][σ].
  Proof. now bsimpl. Qed.

  Lemma pairFstValid0 {Γ A B a b l}
    (VΓ : [||-v Γ])
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
    instValid Vσσ'; instValid (liftSubstEq' VA Vσσ'); escape.
    eapply redtm_fst_beta; tea.
    now rewrite up_subst_single'.
  Qed.

  Lemma pairFstValid {Γ A B a b l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tFst (tPair A B a b) : _ | VΓ | VA] ×
    [Γ ||-v<l> tFst (tPair A B a b) ≅ a : _ | VΓ | VA].
  Proof.
    split; [eapply lreflValidTm|]; now eapply pairFstValid0.
  Qed.

  Lemma pairSndValid0 {Γ A B a b l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa])
    (Vfstall := pairFstValid VΓ VA VB Va Vb)
    (VBfst := substS VB (fst Vfstall)) :
    [Γ ||-v<l> tSnd (tPair A B a b) ≅ b : _ | VΓ | VBfst].
  Proof.
    eapply redSubstValid; cycle 1.
    + eapply conv; tea.
      pose proof (h := symValidTmEq (pairFstValid0 VΓ VA VB Va Vb)).
      epose proof (substSEq (reflValidTy VA) (reflValidTy VB) h).
      irrValid.
    + constructor; intros.
      rewrite <-up_subst_single', subst_snd, <-subst_fst, subst_pair.
      instValid Vσσ'; instValid (liftSubstEq' VA Vσσ'); escape.
      eapply redtm_snd_beta; tea.
      now rewrite up_subst_single'.
  Qed.


  Lemma pairSndValid {Γ A B a b l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa])
    (Vfstall := pairFstValid VΓ VA VB Va Vb)
    (VBfst := substS VB (fst Vfstall)) :
    [Γ ||-v<l> tSnd (tPair A B a b) : _ | VΓ | VBfst] ×
    [Γ ||-v<l> tSnd (tPair A B a b) ≅ b : _ | VΓ | VBfst].
  Proof.
    split; [eapply lreflValidTm|]; now eapply pairSndValid0.
  Qed.

  Lemma pairCongValid {Γ A A' B B' a a' b b' l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VA' : [ Γ ||-v<l> A ≅ A' | VΓ | VA])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA ])
    (VBB' : [ Γ ,, A ||-v<l> B ≅ B' | validSnoc VΓ VA | VB])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a ≅ a' : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b ≅ b' : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tPair A B a b ≅ tPair A' B' a' b' : _ | VΓ | VΣ].
  Proof.
    constructor; intros; rewrite 2!subst_pair.
    assert [_ ||-v<l> tSig A B ≅ tSig A' B' | VΓ | VΣ].
    1:{
      eapply SigCong; tea.
      eapply convCtx1; tea; now eapply ureflValidTy.
    }
    instValid Vσσ'; instValid (liftSubstEq' VA Vσσ').
    irrelevance0; [now rewrite subst_sig|].
    eapply pairCongRed0; tea.
    + irrelevance.
    +
      pose proof (lreflValidTm _ Vb).
      unshelve epose proof (Rafst := symValidTmEq (pairFstValid0 VΓ VA VB (lreflValidTm _ Va) _)).
      2: irrValid.
      pose proof (RBaBfst := substSEq (reflValidTy VA) (reflValidTy VB) Rafst).
      pose proof (validTyEq RBaBfst _ (lrefl Vσσ')).
      rewrite <-subst_pair, subst_fst, up_subst_single'; irrelevance.
    + irrelevance.
    Unshelve.
    1: now eapply ureflValidTy.
    1:  rewrite <-subst_sig; now apply invLRΣ.
    now rewrite up_subst_single'.
  Qed.

  Lemma pairValid {Γ A B a b l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tPair A B a b : _ | VΓ | VΣ].
  Proof.
    eapply pairCongValid; tea; now eapply reflValidTy.
  Qed.

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
    instValid Vσσ'.
    irrelevance0; [now rewrite subst_sig|].
    eapply sigEtaRed; try irrelevance.
    + eapply lrefl; irrelevance.
    + eapply urefl; irrelevance.
    Unshelve.
    2: rewrite <- subst_sig; now apply invLRΣ.
    1: tea.
    now rewrite subst_fst, up_subst_single'.
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
    pose proof (pairFstValid0 _ _ _ Vfst Vsnd).
    pose proof (pairSndValid0 _ _ _ Vfst Vsnd).
    pose proof (pairValid _ _ _ Vfst Vsnd).
    unshelve eapply sigEtaEqValid; tea; try irrValid.
  Qed.

End PairRed.




