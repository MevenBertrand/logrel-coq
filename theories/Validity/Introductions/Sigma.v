From Coq Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Poly Sigma.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly ValidityTactics.


Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaCongRed.

Context `{GenericTypingProperties}.

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

  Lemma SigRedU {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
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

  Lemma SigValidU : [ Γ ||-v< one > tSig F G ≅ tSig F' G' : U | VΓ | UValid VΓ ].
  Proof. econstructor; intros Δ tΔ  σ σ' Vσσ'; eapply SigRedU. Qed.

End SigTmValidity.


Section ProjRed.
  Context `{GenericTypingProperties}.

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




