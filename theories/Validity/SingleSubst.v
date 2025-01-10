From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity NormalRed.
From LogRel.Validity Require Import Validity Irrelevance Properties Conversion Reflexivity.

Set Universe Polymorphism.

Section SingleSubst.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma singleSubstComm G t σ : G[t..][σ] = G[t[σ] .: σ].
Proof. now asimpl. Qed.


Lemma substS {Γ F G t t' l} {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VG : [Γ,, F ||-v<l> G | validSnoc VΓ VF])
  (Vt : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] | VΓ].
Proof.
  opector; intros; rewrite singleSubstComm.
  - unshelve eapply validTy.
    6: now eapply consSubstEqvalid.
    tea.
  - irrelevance0. 1: symmetry; apply singleSubstComm.
    unshelve eapply validTyExt.
    5: now eapply consSubstEqvalid, lreflValidTm.
    tea.
Qed.

Lemma substSEq {Γ F F' G G' t t' l} {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ,, F ||-v<l> G | VΓF]}
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF])
  (VGt := substS VG Vtt') :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ | VGt].
Proof.
  constructor; intros.
  rewrite singleSubstComm; irrelevance0.
  1: symmetry; apply singleSubstComm.
  unshelve now eapply validTyEq.
  2: now eapply consSubstEqvalid.
Qed.

Lemma substSTmEq {Γ F F' G G' t t' f f' l} (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF])
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF])
  (Vff' : [Γ ,, F ||-v<l> f ≅ f' : G | VΓF | VG]) :
  [Γ ||-v<l> f[t..] ≅ f'[t'..] : G[t..] | VΓ | substS VG Vtt'].
Proof.
  constructor; intros; rewrite !singleSubstComm; irrelevance0.
  1: symmetry; apply singleSubstComm.
  unshelve now eapply validTmEq.
  1: tea.
  now unshelve now eapply consSubstEq, validTmEq.
Qed.

Lemma substSTm {Γ F G t f l} {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ,, F ||-v<l> G | VΓF]}
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Vf : [Γ ,, F ||-v<l> f : G | VΓF | VG])
  (VGt := substS VG Vt) :
  [Γ ||-v<l> f[t..] : G[t..] | VΓ | VGt].
Proof. eapply substSTmEq; tea; now eapply reflValidTy. Qed.


Lemma liftSubstComm G t σ : G[t]⇑[σ] = G[t[σ] .: ↑ >> σ].
Proof. now bsimpl. Qed.

Lemma substLiftS {Γ F G t l} (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF])
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']) :
  [Γ ,, F ||-v<l> G[t]⇑ | VΓF].
Proof.
  assert (h : forall Δ σ σ' (wfΔ: [|- Δ])
    (vσσ': [VΓF | Δ ||-v σ ≅ σ' : Γ,, F | wfΔ]),
    [VΓF | Δ ||-v (t[σ] .: ↑ >> σ) ≅ (t[σ'] .: ↑ >> σ') : _ | wfΔ ]).
  1:{
    unshelve econstructor.
    + asimpl; now eapply eqTail.
    + cbn. irrelevance0.
      2: now eapply validTmExt.
      now bsimpl.
  }
  opector; intros; rewrite liftSubstComm.
  - unshelve eapply validTy.
    6: now eapply h.
    tea.
  - irrelevance0.
    2: unshelve eapply validTyExt.
    7: now eapply h.
    2: tea.
    now bsimpl.
    Unshelve. all:tea.
Qed.

Lemma substLiftSEq {Γ F G G' t l} (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF])
  (VG' : [Γ,, F ||-v<l> G' | VΓF])
  (VGeq : [Γ,, F ||-v<l> G ≅ G' | VΓF | VG])
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t]⇑ | VΓF | substLiftS _ VF VG Vt].
Proof.
  constructor; intros; rewrite liftSubstComm.
  assert (Vσt : [Δ ||-v (t[σ] .: ↑ >> σ) ≅ (t[σ'] .: ↑ >> σ') : _ | VΓF | wfΔ ]). 1:{
    unshelve econstructor.
    + bsimpl. now eapply eqTail.
    + cbn; instValid Vσσ'; irrelevance.
  }
  instValid Vσt. irrelevance.
Qed.

Lemma substLiftSEq' {Γ F G G' t t' l} (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF])
  (VG' : [Γ,, F ||-v<l> G' | VΓF])
  (VGeq : [Γ,, F ||-v<l> G ≅ G' | VΓF | VG])
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF'])
  (Vt' : [Γ,, F ||-v<l> t' : F⟨@wk1 Γ F⟩ | VΓF | VF'])
  (Vtt' : [Γ,, F ||-v<l> t ≅ t' : F⟨@wk1 Γ F⟩ | VΓF | VF']) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t']⇑ | VΓF | substLiftS _ VF VG Vt].
Proof.
  constructor; intros; rewrite liftSubstComm.
  assert (Vσt : [Δ ||-v (t[σ] .: ↑ >> σ) ≅ (t'[σ'] .: ↑ >> σ') : _ | VΓF | wfΔ ]). 1:{
    unshelve econstructor.
    + bsimpl. now eapply eqTail.
    + cbn; instValid Vσσ'; irrelevance.
  }
  instValid Vσt. irrelevance.
Qed.


Lemma singleSubstPoly {Γ F G t u l lF}
  (RFG : PolyRed Γ l F G)
  {RF : [Γ ||-<lF> F]}
  (Rt : [Γ ||-<lF> t ≅ u : F | RF]) :
  [Γ ||-<l> G[t..]].
Proof.
  replace G[t..] with G[t .: wk_id (Γ:=Γ) >> tRel] by now bsimpl.
  unshelve eapply (PolyRed.posRed RFG).
  2: escape; gen_typing.
  2: irrelevance0; tea.
  now bsimpl.
Qed.

Lemma singleSubstΠ1 {Γ F G t u l lF}
  (ΠFG : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<lF> F]}
  (Rt : [Γ ||-<lF> t ≅ u : F | RF]) :
  [Γ ||-<l> G[t..]].
Proof.
  eapply singleSubstPoly; tea.
  eapply (ParamRedTy.polyRed (normRedΠ0 (invLRΠ ΠFG))).
Qed.

Lemma singleSubstΣ1 {Γ F G t u l lF}
  (ΠFG : [Γ ||-<l> tSig F G])
  {RF : [Γ ||-<lF> F]}
  (Rt : [Γ ||-<lF> t ≅ u : F | RF]) :
  [Γ ||-<l> G[t..]].
Proof.
  eapply singleSubstPoly; tea.
  eapply (ParamRedTy.polyRed (normRedΣ0 (invLRΣ ΠFG))).
Qed.

Lemma substId Γ t u : t[u..] = t[u .: wk_id (Γ:=Γ) >> tRel ].
Proof. now bsimpl. Qed.

Lemma singleSubstPoly2 {Γ F F' G G' t t' l lF}
  {RFG : PolyRed Γ l F G}
  (RFGeq : PolyRedEq RFG F' G')
  {RF : [Γ ||-<lF> F]}
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF])
  (RGt : [Γ ||-<lF> G[t..]]) :
  [Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ].
Proof.
  assert (wfΓ : [|-Γ]) by (escape ; gen_typing).
  rewrite (substId Γ).
  irrelevance0; [now rewrite (substId Γ)|].
  eapply transEq.
  + unshelve eapply PolyRed.posExt.
    2,4: tea.
    2: irrelevance.
  + unshelve eapply (PolyRedEq.posRed RFGeq).
    2: tea.
    2: irrelevance0; [| now eapply urefl]; now bsimpl.
Qed.

Lemma singleSubstEqPoly {Γ F G t t' l lF}
  {RFG : PolyRed Γ l F G}
  {RF : [Γ ||-<lF> F]}
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF])
  (RGt : [Γ ||-<lF> G[t..]]) :
  [Γ ||-<lF> G[t..] ≅ G[t'..] | RGt ].
Proof.
  eapply (singleSubstPoly2 (F':=F) (RFG:=RFG)); tea.
  destruct RFG; econstructor; cbn; tea; intros; eapply reflLRTyEq.
Qed.

Lemma singleSubstEqΣ {Γ F G t t' l lF}
  {RFG : [Γ ||-<l> tSig F G]}
  {RF : [Γ ||-<lF> F]}
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF])
  (RGt : [Γ ||-<lF> G[t..]]) :
  [Γ ||-<lF> G[t..] ≅ G[t'..] | RGt ].
Proof.
  unshelve (eapply singleSubstEqPoly; tea).
  2: exact (normRedΣ0 (invLRΣ RFG)).
Qed.

Lemma singleSubstΠ2 {Γ F F' G G' t t' l lF}
  {ΠFG : [Γ ||-<l> tProd F G]}
  (ΠFGeq : [Γ ||-<l> tProd F G ≅ tProd F' G' | ΠFG])
  {RF : [Γ ||-<lF> F]}
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF])
  (RGt : [Γ ||-<lF> G[t..]]) :
  [Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ].
Proof.
  eapply singleSubstPoly2; tea.
  pose (hΠ := normRedΠ0 (invLRΠ ΠFG)).
  assert (heq : [Γ ||-<l> tProd F G ≅ tProd F' G' | LRPi' hΠ]) by irrelevance.
  destruct heq as [?? red' ?? polyRed]; cbn in *.
  assert (h' :=redtywf_whnf red' whnf_tProd).
  symmetry in h'; injection h'; clear h'; intros ;  subst.
  exact polyRed.
Qed.

Lemma substSΠaux {Γ F G t u l}
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ])
  (Vt : [Γ ||-v<l> t ≅ u : F | VΓ | VF])
  (Δ : context) (σ σ' : nat -> term)
  (wfΔ : [ |-[ ta ] Δ]) (vσ : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ]) :
  [Δ ||-< l > G[up_term_term σ][t[σ]..]].
Proof.
  eapply singleSubstΠ1.
  eapply (validTy VΠFG); tea.
  unshelve now eapply validTmEq.
  1,3: tea.
Qed.

Lemma singleSubstComm' G t σ : G[t..][σ] = G[up_term_term σ][t[σ]..].
Proof. now asimpl. Qed.

Lemma substSΠ {Γ F G t l}
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] | VΓ].
Proof.
  opector; intros.
  - rewrite singleSubstComm'. now eapply substSΠaux.
  - rewrite singleSubstComm'.
    irrelevance0. 1: symmetry; apply singleSubstComm'.
    eapply singleSubstΠ2.
    1: eapply (validTyExt VΠFG).
    1: now eapply validTmExt.
    Unshelve. all: tea.
    now eapply substSΠaux.
Qed.


Lemma substSΠeq {Γ F F' G G' t u l}
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  {VF' : [Γ ||-v<l> F' | VΓ]}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]}
  (VΠFGeq : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ | VΠFG])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Vu : [Γ ||-v<l> u : F' | VΓ | VF'])
  (Vtu : [Γ ||-v<l> t ≅ u : F | VΓ | VF])
  (VGt := substSΠ VΠFG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[u..] | VΓ | VGt].
Proof.
  pose proof (ureflValidTy VΠFGeq).
  constructor; intros.
  rewrite singleSubstComm'.
  irrelevance0.
  1: symmetry; apply singleSubstComm'.
  eapply singleSubstΠ2.
  1: now eapply (validTyEq VΠFGeq).
  1: now eapply validTmEq.
  Unshelve. all: tea.
  now eapply substSΠaux.
Qed.

End SingleSubst.