From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity Irrelevance Properties.

Set Universe Polymorphism.

Section SingleSubst.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

(* Lemma singleSubstComm G t σ : G[t..][σ] = G[t[σ] .: σ].
Proof. now asimpl. Qed. *)




(* Lemma singleSubstPoly {Γ F G t u l lF}
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
Qed. *)

(* Lemma subst_up_term_single A σ t : A[up_term_term σ][t..] = A[t .: σ].
Proof. now bsimpl. Qed.

Lemma eta_up_single_subst A σ : A[up_term_term (↑ >> σ)][(σ var_zero)..] = A[σ].
Proof. now rewrite up_single_subst, (scons_eta' σ). Qed. *)

Lemma validΠdom {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΠ : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ]) :
  [Γ ||-v<l> F ≅ F' | VΓ].
Proof.
  constructor; intros ? wfΔ ?? Vσ.
  pose proof (RΠ := validTyExt VΠ wfΔ Vσ).
  rewrite 2!subst_prod in RΠ.
  now unshelve eapply (instKripke _ (normRedΠ RΠ).(PolyRed.shpRed)).
Qed.

Lemma validΠcod {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΠ : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ]) :
  [Γ,, F ||-v<l> G ≅ G' | validSnoc VΓ (validΠdom VΠ)].
Proof.
  constructor; intros ? wfΔ ?? [Vσ hd].
  pose proof (RΠ := validTyExt VΠ wfΔ Vσ).
  rewrite 2!subst_prod in RΠ.
  generalize (instKripkeSubst (normRedΠ RΠ).(PolyRed.posRed) _ hd).
  cbn -[wk1]; now rewrite 2!eta_up_single_subst.
Qed.

Lemma substSΠ {Γ Γ' F F' G G' t u l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΠ : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ])
  (Vt : [Γ ||-v<l> t ≅ u : F | VΓ | validΠdom VΠ]) :
  [_ ||-v<l> G[t..] ≅ G'[u..] | VΓ].
Proof. eapply substS ; tea; eapply validΠcod. Qed.


(*
Lemma subst_sig X Y σ : (tSig X Y)[σ] = tSig X[σ] Y[up_term_term σ].
Proof. now asimpl. Qed. *)

Lemma validΣdom {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΣ : [Γ ||-v<l> tSig F G ≅ tSig F' G' | VΓ]) :
  [Γ ||-v<l> F ≅ F' | VΓ].
Proof.
  constructor; intros ? wfΔ ?? Vσ.
  pose proof (RΠ := validTyExt VΣ wfΔ Vσ).
  rewrite 2!subst_sig in RΠ.
  now unshelve eapply (instKripke _ (normRedΣ RΠ).(PolyRed.shpRed)).
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

End SingleSubst.