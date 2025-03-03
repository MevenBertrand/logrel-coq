From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l Γ A B} : [Γ |- A] -> [Γ |- B] -> [ Γ |- A ~ B : U] -> [Γ ||-<l> A ≅ B].
Proof.
  intros; apply LRne_.
  exists A B ; tea; gtyping.
Defined.

Lemma neU {l l' Γ A B n n'} (h : [Γ ||-U<l> A ≅ B]) :
  [Γ |- n : A] ->
  [Γ |- n ~ n' : A] ->  URedTm l' Γ n.
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros; exists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now eapply NeType, convneu_whne.
Defined.

Definition reflect {l Γ A B} (RA : [Γ ||-<l> A ≅ B]) :=
 forall n n',
    [Γ |- n : A] ->
    [Γ |- n' : A] ->
    [Γ |- n ~ n' : A] ->
    [Γ ||-<l> n ≅ n' : _ | RA].


Lemma reflect_diag {l Γ A B} (RA : [Γ ||-<l> A ≅ B]) (c : reflect RA) :
  forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-<l> n : A | RA].
Proof.
  intros; eapply c.
  all: eassumption.
Qed.

Lemma reflect_var0 {l Γ A A' B'} (RA : [Γ ,, A ||-<l> A' ≅ B']) :
  reflect RA ->
  [Γ ,, A |- A⟨↑⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  intros cRA conv HA.
  assert [Γ ,, A |- tRel 0 : A'].
  1:{
    eapply ty_conv; tea; escape.
    unshelve eapply (ty_var _ (in_here _ _)).
    now eapply wfc_wft.
  }
  eapply reflect_diag; tea.
  eapply convneu_var; tea.
Qed.


Lemma reflect_U {l Γ A B} (h : [Γ ||-U<l> A ≅ B]) : reflect (LRU_ h).
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros n n' tyn tyn' conv.
  exists (neU h tyn conv) (neU h tyn' (symmetry conv)).
  * cbn; eapply convtm_convneu; [constructor|]; now eapply convneu_conv.
  * eapply redTyRecBwd, neu.
    1,2: gtyping.
    now eapply convneu_conv.
Qed.


Lemma reflect_ne {l Γ A B} (RA : [Γ ||-ne A ≅ B]) : reflect (LRne_ l RA).
Proof.
  intros ? **. pose proof (h := whredL_conv (LRne_ l RA)); cbn in h.
  exists n n'; cbn.
  1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
  gen_typing.
Qed.


Section ReflectPi.
Context {l Γ A B} (RA : [Γ ||-Π< l > A ≅ B]).

Let convΠ : [Γ |- A ≅ outTyL RA] := whredL_conv (LRPi' RA).

#[local]
Definition funred {n} : [Γ |- n : A] -> [Γ |- n ~ n : A] -> PiRedTm RA n.
Proof.
  intros. exists n; cbn.
  - now eapply redtmwf_refl, ty_conv.
  - constructor; now eapply convneu_conv.
Defined.

Lemma reflect_Pi
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  (ihcod : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b: _]),
        reflect (PolyRed.posRed RA ρ h ha))
  : reflect (LRPi' RA).
Proof.
  destruct (ParamRedTy.redL RA).
  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  unshelve econstructor.
  1,2: now apply funred.
  * cbn; eapply convtm_eta ; tea.
    1-4: first [now eapply ty_conv| constructor; now eapply convneu_conv].
    rewrite <-(@var0_wk1_id Γ RA.(ParamRedTy.domL) RA.(ParamRedTy.codL)).
    assert [Γ,, PiRedTy.domL RA |-[ ta ] tRel 0 : (PiRedTy.domL RA)⟨@wk1 Γ (PiRedTy.domL RA)⟩]
    by (rewrite wk1_ren_on; eapply ty_var0; now destruct RA as [???? []]).
    unshelve eapply escapeTm, ihcod.
    2: gtyping.
    2: eapply reflect_var0; [eapply ihdom| | eassumption].
    all: erewrite <-!wk1_ren_on.
    2,3: now eapply ty_app_ren.
    1: apply convty_wk; [gtyping| destruct RA; now eapply lrefl].
    eapply convneu_app_ren; tea.
    eapply escapeTm, ihdom; tea; now apply convneu_var.
    Unshelve. gtyping.
  * cbn; intros; apply ihcod; cbn.
    + escape; now eapply ty_app_ren.
    + eapply ty_conv.
      1: escape; now eapply ty_app_ren.
      pose proof (kripkeLRlrefl (PolyRed.posRed RA) _ _ hab).
      escape; now symmetry.
    + eapply convneu_app_ren.
      1,2: eassumption.
      now escape.
Qed.

End ReflectPi.

Section ReflectSig.
Context {l Γ A B} (RA : [Γ ||-Σ< l > A ≅ B]).

Let convΣ : [Γ |- A ≅ outTyL RA] := whredL_conv (LRSig' RA).

#[local]
Definition sigred {n} : [Γ |- n : A] -> [Γ |- n ~ n : A] -> SigRedTm RA n.
Proof.
  intros. exists n; cbn.
  - now eapply redtmwf_refl, ty_conv.
  - constructor; now eapply convneu_conv.
Defined.

#[local]
Definition hconv_fst
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  {n n' Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ])  :
  [Γ |- n : A] -> [Γ |- n' : A] -> [Γ |- n ~ n' : A] ->
  [PolyRed.shpRed RA ρ h | Δ ||- tFst n⟨ρ⟩ ≅ tFst n'⟨ρ⟩ : _].
Proof.
  intros; eapply ihdom; rewrite !wk_fst.
  1,2: eapply ty_wk; tea; now eapply ty_fst, ty_conv.
  eapply convneu_wk; tea; now eapply convneu_fst, convneu_conv.
Qed.

#[local]
Definition hconv_snd
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  (ihcod : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b: _]),
        reflect (PolyRed.posRed RA ρ h ha))
  {n n' Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ])
  (tyn : [Γ |- n : A]) (tyn' : [Γ |- n' : A]) (convnn' : [Γ |- n ~ n' : A])
  (hfst := hconv_fst ihdom ρ h tyn tyn' convnn') :
  [PolyRed.posRed RA ρ h hfst | Δ ||- tSnd n⟨ρ⟩ ≅ tSnd n'⟨ρ⟩ : _].
Proof.
  intros; eapply ihcod; rewrite !wk_fst, !wk_snd, <-subst_ren_subst_mixed.
  1,2: eapply ty_wk; tea.
  * now eapply ty_snd, ty_conv.
  * eapply ty_conv.
    1: now eapply ty_snd, ty_conv.
    assert (wfΓ : [|-Γ]) by gtyping.
    pose (hfst' := hconv_fst ihdom wk_id wfΓ tyn tyn' convnn').
    pose proof (kr := kripkeLRlrefl (PolyRed.posRed RA) wk_id wfΓ hfst').
    rewrite 2!wk_fst,<-2!eq_subst_scons in kr; escape; now symmetry.
  * eapply convneu_wk; tea; now eapply convneu_snd, convneu_conv.
Qed.

Lemma reflect_Sig
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  (ihcod : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b: _]),
        reflect (PolyRed.posRed RA ρ h ha))
  : reflect (LRSig' RA).
Proof.
  destruct (ParamRedTy.redL RA).
  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  unshelve econstructor.
  1,2: now apply sigred.
  * intros; now eapply hconv_fst.
  * assert (wfΓ : [|-Γ]) by gtyping.
    unshelve epose proof (hfst := hconv_fst ihdom wk_id wfΓ _ _ h); tea.
    unshelve epose proof (hsnd := hconv_snd ihdom ihcod wk_id wfΓ _ _ h); tea.
    cbn in hsnd; escape.
    rewrite !wk_fst,<-?eq_subst_scons,!wk_id_ren_on in *.
    eapply convtm_eta_sig ; cbn in * ; tea.
    all: first [now eapply ty_conv| constructor; now eapply convneu_conv].
  * intros; now eapply hconv_snd.
Qed.
End ReflectSig.

Lemma reflect_Nat {l Γ A B} (NA : [Γ ||-Nat A ≅ B]) : reflect (LRNat_ l NA).
Proof.
  red; intros; pose proof (whredL_conv (LRNat_ l NA)).
  assert [Γ |- n : tNat] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  1,3: eapply convneu_conv; [|eassumption]; tea.
  eapply ty_conv; eassumption.
Qed.

Lemma reflect_Empty {l Γ A B} (NA : [Γ ||-Empty A ≅ B]) : reflect (LREmpty_ l NA).
Proof.
  red; intros; pose proof (whredL_conv (LREmpty_ l NA)).
  assert [Γ |- n : tEmpty] by now eapply ty_conv.
  assert [Γ |- n' : tEmpty] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  constructor; tea; now eapply convneu_conv.
Qed.

Lemma reflect_Id {l Γ A B} (IA : [Γ ||-Id<l> A ≅ B]) :
  reflect (LRId' IA).
Proof.
  red; intros; pose proof (whredL_conv (LRId' IA)).
  assert [Γ |- n : IdRedTy.outTy IA] by now eapply ty_conv.
  assert [Γ |- n' : IdRedTy.outTy IA] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  all: now eapply convneu_conv.
Qed.

Lemma reflectLR {l Γ A B} (RA : [Γ ||-<l> A ≅ B]) : reflect RA.
Proof.
  indLR RA; intros.
  - now apply reflect_U.
  - now apply reflect_ne.
  - now apply reflect_Pi.
  - now apply reflect_Nat.
  - now apply reflect_Empty.
  - now apply reflect_Sig.
  - now apply reflect_Id.
Qed.

Definition neuTerm {l Γ A B} (RA : [Γ ||-<l> A ≅ B]) {n} :=
  reflect_diag RA (reflectLR RA) n.

Lemma neNfTermEq {Γ l A n n'} (RA : [Γ ||-<l> A]) : [Γ ||-NeNf n ≅ n' : A] -> [RA | Γ ||- n ≅ n' : A].
Proof. intros []; now eapply reflectLR. Qed.


Lemma var0conv {l Γ A A' B'} (RA : [Γ ,, A ||-<l> A' ≅ B']) :
  [Γ,, A |- A⟨↑⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  apply reflect_var0 ; now eapply reflectLR.
Qed.

Lemma var0 {l Γ A A' B'} (RA : [Γ ,, A ||-<l> A' ≅ B']) :
  A⟨↑⟩ = A' ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  intros; subst; apply var0conv; tea.
  eapply lrefl; now escape.
Qed.

End Neutral.


