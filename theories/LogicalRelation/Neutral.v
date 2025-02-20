From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Reflexivity Irrelevance Escape Transitivity.

Set Universe Polymorphism.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l Γ A} : [Γ |- A] -> [ Γ |- A ~ A : U] -> [Γ ||-<l> A].
Proof.
  intros wtyA reflA. apply LRne_.
  exists A; [gen_typing|..]; assumption.
Defined.

Lemma neU {l Γ A n} (h : [Γ ||-U<l> A]) :
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] -> URedTm (LogRelRec l) Γ n A h.
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros; unshelve eexists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now eapply NeType, convneu_whne.
Defined.


Set Printing Primitive Projection Parameters.


Lemma neuEq {l Γ A B} (RA : [Γ ||-<l> A]) :
  [Γ |- A] -> [Γ |- B] ->
  [Γ |- A ~ B : U] ->
  [Γ ||-<l> A ≅ B | RA].
Proof.
  intros wtyA wtyB eqAB.
  unshelve irrelevance0. 1: assumption. 3: reflexivity.
  1: apply neu; try assumption; now eapply lrefl.
  econstructor.
  1: now apply redtywf_refl.
  all: cbn; assumption.
Qed.

(* TODO MOVE ME *)
Lemma ty_app_ren {Γ Δ A f a dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f : A] -> [Γ |- A ≅ tProd dom cod] -> [Δ |- a : dom⟨ρ⟩] -> [Δ |- tApp f⟨ρ⟩ a : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply ty_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

(* TODO MOVE ME *)
Lemma convneu_app_ren {Γ Δ A f g a b dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f ~ g : A] ->
  [Γ |- A ≅ tProd dom cod] ->
  [Δ |- a ≅ b : dom⟨ρ⟩] ->
  [Δ |- tApp f⟨ρ⟩ a ~ tApp g⟨ρ⟩ b : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply convneu_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Definition reflect {l Γ A} (RA : [Γ ||-<l> A]) :=
 forall n n',
    [Γ |- n : A] ->
    [Γ |- n' : A] ->
    [Γ |- n ~ n' : A] ->
    [Γ ||-<l> n ≅ n' : A| RA].

Lemma reflect_diag {l Γ A} (RA : [Γ ||-<l> A]) (c : reflect RA) :
  forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-<l> n : A | RA].
Proof.
intros; eapply c.
all: eassumption.
Qed.

Lemma reflect_var0 {l Γ A A'} (RA : [Γ ,, A ||-<l> A']) :
  reflect RA ->
  [Γ ,, A |- A⟨↑⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  intros cRA conv HA.
  assert [Γ ,, A |- tRel 0 : A']
  by (eapply ty_conv; tea; escape; eapply (ty_var (wfc_wft EscRA) (in_here _ _))).
  eapply reflect_diag; tea.
  eapply convneu_var; tea.
Qed.


Lemma reflect_U : forall l Γ A (RA : [Γ ||-U< l > A]), reflect (LRU_ RA).
Proof.
  intros l Γ A h0 ???? h; pose proof (lrefl h); pose proof (urefl h).
  assert [Γ |- A ≅ U] by (destruct h0; gen_typing).
  unshelve econstructor.
  1-2: now apply neU.
  + eapply RedTyRecBwd, neu. 1,2: try gen_typing.
  + cbn. gen_typing.
  + eapply RedTyRecBwd; apply neu. 1,2: gen_typing.
  + eapply TyEqRecBwd. eapply neuEq. all: try gen_typing.
    all: eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
Qed.

Lemma reflect_ne : forall l Γ A (RA : [Γ ||-ne A]), reflect (LRne_ l RA).
Proof.
  intros l Γ A h0 ?????.
  destruct h0 as [B []]; intros ** ; assert ([Γ |- A ≅ B]) by gen_typing.
  exists n n'; cbn.
  1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
  gen_typing.
Qed.

Lemma reflect_Pi : forall l Γ A (RA : [Γ ||-Π< l > A]),
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h)) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b: _]),
        reflect (PolyRed.posRed RA ρ h ha)) ->
  reflect (LRPi' RA).
Proof.
  intros l Γ A ΠA0 ihdom ihcod.
  set (ΠA := ΠA0); destruct ΠA0 as [dom cod].
  simpl in ihdom, ihcod.
  assert [Γ |- A ≅ tProd dom cod] by gen_typing.
  assert [Γ |- dom] by eapply PolyRed.shpTy, polyRed.
  assert [|- Γ ,, dom] as Hext by gen_typing.
  assert [Γ,, dom |-[ ta ] tRel 0 : dom⟨@wk1 Γ dom⟩]
    by (rewrite wk1_ren_on; now eapply ty_var0).
  assert [Γ,, dom |-[ ta ] tRel 0 ~ tRel 0 : dom⟨@wk1 Γ dom⟩]
    by now apply convneu_var.
  assert [PolyRed.shpRed polyRed (wk1 dom) Hext | Γ,, dom ||- tRel 0 : dom⟨wk1 dom⟩]
    by now eapply ihdom.
  assert [Γ ,, dom |- cod] by eapply PolyRed.posTy, polyRed.

  assert (forall n Δ a (ρ : Δ ≤ Γ),
      [|- Δ] -> [Γ |- n : A] -> [Δ |- a : dom⟨ρ⟩] -> [Δ |-[ ta ] tApp n⟨ρ⟩ a : cod[a .: ρ >> tRel]]) as Happ.
  {
    intros.
    eapply typing_meta_conv.
    1: eapply ty_app ; tea.
    1: eapply typing_meta_conv.
    1: eapply ty_wk.
    - eassumption.
    - eapply ty_conv ; tea.
    - cbn ; reflexivity.
    - now bsimpl.
  }

  assert (forall n n',
    [Γ |- n : A] -> [Γ |- n' : A] ->
    [Γ |- n ~ n : A] -> [Γ |- n' ~ n' : A] ->
    [Γ |- n ~ n' : A] ->
    [Γ |-[ ta ] n ≅ n' : tProd dom cod]).
  {
    intros ?????? hnn'.
    eapply convtm_eta ; tea.
    1-4: first [now eapply ty_conv| constructor; now eapply convneu_conv].
    eapply convneu_app_ren in hnn' ; tea ; cycle -1.
    1: now eapply escapeEqTerm.
    eapply ihcod in hnn' as hred.
    + erewrite <- wk1_ren_on.
      eapply convtm_meta_conv.
      1: now escape.
      all: now bsimpl.
    + eapply typing_meta_conv ; eauto.
    + eapply typing_meta_conv ; eauto.
    Unshelve. 3: eassumption.
  }

  unshelve refine ( let funred : forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> PiRedTm ΠA n := _ in _).
  {
    intros. exists n; cbn.
    - eapply redtmwf_refl ; gen_typing.
    - constructor; now eapply convneu_conv.
  }

  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  unshelve econstructor.
  1,2: now apply funred.
  all: cbn; clear funred.
  * eauto.
  * intros. apply ihcod; cbn.
    + apply escapeTerm in hab; now eapply ty_app_ren.
    + pose proof (escapeEq _ (ΠA.(PolyRed.posExt) _ _ hab)).
      apply LRTmEqSym, escapeTerm in hab.
      eapply ty_conv; [| now symmetry].
      now eapply ty_app_ren.
    + eapply convneu_app_ren. 1,2: eassumption.
      now eapply escapeEqTerm.
Qed.

Arguments ParamRedTy.outTy /.

Lemma reflect_Sig : forall l Γ A (RA : [Γ ||-Σ< l > A]),
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h)) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b : _]),
        reflect (PolyRed.posRed RA ρ h ha)) ->
  reflect (LRSig' RA).
Proof.
  intros l Γ A ΣA0 ihdom ihcod.
  set (ΣA := ΣA0); destruct ΣA0 as [dom cod] ; cbn in *.

  assert [Γ |- A ≅ ΣA.(outTy)]
    by (destruct ΣA; cbn in *; gen_typing).
  assert [Γ |- ΣA.(outTy)]
    by (destruct ΣA; cbn in *; gen_typing).
  assert [Γ |- dom] by now eapply PolyRed.shpTy.
  assert [|- Γ ,, dom] as Hext by gen_typing.
  assert [Γ,, dom |-[ ta ] tRel 0 : dom⟨@wk1 Γ dom⟩]
    by (rewrite wk1_ren_on; now eapply ty_var0).
  assert [Γ,, dom |-[ ta ] tRel 0 ~ tRel 0 : dom⟨@wk1 Γ dom⟩]
    by now apply convneu_var.
  assert [PolyRed.shpRed polyRed (wk1 dom) Hext | Γ,, dom ||- tRel 0 : dom⟨wk1 dom⟩]
    by now eapply ihdom.
  assert [Γ ,, dom |- cod]
    by now eapply PolyRed.posTy.

  assert (hconv_fst : forall n n' Δ (ρ : Δ ≤ Γ) (h : [ |- Δ]), [Γ |- n : A] -> [Γ |- n' : A] -> [Γ |- n ~ n' : A] ->
    [PolyRedPack.shpRed ΣA ρ h | Δ ||- tFst n⟨ρ⟩ ≅ tFst n'⟨ρ⟩ : _]).
    1:{
      intros.
      eapply ihdom.
      * rewrite wk_fst; eapply ty_wk; tea.
        eapply ty_fst; now eapply ty_conv.
      * rewrite wk_fst ; eapply ty_wk ; tea.
        eapply ty_fst ; now eapply ty_conv.
      * repeat rewrite wk_fst; eapply convneu_wk; tea.
        eapply convneu_fst; now eapply convneu_conv.
    }

  assert (hconv : forall n n',
  [Γ |- n : A] -> [Γ |- n' : A] ->
  [Γ |- n ~ n : A] -> [Γ |- n' ~ n' : A] ->
  [Γ |- n ~ n' : A] -> [Γ |-[ ta ] n ≅ n' : tSig dom cod]).
  {
    intros n n' hn hn' hnn hn'n' hnn'.
    assert (wfΓ : [|- Γ]) by gen_typing.
    pose proof (hfst := hconv_fst n n' Γ wk_id wfΓ hn hn' hnn').
    eapply convtm_eta_sig ; cbn in * ; tea.
    1-4: first [now eapply ty_conv| constructor; now eapply convneu_conv].
    1: generalize (escapeEqTerm _ hfst); now rewrite !wk_id_ren_on.

    eapply convtm_meta_conv.
    1: unshelve eapply escapeEqTerm, (ihcod _ (tFst n)⟨wk_id⟩ (tFst n)⟨wk_id⟩ wk_id); tea.
    6: reflexivity.
    + now eapply lrefl.
    + eapply typing_meta_conv.
      1: gen_typing.
      now bsimpl.
    + eapply ty_conv.
      1: gen_typing.
      symmetry.
      replace (cod[(tFst n')..]) with (cod[(tFst n') .: (@wk_id Γ) >> tRel]) by (now bsimpl).
      unshelve eapply escapeEq, polyRed.(PolyRed.posExt) ; tea.
      now erewrite <- (wk_id_ren_on _ n').
    + eapply convne_meta_conv.
      1:now eapply convneu_snd, convneu_conv.
      1: now bsimpl.
      easy.
    + now bsimpl.
  }

  unshelve refine ( let funred : forall n,
    [Γ |- n : A] ->
    [Γ |- n ~ n : A] -> SigRedTm ΣA n  := _ in _).
  {
    intros n **.
    cbn in *.
    unshelve eexists n.
    - eapply redtmwf_refl; now eapply ty_conv.
    - constructor ; cbn ; now eapply convneu_conv.
  }

  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  unshelve refine (let Rn : SigRedTm ΣA n := _ in _).
  1: now eapply funred.
  unshelve refine (let Rn' : SigRedTm ΣA n' := _ in _).
  1: now eapply funred.
  assert (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
    [Δ |- cod[tFst n⟨ρ⟩ .: ρ >> tRel] ≅ cod[tFst n'⟨ρ⟩ .: ρ >> tRel]]).
  {
    intros; eapply escapeEq; unshelve eapply (PolyRed.posExt ΣA); tea.
    now eapply hconv_fst.
  }
  unshelve eexists Rn Rn' _.
  + cbn. intros. now eapply hconv_fst.
  + cbn.  eapply hconv ; tea.
  + intros; cbn. eapply ihcod.
    all: rewrite wk_fst; rewrite !wk_snd.
    2: eapply ty_conv; [|now symmetry]; rewrite wk_fst.
    all: rewrite <- subst_ren_subst_mixed.
    * eapply ty_wk; tea; eapply ty_snd; now eapply ty_conv.
    * eapply ty_wk; tea; eapply ty_snd; now eapply ty_conv.
    * eapply convneu_wk; tea; eapply convneu_snd; now eapply convneu_conv.
Qed.

Lemma reflect_Nat {l Γ A} (NA : [Γ ||-Nat A]) : reflect (LRNat_ l NA).
Proof.
  red; intros.
  assert [Γ |- A ≅ tNat] by (destruct NA; gen_typing).
  assert [Γ |- n : tNat] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  1,3: eapply convneu_conv; [|eassumption]; tea.
  eapply ty_conv; eassumption.
Qed.

Lemma reflect_Empty {l Γ A} (NA : [Γ ||-Empty A]) : reflect (LREmpty_ l NA).
Proof.
  red; intros.
  assert [Γ |- A ≅ tEmpty] by (destruct NA; gen_typing).
  assert [Γ |- n : tEmpty] by now eapply ty_conv.
  assert [Γ |- n' : tEmpty] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  all: now eapply convneu_conv.
Qed.

Lemma reflect_Id {l Γ A} (IA : [Γ ||-Id<l> A]) :
  reflect (LRId' IA).
Proof.
  red; intros.
  assert [Γ |- A ≅ IA.(IdRedTy.outTy)] by (destruct IA; unfold IdRedTy.outTy; cbn; gen_typing).
  assert [Γ |- n : IA.(IdRedTy.outTy)] by now eapply ty_conv.
  assert [Γ |- n' : IA.(IdRedTy.outTy)] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  all: now eapply convneu_conv.
Qed.

Lemma reflectness {l Γ A} (RA : [Γ ||-<l> A]) : reflect RA.
Proof.
revert l Γ A RA; eapply LR_rect_TyUr; cbn; intros.
- now apply reflect_U.
- now apply reflect_ne.
- now apply reflect_Pi.
- now apply reflect_Nat.
- now apply reflect_Empty.
- now apply reflect_Sig.
- now apply reflect_Id.
Qed.

Lemma neuTerm {l Γ A} (RA : [Γ ||-<l> A]) {n} :
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [Γ ||-<l> n : A | RA].
Proof.
  intros.  now eapply reflectness.
Qed.

Lemma neuTermEq {l Γ A} (RA : [Γ ||-<l> A]) {n n'} :
  [Γ |- n : A] ->
  [Γ |- n' : A] ->
  [Γ |- n ~ n' : A] ->
  [Γ ||-<l> n ≅ n' : A| RA].
Proof.
  intros; now eapply reflectness.
Qed.

Lemma neNfTermEq {Γ l A n n'} (RA : [Γ ||-<l> A]) : [Γ ||-NeNf n ≅ n' : A] -> [RA | Γ ||- n ≅ n' : A].
Proof.  intros []; now eapply neuTermEq. Qed.


Lemma var0conv {l Γ A A'} (RA : [Γ ,, A ||-<l> A']) :
  [Γ,, A |- A⟨↑⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  apply reflect_var0 ; now eapply reflectness.
Qed.

Lemma var0 {l Γ A A'} (RA : [Γ ,, A ||-<l> A']) :
  A⟨↑⟩ = A' ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  intros eq.
  apply var0conv.
  rewrite eq.
  unshelve eapply escapeEq; tea.
  eapply reflLRTyEq.
Qed.

End Neutral.


