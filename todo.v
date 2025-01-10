
Import WeakDeclarativeTypingProperties.
Axiom Subst : TypingSubst (ta := de).

Existing Instance Subst.

Definition idnat (t : term) : term := 
  tNatElim tNat tZero (tLambda tNat (tLambda tNat (tRel 1))) t.

Lemma idnat_ty Γ (t : term) :
  [Γ |- t : tNat] ->
  [Γ |- idnat t : tNat].
Proof.
  intros.
  assert [|- Γ] by gen_typing.
  unfold idnat.
  repeat (econstructor ; eauto).
Qed.

Lemma idnat_succ Γ (t : term) :
  [Γ |- t : tNat] ->
  [Γ |- idnat (tSucc t) ≅ t : tNat].
Proof.
  intros.
  assert [|- Γ] by gen_typing.
  unfold idnat.
  etransitivity.
  1:{
    eapply convtm_meta_conv.
    1: eapply TermNatElimSucc ; refold.
    all: cbn in * ; eauto.
    all: repeat (econstructor ; eauto).
  }
  etransitivity.
  {
   eapply convtm_meta_conv.
   1: econstructor.
   1: eapply convtm_meta_conv.
   1: eapply TermBRed ; refold.
   all: cbn in * ; eauto.
   1,2,4: repeat (econstructor ; eauto).
   all: reflexivity.
  }
  etransitivity.
  {
   eapply convtm_meta_conv.
   1: eapply TermBRed ; refold.
   all: cbn in * ; eauto.
   1: repeat (econstructor ; eauto).
   1: erewrite <- wk1_ren_on ; eapply typing_wk ; gen_typing.
   repeat (econstructor ; eauto).
   reflexivity.
  }
  cbn.
  symmetry.
  eapply convtm_meta_conv.
  1: now constructor.
  1: reflexivity.
  now bsimpl.
Qed.

Lemma test Γ (A B t t' : term) :
  [|- Γ] ->
  [Γ |- t : tNat] ->
  [Γ |- t' : tNat] ->
  [Γ |- tSucc t ≅ tSucc t' : tNat] ->
  [Γ |- t ≅ t' : tNat].
Proof.
  intros ??? Hconv.
  etransitivity.
  1: etransitivity.
  1: symmetry.
  1,3: now eapply idnat_succ.
  unfold idnat.
  eapply convtm_meta_conv.
  1: econstructor ; eauto.
  4,5: reflexivity.
  all: repeat (econstructor ; eauto).
Qed.