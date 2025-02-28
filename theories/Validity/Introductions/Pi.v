From Coq Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section PiValidity.

  Context `{GenericTypingProperties}.

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

  Definition PiValid {l Γ Γ' F F' G G'} (VΓ : [||-v Γ ≅ Γ'])
    (VF : [Γ ||-v< l > F ≅ F' | VΓ ])
    (VG : [Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF]) :
    [Γ ||-v< l > tProd F G ≅ tProd F' G' | VΓ].
  Proof.
    constructor; intros; rewrite 2!subst_prod.
    eapply LRPi', substParamRedTy; tea; intros; gtyping.
  Qed.


  Lemma PiValidU {Γ Γ' F F' G G'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VF : [ Γ ||-v< one > F ≅ F' | VΓ ])
    (VΓF := validSnoc VΓ VF)
    (VU : [ Γ ||-v< one > U | VΓ ])
    (VU' : [ Γ ,, F ||-v< one > U | VΓF ])
    (VFU : [ Γ ||-v< one > F ≅ F' : U | VΓ | VU ])
    (VGU : [ Γ ,, F ||-v< one > G ≅ G' : U | VΓF | VU' ]) :
    [ Γ ||-v< one > tProd F G ≅ tProd F' G' : U | VΓ | UValid VΓ ].
  Proof.
    constructor; intros ? wfΔ0 ?? Vσ.
    pose proof (univValid zero VFU) as VF0.
    pose proof (univValid zero VGU) as VG0.
    pose (v := validSnoc VΓ (urefl VF)).
    assert [_ ||-v<one> G ≅ G' : _ | _ | UValid v] by irrValid.
    pose proof (Vuσ := liftSubst' VF Vσ).
    pose proof (Vuσ' := liftSubst' (urefl VF) (urefl Vσ)).
    instValid Vuσ'.
    instValid Vuσ; instValid Vσ; escape.
    unshelve econstructor.
    1,2: econstructor; [apply redtmwf_refl; cbn; eapply ty_prod; tea| constructor].
    1: cbn in *; gtyping.
    enough (h : [ Δ ||-< zero > (tProd F G)[σ] ≅ (tProd F' G')[σ']]) by exact (cumLR h).
    eapply validTyExt; tea; unshelve eapply PiValid; tea.
    eapply convValidTy; exact VG0.
  Qed.

End PiValidity.
