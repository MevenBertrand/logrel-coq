From Coq Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Induction NormalRed EqRedRight.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi.
From LogRel.Validity Require Import Validity Irrelevance Properties SingleSubst Reflexivity Universe Poly.

Set Universe Polymorphism.

Section PiTyValidity.

  Context `{GenericTypingProperties}.
  Context {l Γ F G} (vΓ : [||-v Γ])
    (vF : [Γ ||-v< l > F | vΓ ])
    (vG : [Γ ,, F ||-v< l > G | validSnoc vΓ vF]).

  Lemma PiRed {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
    : [ Δ ||-< l > (tProd F G)[σ] ].
  Proof.
    eapply LRPi'.
    pose (p := substPolyRed vΓ vF vG _ (lrefl vσ)).
    escape; cbn; econstructor; tea;
    destruct (polyRedId p);
    destruct (polyRedEqId p (substPolyRedEq vΓ vF vG _ (lrefl vσ) p)); escape.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
    - gen_typing.
  Defined.

  Lemma PiEqRed1 {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ ])
    : [ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F G)[σ'] | PiRed tΔ vσσ' ].
  Proof.
    pose (p := substPolyRed vΓ vF vG _ vσσ').
    pose (p' := substPolyRed vΓ vF vG _ (urefl vσσ')).
    pose (peq := substPolyRedEq vΓ vF vG _ vσσ' p).
    destruct (polyRedId p), (polyRedId p'), (polyRedEqId p peq).
    escape; econstructor; cbn; tea.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
    - now eapply substPolyRedEq.
  Defined.

  Lemma PiValid : [Γ ||-v< l > tProd F G | vΓ].
  Proof.
    unshelve econstructor.
    - intros; now eapply PiRed.
    - intros; eapply PiEqRed1.
  Defined.

End PiTyValidity.

Section PiTyDomValidity.

  Context `{GenericTypingProperties}.
  Context {l Γ F G} (vΓ : [||-v Γ])
    (vΠFG : [Γ ||-v< l > tProd F G | vΓ ]).

  Lemma PiValidDom : [Γ ||-v< l > F | vΓ].
  Proof.
  unshelve econstructor.
  - intros Δ vΔ σ σ' vσ; instValid vσ.
    now pose proof (polyRedId (normRedΠ0 (invLRΠ RvΠFG))) as [].
  - intros Δ vΔ σ σ' vσσ'; instValid vσσ'.
    pose proof (polyRedEqId _ (normEqRedΠ _ REvΠFG)) as [? _].
    irrelevance.
  Qed.

  Lemma eq_subst_eta A σ : A[σ] = A[up_term_term (↑ >> σ)][(σ var_zero)..].
  Proof. now bsimpl. Qed.

  Lemma PiValidCod : [Γ,, F ||-v< l > G | validSnoc vΓ PiValidDom].
  Proof.
    unshelve econstructor.
    - intros Δ vΔ σ σ' [vσ v0]; instValid vσ; cbn in *.
      rewrite eq_subst_eta; eapply singleSubstΠ1; tea.
    - cbn; refold.
      intros Δ vΔ σ σ' [vσσ' v00']; instValid vσσ'; instValid (urefl vσσ'); cbn in *.
      pose proof (polyRedEqId _ (normEqRedΠ _ REvΠFG)) as [? _].
      rewrite 2!eq_subst_eta; eapply singleSubstΠ2; tea.
    Qed.

End PiTyDomValidity.

Section PiTyCongruence.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G' l}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< l > F | vΓ ])
    (vG : [ Γ ,, F ||-v< l > G | validSnoc vΓ vF ])
    (vF' : [ Γ ||-v< l > F' | vΓ ])
    (vG' : [ Γ ,, F' ||-v< l > G' | validSnoc vΓ vF' ])
    (vFF' : [ Γ ||-v< l > F ≅ F' | vΓ | vF ])
    (vGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc vΓ vF | vG ]).

  Lemma PiEqRed2 {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
    : [ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F' G')[σ'] | validTy (PiValid vΓ vF vG) tΔ vσ ].
  Proof.
    pose (p := substPolyRed vΓ vF vG _ (lrefl vσ)).
    pose (p' := substPolyRed vΓ vF' vG' _ (urefl vσ)).
    pose (peq := substEqPolyRedEq vΓ vF vG _ vσ vF' vG' vFF' vGG' p).
    destruct (polyRedId p); destruct (polyRedId p'); destruct (polyRedEqId p peq).
    escape; econstructor; cbn; tea.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
  Qed.

  Lemma PiCong : [ Γ ||-v< l > tProd F G ≅ tProd F' G' | vΓ | PiValid vΓ vF vG ].
  Proof.
    econstructor. intros *; eapply PiEqRed2.
  Qed.

End PiTyCongruence.



Section PiTmCongruence.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G'}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< one > F | vΓ ])
    (vU : [ Γ ,, F ||-v< one > U | validSnoc vΓ vF ])
    (vFU : [ Γ ||-v< one > F : U | vΓ | UValid vΓ ])
    (vGU : [ Γ ,, F ||-v< one > G : U | validSnoc vΓ vF | vU ])
    (vF' : [ Γ ||-v< one > F' | vΓ ])
    (vU' : [ Γ ,, F' ||-v< one > U | validSnoc vΓ vF' ])
    (vF'U : [ Γ ||-v< one > F' : U | vΓ | UValid vΓ ])
    (vG'U : [ Γ ,, F' ||-v< one > G' : U | validSnoc vΓ vF' | vU' ])
    (vFF' : [ Γ ||-v< one > F ≅ F' : U | vΓ | UValid vΓ ])
    (vGG' : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc vΓ vF | vU ]).

  Lemma PiCongTm : [ Γ ||-v< one > tProd F G ≅ tProd F' G' : U | vΓ | UValid vΓ ].
  Proof.
    econstructor.
    intros Δ tΔ σ σ' Vσσ'.
    pose proof (univValid (l' := zero) _ _ vFU) as vF0.
    pose proof (univValid (l' := zero) _ _ vF'U) as vF'0.
    pose proof (Vuσ := liftSubstEq' vF Vσσ').
    (* pose proof (Vuσ' := liftSubstEq' vF (urefl Vσσ')). *)
    pose proof (Vuσ' := liftSubstEq' vF' (urefl Vσσ')).
    instValid Vσσ'; instValid (urefl Vσσ'); instValid Vuσ ; instValid Vuσ'; escape.
    pose proof (irrelevanceTy (validSnoc vΓ vF)
                  (validSnoc (l := zero) vΓ vF0)
                  (univValid (l' := zero) _ _ vGU)) as vG0.
    pose proof (irrelevanceTy (validSnoc vΓ vF')
                  (validSnoc (l := zero) vΓ vF'0)
                  (univValid (l' := zero) _ _ vG'U)) as vG'0.
    unshelve econstructor ; cbn.
    1,2: econstructor; [apply redtmwf_refl; cbn; now eapply ty_prod| constructor].
    - unshelve refine (LRCumulative (PiRed _ _ _ tΔ Vσσ')).
      all: unshelve eapply univValid; tea; try irrValid.
    - now eapply convtm_prod.
    - unshelve refine (LRCumulative (PiRed _ _ _ tΔ (urefl Vσσ'))).
      all: unshelve eapply univValid; tea; try irrValid.
    - enough ([ Δ ||-< zero > (tProd F G)[σ] ≅ (tProd F' G')[σ'] | PiRed vΓ vF0 vG0 tΔ Vσσ']) by irrelevanceCum.
      refine (PiEqRed2 vΓ vF0 vG0 vF'0 vG'0 _ _ tΔ Vσσ').
      + exact (univEqValid vΓ (UValid vΓ) vF0 vFF').
      + pose proof (univEqValid (validSnoc vΓ vF) vU (univValid (l' := zero) _ _ vGU) vGG') as vGG'0.
        refine (irrelevanceTyEq _ _ _ _ vGG'0).
  Qed.

End PiTmCongruence.


Section PiTmValidity.

  Context `{GenericTypingProperties}.
  Context {Γ F G} (VΓ : [||-v Γ])
    (VF : [ Γ ||-v< one > F | VΓ ])
    (VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ])
    (VFU : [ Γ ||-v< one > F : U | VΓ | UValid VΓ ])
    (VGU : [ Γ ,, F ||-v< one > G : U | validSnoc VΓ VF | VU ]) .

  Lemma PiValidU : [ Γ ||-v< one > tProd F G : U | VΓ | UValid VΓ ].
  Proof.
    now eapply lreflValidTm, PiCongTm.
  Qed.

End PiTmValidity.
