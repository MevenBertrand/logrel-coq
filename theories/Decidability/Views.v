(** * LogRel.Decidability.Views: properties of the view-building functions. *)
From Coq Require Import Nat Lia.
From Equations Require Import Equations.
From PartialFun Require Import Monad PartialFun MonadExn.
From LogRel Require Import Utils BasicAst AutoSubst.Extra Context NormalForms Notations PropertiesDefinition DeclarativeTyping NeutralConvProperties.
From LogRel.Decidability Require Import Functions UntypedFunctions.

Import MonadNotations.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Import DeclarativeTypingProperties.

Lemma zip_can t s : ~ isCanonical (zip1 t s).
Proof.
  destruct s ; cbn.
  all: now intros c ; inversion c.
Qed.

Lemma isType_tm_view1 t e :
  build_tm_view1 t = tm_view1_type e ->
  isType t × ~ whne t.
Proof.
  intros H.
  destruct e ; cbn.
  all: split ; [ now econstructor | intros H' ; inversion H'].
Qed.

Lemma whnf_tm_view1_nat t e :
  build_tm_view1 t = tm_view1_nat e ->
  whnf t × ~ whne t.
Proof.
  intros H.
  destruct e ; cbn.
  all: split ; [ now econstructor | intros H' ; inversion H'].
Qed.


Lemma ty_view1_small_can T n : build_ty_view1 T = ty_view1_small n -> ~ isCanonical T.
Proof.
  destruct T ; cbn.
  all: inversion 1.
  all: inversion 1.
Qed.

Lemma tm_view1_neutral_can t n : build_nf_view1 t = nf_view1_ne n -> ~ isCanonical t.
Proof.
  destruct t ; cbn.
  all: inversion 1.
  all: inversion 1.
Qed.

Lemma ty_view2_neutral_can T V : build_nf_ty_view2 T V = ty_neutrals T V -> ~ isCanonical T × ~ isCanonical V.
Proof.
  destruct T, V ; cbn.
  all: inversion 1.
  all: split ; inversion 1.
Qed.


Lemma whnf_view3_ty_neutral_can s t u : build_nf_view3 (tSort s) t u = types s (ty_neutrals t u) -> ~ isCanonical t × ~ isCanonical u.
Proof.
  destruct t, u ; cbn.
  all: inversion 1.
  all: split ; inversion 1.
Qed.

Lemma whnf_view3_neutrals_can A t u :
  whnf A ->
  build_nf_view3 A t u = neutrals A t u ->
  [× isPosType A, ~ isCanonical t & ~ isCanonical u].
Proof.
  intros HA.
  simp build_nf_view3.
  destruct (build_ty_view1 A) eqn:EA ; cbn.
  all: try solve [inversion 1].
  1: match goal with | |- context [match ?t with | _ => _ end] => destruct t eqn:? ; cbn end ;
    try solve [inversion 1].
  all: simp build_nf_view3 ; cbn.
  all: destruct (build_nf_view1 t) eqn:? ; cbn.
  all: try solve [inversion 1].
  all: repeat (
    match goal with | |- context [match ?t with | _ => _ end] => destruct t eqn:? ; cbn end ;
    try solve [inversion 1]).
  all: intros _.
  all: split ; try solve [now eapply tm_view1_neutral_can].
  all: econstructor.
  eapply ty_view1_small_can in EA.
  destruct HA ; try easy.
  all: exfalso ; apply EA ; now constructor.
Qed.

Definition whne_ne_view1 {N} (w : whne N) : ne_view1 N :=
  match w with
  | whne_tRel => ne_view1_rel _
  | whne_tApp _ => ne_view1_dest _ (eApp _)
  | whne_tNatElim _ => ne_view1_dest _ (eNatElim _ _ _)
  | whne_tEmptyElim _ => ne_view1_dest _ (eEmptyElim _)
  | whne_tFst _ => ne_view1_dest _ eFst
  | whne_tSnd _ => ne_view1_dest _ eSnd
  | whne_tIdElim _ => ne_view1_dest _ (eIdElim _ _ _ _ _)
  end.

Lemma whne_ty_view1 {N} (w : whne N) : build_ty_view1 N = ty_view1_small (whne_ne_view1 w).
Proof.
  now destruct w.
Qed.

Lemma whne_nf_view1 {N} (w : whne N) : build_nf_view1 N = nf_view1_ne (whne_ne_view1 w).
Proof.
  now destruct w.
Qed.

Lemma whne_ty_view2 {M N} (wM : whne M) (wN : whne N) : build_nf_ty_view2 M N = ty_neutrals M N.
Proof.
  simp build_nf_ty_view2.
  unshelve erewrite ! whne_ty_view1 ; tea.
  now reflexivity.
Qed.

Lemma whne_nf_view3 P m n (wP : isPosType P) (wm : whne m) (wn : whne n) :
  build_nf_view3 P m n =
    (match wP with
    | UnivPos => types _ (ty_neutrals m n)
    | _ => neutrals _ m n
    end).
Proof.
  simp build_nf_view3.
  destruct wP ; cbn.
  2-4: unshelve erewrite whne_nf_view1 ; tea; cbn; now rewrite (whne_nf_view1 wn).
  - rewrite whne_ty_view2 ; cbn ; tea.
    reflexivity.
  - unshelve erewrite whne_ty_view1 ; tea.
    cbn.
    unshelve erewrite whne_nf_view1 ; tea ; cbn.
    destruct (build_nf_view1 _) eqn:e ; try easy.
    all: unshelve erewrite whne_nf_view1 in e ; tea.
    all: inversion e.
Qed.

Lemma ty_mismatch_hd_view Γ T V (tT : isType T) (tV : isType V) :
  build_nf_ty_view2 T V = ty_mismatch T V ->
  type_hd_view Γ tT tV = False.
Proof.
  destruct tT, tV ; cbn ; try reflexivity.
  all: simp build_nf_ty_view2 ; cbn.
  1-6: congruence.
  do 2 (unshelve erewrite whne_ty_view1 ; tea) ; cbn.
  congruence.
Qed.

Lemma univ_mismatch_hd_view Γ s T V (tT : isType T) (tV : isType V) :
  build_nf_view3 (tSort s) T V = types s (ty_mismatch T V) ->
  univ_hd_view Γ tT tV = False.
Proof.
  destruct tT, tV ; cbn ; try reflexivity.
  all: simp build_nf_view3 build_nf_ty_view2 ; cbn.
  1-5: intros [=].
  do 2 (unshelve erewrite whne_ty_view1 ; tea) ; cbn.
  discriminate.
Qed.

Lemma mismatch_hd_view Γ A t u (tA : isType A) :
  whnf t -> whnf u ->
  build_nf_view3 A t u = mismatch A t u ->
  (∑ (nft : isNat t) (nfu : isNat u), A = tNat × nat_hd_view Γ nft nfu = False) +
  (∑ (nft : isId t) (nfu : isId u) A' x y, A = tId A' x y × id_hd_view Γ A' x y nft nfu = False).
Proof.
  intros wt wu.
  destruct tA ; cbn.
  all: simp build_nf_view3 build_nf_ty_view2 ; cbn.
  all: try solve [intros [=]].
  - destruct (build_nf_view1 t), (build_nf_view1 u) ; cbn.
    all: try solve [intros [=]].
    all: destruct n ; cbn ; try solve [intros [=]].
    all: destruct n0 ; cbn ; try solve [intros [=]].
    all: unshelve (intros _ ; left ; do 2 eexists).
    all: try solve [constructor].
    1-8: econstructor ; eapply not_can_whne ; tea ; solve [now apply zip_can | intros c ; inversion c].
    all: now cbn.

  - destruct (build_nf_view1 t), (build_nf_view1 u) ; cbn.
    all: solve [intros [=]].

  - destruct (build_nf_view1 t), (build_nf_view1 u) ; cbn.
    all: try solve [intros [=]]. 
    all: destruct n ; cbn ; try solve [intros [=]].
    all: (intros _ ; right ; do 5 eexists).
    all: split ; [reflexivity|..].
    Unshelve.
    all: try solve [constructor].
    5-8: econstructor ; eapply not_can_whne ; tea ; solve [now apply zip_can | intros c ; inversion c].
    all: now cbn.
    
  - unshelve erewrite whne_ty_view1 ; tea ; cbn.
    destruct (build_nf_view1 t) ; cbn ; try solve [intros [=]].
    destruct (build_nf_view1 u) ; cbn ; solve [intros [=]].

Qed.

Definition ncan_ne_view1 {N} (w : ~ isCanonical N) : ne_view1 N.
Proof.
  destruct N.
  all: try solve [destruct w ; econstructor].
  - now constructor.
  - eapply (ne_view1_dest _ (eApp _)).
  - eapply (ne_view1_dest _ (eNatElim _ _ _)).
  - eapply (ne_view1_dest _ (eEmptyElim _)).
  - eapply (ne_view1_dest _ eFst).
  - eapply (ne_view1_dest _ eSnd).
  - eapply (ne_view1_dest _ (eIdElim _ _ _ _ _)).
Defined.


Lemma ncan_nf_view1 {N} (w : ~ isCanonical N) :
  build_nf_view1 N = nf_view1_ne (ncan_ne_view1 w).
Proof.
  destruct N ; cbn ; try reflexivity.
  all: destruct w ; econstructor.
Qed.

Lemma nf_view2_neutral_can t t' :
  build_nf_view2 t t' = neutrals2 t t' ->
  ~ isCanonical t /\ ~ isCanonical t'.
Proof.
  intros Heq.
  simp build_nf_view2 in Heq.
  destruct (build_nf_view1 t) as [? [] | | ? [] | | | ] eqn:Heqt ; cbn in Heq.
  all: destruct (build_nf_view1 t') as [? [] | | ? [] | | | ] eqn:Heqt' ; cbn in Heq.
  all: try solve [congruence].
  split.
  all: now eapply tm_view1_neutral_can.
Qed.

Definition nf_view2_rename (ρ : nat -> nat) {t t' : term} (v : nf_view2 t t') : nf_view2 t⟨ρ⟩ t'⟨ρ⟩ :=
  match v in nf_view2 x x' return nf_view2 x⟨ρ⟩ x'⟨ρ⟩ with
  | sorts2 s s' => sorts2 s s'
  | prods2 A A' B B' => prods2 A⟨ρ⟩ A'⟨ρ⟩ B⟨upRen_term_term ρ⟩ B'⟨upRen_term_term ρ⟩
  | nats2 => nats2
  | emptys2 => emptys2
  | sigs2 A A' B B' => sigs2 A⟨ρ⟩ A'⟨ρ⟩ B⟨upRen_term_term ρ⟩ B'⟨upRen_term_term ρ⟩
  | ids2 A A' x x' y y' => ids2 A⟨ρ⟩ A'⟨ρ⟩ x⟨ρ⟩ x'⟨ρ⟩ y⟨ρ⟩ y'⟨ρ⟩
  | lams2 A A' t t' => lams2 A⟨ρ⟩ A'⟨ρ⟩ t⟨upRen_term_term ρ⟩ t'⟨upRen_term_term ρ⟩
  | lam_ne2 A t n' => lam_ne2 A⟨ρ⟩ t⟨upRen_term_term ρ⟩ n'⟨ρ⟩
  | ne_lam2 n A' t' => ne_lam2 n⟨ρ⟩ A'⟨ρ⟩ t'⟨upRen_term_term ρ⟩
  | zeros2 => zeros2
  | succs2 t t' => succs2 t⟨ρ⟩ t'⟨ρ⟩
  | pairs2 A A' B B' t t' u u' =>
      pairs2 A⟨ρ⟩ A'⟨ρ⟩ B⟨upRen_term_term ρ⟩ B'⟨upRen_term_term ρ⟩ t⟨ρ⟩ t'⟨ρ⟩ u⟨ρ⟩ u'⟨ρ⟩
  | pair_ne2 A B t u n' => pair_ne2 A⟨ρ⟩ B⟨upRen_term_term ρ⟩ t⟨ρ⟩ u⟨ρ⟩ n'⟨ρ⟩
  | ne_pair2 n A' B' t' u' => ne_pair2 n⟨ρ⟩ A'⟨ρ⟩ B'⟨upRen_term_term ρ⟩ t'⟨ρ⟩ u'⟨ρ⟩
  | refls2 A A' x x' => refls2 A⟨ρ⟩ A'⟨ρ⟩ x⟨ρ⟩ x'⟨ρ⟩
  | neutrals2 n n' => neutrals2 n⟨ρ⟩ n'⟨ρ⟩
  | mismatch2 t u => mismatch2 t⟨ρ⟩ u⟨ρ⟩
  | anomaly2 t u => anomaly2 t⟨ρ⟩ u⟨ρ⟩
  end.

Lemma build_nf_view2_rename ρ t t' : build_nf_view2 t⟨ρ⟩ t'⟨ρ⟩ = nf_view2_rename ρ (build_nf_view2 t t').
Proof.
  destruct t, t' ; reflexivity.
Qed.

Definition ne_view2_rename (ρ : nat -> nat) {t t' : term} (v : ne_view2 t t') : ne_view2 t⟨ρ⟩ t'⟨ρ⟩ :=
  match v in ne_view2 x x' return ne_view2 x⟨ρ⟩ x'⟨ρ⟩ with
  | ne_rels n n' => ne_rels (ρ n) (ρ n')
  | ne_apps f u f' u' => ne_apps f⟨ρ⟩ u⟨ρ⟩ f'⟨ρ⟩ u'⟨ρ⟩
  | ne_nats n P hz hs n' P' hz' hs' => ne_nats
      n⟨ρ⟩ P⟨upRen_term_term ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩
      n'⟨ρ⟩ P'⟨upRen_term_term ρ⟩ hz'⟨ρ⟩ hs'⟨ρ⟩
  | ne_emptys n P n' P' => ne_emptys n⟨ρ⟩ P⟨upRen_term_term ρ⟩ n'⟨ρ⟩ P'⟨upRen_term_term ρ⟩
  | ne_fsts p p' => ne_fsts p⟨ρ⟩ p'⟨ρ⟩
  | ne_snds p p' => ne_snds p⟨ρ⟩ p'⟨ρ⟩
  | ne_ids A x P hr y e A' x' P' hr' y' e' => ne_ids
    A⟨ρ⟩ x⟨ρ⟩ P⟨upRen_term_term (upRen_term_term ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩ e⟨ρ⟩
    A'⟨ρ⟩ x'⟨ρ⟩ P'⟨upRen_term_term (upRen_term_term ρ)⟩ hr'⟨ρ⟩ y'⟨ρ⟩ e'⟨ρ⟩
  | ne_mismatch t u => ne_mismatch t⟨ρ⟩ u⟨ρ⟩
  | ne_anomaly t u => ne_anomaly t⟨ρ⟩ u⟨ρ⟩
  end.

Lemma build_ne_view2_rename ρ t t' : build_ne_view2 t⟨ρ⟩ t'⟨ρ⟩ = ne_view2_rename ρ (build_ne_view2 t t').
Proof.
  destruct t, t' ; reflexivity.
Qed.

Lemma mismatch2_hd_view_ty Γ T V (tT : isType T) (tV : isType V) :
  build_nf_view2 T V = mismatch2 T V ->
  type_hd_view Γ tT tV = False.
Proof.
  destruct tT, tV ; cbn ; try reflexivity.
  all: simp build_nf_view2 ; cbn.
  1-6: congruence.
  do 2 (unshelve erewrite whne_nf_view1 ; tea ; cbn).
  congruence.
Qed.