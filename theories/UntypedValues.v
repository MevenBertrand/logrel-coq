From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction GenericTyping.

Unset Elimination Schemes.

Inductive snf (r : term) : Type :=
  | snf_tSort {s} : [ r ⇒* tSort s ] -> snf r
  | snf_tProd {A B} : [ r ⇒* tProd A B ] -> snf A -> snf B -> snf r
  | snf_tLambda {A t} : [ r ⇒* tLambda A t ] -> snf A -> snf t -> snf r
  | snf_tNat : [ r ⇒* tNat ] -> snf r
  | snf_tZero : [ r ⇒* tZero ] -> snf r
  | snf_tSucc {n} : [ r ⇒* tSucc n ] -> snf n -> snf r
  | snf_tEmpty : [ r ⇒* tEmpty ] -> snf r
  | snf_tSig {A B} : [r ⇒* tSig A B] -> snf A -> snf B -> snf r
  | snf_tPair {A B a b} : [r ⇒* tPair A B a b] -> snf A -> snf B -> snf a -> snf b -> snf r
  | snf_tList {A} : [ r ⇒* tList A ] -> snf A -> snf r
  | snf_tNil {A} : [ r ⇒* tNil  A ] -> snf A -> snf r
  | snf_tCons {A hd tl} : [r ⇒* tCons A hd tl ] -> snf A -> snf hd -> snf tl -> snf r
  | snf_sne {n} : [ r ⇒* n ] -> sne n -> snf r
  | snf_sne_list {n} : [r ⇒* n] -> sne_list n -> snf r
with sne (r : term) : Type :=
  | sne_tRel {v} : r = tRel v -> sne r
  | sne_tApp {n t} : r = tApp n t -> sne n -> snf t -> sne r
  | sne_tNatElim {P hz hs n} : r = tNatElim P hz hs n -> snf P -> snf hz -> snf hs -> sne n -> sne r
  | sne_tEmptyElim {P e} : r = tEmptyElim P e -> snf P -> sne e -> sne r
  | sne_tFst {p} : r = tFst p -> sne p -> sne r
  | sne_tSnd {p} : r = tSnd p -> sne p -> sne r
with sne_list (r : term) : Type :=
  | sne_tMap {A B f l} : r = tMap A B f l -> snf A -> snf B -> snf f -> sne l -> sne_list r
  | sne_list_sne : sne r -> sne_list r.

Set Elimination Schemes.

Scheme
  Induction for snf Sort Type with
  Induction for sne Sort Type with
  Induction for sne_list Sort Type.

Definition snf_rec
  (P : forall r : term, snf r -> Set)
  (Q : forall r : term, sne r -> Set)
  (R : forall r : term, sne_list r -> Set) := snf_rect P Q R.

Definition snf_ind
  (P : forall r : term, snf r -> Prop)
  (Q : forall r : term, sne r -> Prop)
  (R : forall r : term, sne_list r -> Prop) := snf_rect P Q R.

Definition sne_rec
  (P : forall r : term, snf r -> Set)
  (Q : forall r : term, sne r -> Set)
  (R : forall r : term, sne_list r -> Set) := sne_rect P Q R.

Definition sne_ind
  (P : forall r : term, snf r -> Prop)
  (Q : forall r : term, sne r -> Prop)
  (R : forall r : term, sne_list r -> Prop) := sne_rect P Q R.

Definition sne_list_rec
(P : forall r : term, snf r -> Set)
(Q : forall r : term, sne r -> Set)
(R : forall r : term, sne_list r -> Set) := sne_list_rect P Q R.

Definition sne_list_ind
(P : forall r : term, snf r -> Prop)
(Q : forall r : term, sne r -> Prop)
(R : forall r : term, sne_list r -> Prop) := sne_list_rect P Q R.

(* A&Y: add as many ps as you added new constructors for snf and sne in total *)
Definition snf_sne_rect P Q R p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 :=
  pair 
    (snf_rect P Q R p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22)
  (pair
    (sne_rect P Q R p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22)
    (sne_list_rect P Q R p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22)).

Lemma sne_whne : forall (t : term), sne t -> whne t.
Proof.
apply sne_rect with (P := fun _ _ => True) (P1 := fun _ _ => True); intros; subst; constructor; assumption.
Qed.

Lemma sne_whne_list : forall (t : term), sne_list t -> whne_list t.
Proof.
apply sne_list_rect with (P := fun _ _ => True) (P0 := fun _ _ => True) ; intros; subst; constructor.
all: eauto using sne_whne.
Qed.

Lemma snf_red : forall t u, [ t ⇒* u ] -> snf u -> snf t.
Proof.
intros t u Hr Hu; destruct Hu.
+ eapply snf_tSort.
  transitivity u; eassumption.
+ eapply snf_tProd.
  - transitivity u; eassumption.
  - assumption.
  - assumption.
+ eapply snf_tLambda.
  - transitivity u; eassumption.
  - assumption.
  - assumption.
+ eapply snf_tNat; transitivity u; eassumption.
+ eapply snf_tZero.
  transitivity u; eassumption.
+ eapply snf_tSucc.
  - transitivity u; eassumption.
  - assumption.
+ eapply snf_tEmpty; transitivity u; eassumption.
+ eapply snf_tSig.
  1: transitivity u; eassumption.
  all: tea.
+ eapply snf_tPair.
  1: transitivity u; eassumption.
  all: tea.
+ eapply snf_tList; tea; now etransitivity.
+ eapply snf_tNil; tea; now etransitivity.
+ eapply snf_tCons; [now etransitivity|..]; tea.
+ eapply snf_sne.
  - transitivity u; eassumption.
  - eassumption.
+ eapply snf_sne_list.
  - transitivity u; eassumption.
  - eassumption.
Qed.

Section RenSnf.

  Lemma snf_sne_ren :
    prod (forall t, snf t -> forall ρ, snf (t⟨ρ⟩))
    (prod (forall t, sne t -> forall ρ, sne (t⟨ρ⟩)) (forall t, sne_list t -> forall ρ, sne_list (t⟨ρ⟩))).
  Proof.
  apply snf_sne_rect.
  + intros r s Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tSort; eassumption.
  + intros r A B Hr HA IHA HB IHB ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tProd; eauto.
  + intros r A t Hr HA IHA Ht IHt ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tLambda; eauto.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tNat; eassumption.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tZero; eauto.
  + intros r t Hr Ht IHt ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tSucc; eauto.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tEmpty; eassumption.
  + intros r A B Hr ???? ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tSig; eauto.
  + intros r ???? Hr ???????? ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tPair; eauto.
  + intros r ? Hr ?? ρ.
    apply credalg_wk with (ρ := ρ) in Hr; cbn in *.
    eapply snf_tList; tea; eauto.
  + intros r ? Hr ?? ρ.
    apply credalg_wk with (ρ := ρ) in Hr; cbn in *.
    eapply snf_tNil; tea; eauto.
  + intros r ??? Hr ?????? ρ.
    apply credalg_wk with (ρ := ρ) in Hr; cbn in *.
    eapply snf_tCons; tea; eauto.
  + intros r n Hr Hn IHn ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_sne; eauto.
  + intros r n Hr Hn IHn ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_sne_list; eauto. 
  + intros r v -> ρ; econstructor; reflexivity.
  + intros r n t -> Hn IHn Ht IHt ρ.
    cbn; eapply sne_tApp; eauto.
  + intros r P hz hs n -> HP IHP Hhz IHhz Hhs IHhs Hn IHn ρ; cbn.
    eapply sne_tNatElim; eauto.
  + intros. subst. cbn.
    eapply sne_tEmptyElim; eauto.
  + intros r ? -> ???; cbn; eapply sne_tFst; eauto.
  + intros r ? -> ???; cbn; eapply sne_tSnd; eauto.
  + intros; subst; cbn.
    eapply sne_tMap; eauto.
  + intros n Hn IHn ρ.
    eapply sne_list_sne ; eauto. 
  Qed.

  Lemma sne_ren ρ t : sne t -> sne (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

  Lemma sne_list_ren ρ t : sne_list t -> sne_list (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

  Lemma snf_ren ρ t : snf t -> snf (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

End RenSnf.
