(** * LogRel.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening.

(** ** Reductions *)

(** *** One-step reduction. *)

Inductive OneRedAlg : term -> term -> Type :=
| BRed {A a t} :
    [ tApp (tLambda A t) a ⇒ t[a..] ]
| appSubst {t u a} :
    [ t ⇒ u ] ->
    [ tApp t a ⇒ tApp u a ]
| natElimSubst {P hz hs n n'} :
    [ n ⇒ n' ] ->
    [ tNatElim P hz hs n ⇒ tNatElim P hz hs n' ]
| natElimZero {P hz hs} :
    [ tNatElim P hz hs tZero ⇒ hz ]
| natElimSucc {P hz hs n} :
    [ tNatElim P hz hs (tSucc n) ⇒ tApp (tApp hs n) (tNatElim P hz hs n) ]
| emptyElimSubst {P e e'} :
    [e ⇒ e'] ->
    [tEmptyElim P e ⇒ tEmptyElim P e']        
| fstSubst {p p'} :
    [ p ⇒ p'] ->
    [ tFst p ⇒ tFst p']
| fstPair {A B a b} :
    [ tFst (tPair A B a b) ⇒ a ]
| sndSubst {p p'} :
    [ p ⇒ p'] ->
    [ tSnd p ⇒ tSnd p']
| sndPair {A B a b} :
    [ tSnd (tPair A B a b) ⇒ b ]
| termRedMapNilAlg {A A' B f} :
  [ tMap A B f (tNil A') ⇒ tNil B ]
| termRedMapConsAlg {A A' B f a l} :
  [ tMap A B f (tCons A' a l) ⇒ tCons B (tApp f a) (tMap A B f l) ]
| termRedMapUnderAlg {A B f l l'} :
  [ l ⇒ l' ] ->
  [ tMap A B f l ⇒ tMap A B f l' ]
| mapComp {A B B' C f g l} :
  whne l->
  [ tMap B C f (tMap A B' g l) ⇒ tMap A C (comp A f g) l]

where "[ t ⇒ t' ]" := (OneRedAlg t t') : typing_scope.

(* Keep in sync with OneRedTermDecl! *)

(** *** Multi-step reduction *)

Inductive RedClosureAlg : term -> term -> Type :=
  | redIdAlg {t} :
    [ t ⇒* t ]
  | redSuccAlg {t t' u} :
    [ t ⇒ t'] ->
    [ t' ⇒* u ] ->
    [ t ⇒* u ]
  where "[ t ⇒* t' ]" := (RedClosureAlg t t') : typing_scope.

#[export] Instance RedAlgTrans : PreOrder RedClosureAlg.
  Proof.
    split.
    - now econstructor.
    - intros * ; induction 1.
      1: easy.
      intros.
      now econstructor.
  Qed.

(** ** Properties *)

(** *** Weak-head normal forms do not reduce *)

Ltac inv_whne :=
  match goal with
  | [ H : whne _ |- _ ] => inversion H ; subst ; clear H
  | [ H : whne_list _ |- _ ] => inversion H ; subst ; clear H
  end.

Lemma whne_nored n u :
  whne n -> [n ⇒ u] -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  all: solve [repeat (inv_whne ; auto)].
Qed.

Lemma whnf_nored n u :
  whnf n -> [n ⇒ u] -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
  all: inversion nf ; subst ; inv_whne.
  all: try solve [apply IHred ; now constructor].
  all: try solve [do 2 (inv_whne ; auto)].
  all: inv_whne ; apply IHred ; now constructor.
Qed.

(** *** Determinism of reduction *)

Lemma ored_det {t u v} :
  [t ⇒ u] -> [t ⇒ v] ->
  u = v.
Proof.
  intros red red'.
  induction red in v, red' |- *.
  - inversion red' ; subst ; clear red'.
    + reflexivity.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
  - inversion red' ; subst ; clear red'.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
    + f_equal.
      eauto.
  - inversion red'; subst.
    2,3: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst.
    f_equal; eauto.
  - inversion red'; subst; clear red'.
    1: f_equal; now eapply IHred.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; clear red'.
    1: f_equal; now eapply IHred.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red' ; subst ; clear red'.
    2: exfalso; eapply whnf_nored; tea; constructor.
    reflexivity.
  - inversion red' ; subst ; clear red'.
    2: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto.
  - inversion red' ; subst ; clear red'.
    1,2: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto.
Qed.

Lemma red_whne t u : [t ⇒* u] -> whne t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whne_nored.
Qed.

Lemma red_whnf t u : [t ⇒* u] -> whnf t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whnf_nored.
Qed.

Lemma whred_red_det t u u' :
  whnf u ->
  [t ⇒* u] -> [t ⇒* u'] ->
  [u' ⇒* u].
Proof.
  intros whnf red red'.
  induction red in whnf, u', red' |- *.
  - eapply red_whnf in red' as -> ; tea.
    now econstructor.
  - destruct red' as [? | ? ? ? o'].
    + now econstructor.
    + unshelve epose proof (ored_det o o') as <-.
      now eapply IHred.
Qed.

Corollary whred_det t u u' :
  whnf u -> whnf u' ->
  [t ⇒* u] -> [t ⇒* u'] ->
  u = u'.
Proof.
  intros.
  eapply red_whnf ; tea.
  now eapply whred_red_det.
Qed.

(** *** Stability by weakening *)

Lemma oredalg_wk (ρ : nat -> nat) (t u : term) :
[t ⇒ u] ->
[t⟨ρ⟩ ⇒ u⟨ρ⟩].
Proof.
  intros Hred.
  induction Hred in ρ |- *.
  all: try solve [cbn; asimpl; now econstructor].
  - cbn ; asimpl.
    evar (t' : term).
    replace (subst_term _ t) with t'.
    all: subst t'.
    1: econstructor.
    now asimpl.
Qed.

Lemma credalg_wk (ρ : nat -> nat) (t u : term) :
[t ⇒* u] ->
[t⟨ρ⟩ ⇒* u⟨ρ⟩].
Proof.
  induction 1 ; econstructor ; eauto using oredalg_wk.
Qed.

(** Derived rules *)

Lemma redalg_app {t t' u} : [t ⇒* t'] -> [tApp t u ⇒* tApp t' u].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_natElim {P hs hz t t'} : [t ⇒* t'] -> [tNatElim P hs hz t ⇒* tNatElim P hs hz t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_natEmpty {P t t'} : [t ⇒* t'] -> [tEmptyElim P t ⇒* tEmptyElim P t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_fst {t t'} : [t ⇒* t'] -> [tFst t ⇒* tFst t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_snd {t t'} : [t ⇒* t'] -> [tSnd t ⇒* tSnd t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_map {A B f t t'} : [t ⇒* t'] -> [tMap A B f t ⇒* tMap A B f t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_one_step {t t'} : [t ⇒ t'] -> [t ⇒* t'].
Proof. intros; econstructor;[tea|reflexivity]. Qed.