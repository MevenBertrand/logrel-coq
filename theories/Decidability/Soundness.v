(** * LogRel.Decidability.Soundness: the implementations imply the inductive predicates. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction GenericTyping NormalForms.
From LogRel Require Import AlgorithmicTyping.
From LogRel.Decidability Require Import Functions.
From PartialFun Require Import Monad PartialFun MonadExn.

Import AlgorithmicTypingData.

Set Universe Polymorphism.

Section RedImplemSound.

Lemma zip_ored t t' π : [t ⤳ t'] -> [zip t π ⤳ zip t' π].
Proof.
  intros Hred.
  induction π as [|[]] in t, t', Hred |- * ; cbn in *.
  1: eassumption.
  all: apply IHπ ; now econstructor.
Qed.

Lemma zip_red t t' π : [t ⤳* t'] -> [zip t π ⤳* zip t' π].
Proof.
  induction 1.
  1: reflexivity.
  econstructor ; tea.
  now eapply zip_ored.
Qed.

Lemma red_stack_sound :
  funrect wh_red_stack (fun _ => True) (fun '(t,π) t' => [zip t π ⤳* t']).
Proof.
  intros ? _.
  funelim (wh_red_stack _).
  all: cbn ; econstructor ; try eauto.
  all: intros v ?.
  all: etransitivity ; [..|eassumption].
  all: eapply zip_red.
  all: econstructor ; [..|reflexivity].
  all: now econstructor.
Qed.

Lemma stack_ne n π :
  whne n -> whne (zip n π).
Proof.
  intros Hne.
  induction π as [|[]] in n, Hne |- * ; cbn.
  1: eassumption.
  all: eapply IHπ ; now econstructor.
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

Lemma red_stack_whnf :
funrect wh_red_stack (fun _ => True) (fun '(t,π) t' => whnf t').
Proof.
  intros ? _.
  funelim (wh_red_stack _).
  all: cbn ; try solve [constructor ; eauto]. 
  - now eapply isType_whnf, isType_tm_view1.
  - econstructor. eapply stack_ne.
    now econstructor.
  - now eapply whnf_tm_view1_nat.
Qed.

Corollary _red_sound :
  funrect wh_red (fun _ => True) (fun t t' => [t ⤳* t'] × whnf t').
Proof.
  intros ? _.
  cbn; intros ? H; split.
  - eapply funrect_graph in H.
    2: exact red_stack_sound. (* apply fails !? *)
    all: easy.
  - eapply funrect_graph in H.
    2: exact red_stack_whnf.
    all: easy.
Qed.

#[universes(polymorphic)]Corollary red_sound t t' :
  graph wh_red t t' ->
  [t ⤳* t'] × whnf t'.
Proof.
  intros H.
  eapply (funrect_graph wh_red _ _ _ _ _red_sound). (* weird universe inconsistency? *)
  1: easy.
  eassumption.
Qed.

End RedImplemSound.

Section CtxAccessCorrect.

  Lemma ctx_access_sound Γ n d :
    ctx_access Γ n = success d ->
    in_ctx Γ n d.
  Proof.
    funelim (ctx_access Γ n).
    all: simp ctx_access ; cbn.
    - inversion 1.
    - inversion 1.
      now constructor.
    - destruct (ctx_access Γ n') ; cbn.
      all: inversion 1 ; subst.
      constructor.
      now apply H.
  Qed.

  Lemma ctx_access_complete Γ n d :
    in_ctx Γ n d ->
    ctx_access Γ n = success d.
  Proof.
    induction 1.
    all: simp ctx_access ; cbn.
    - reflexivity.
    - now rewrite IHin_ctx. 
  Qed.

  Corollary ctx_access_correct Γ n d :
    in_ctx Γ n d <~> (ctx_access Γ n = success d).
  Proof.
    split.
    - eapply ctx_access_complete.
    - eapply ctx_access_sound.
  Qed.

End CtxAccessCorrect.

Ltac funelim_conv :=
  funelim (_conv _); 
    [ funelim (conv_ty _) | funelim (conv_ty_red _) | 
      funelim (conv_tm _) | funelim (conv_tm_red _) | 
      funelim (conv_ne _) | funelim (conv_ne_red _) ].

Section ConversionSound.


  #[universes(polymorphic)]Definition conv_sound_type
    (x : conv_full_dom)
    (r : conv_full_cod x) : Type :=
  match x, r with
  | _, (exception _) => True
  | (ty_state;Γ;_;T;V), (success _) =>  [Γ |-[al] T ≅ V]
  | (ty_red_state;Γ;_;T;V), (success _) => [Γ |-[al] T ≅h V]
  | (tm_state;Γ;A;t;u), (success _) => [Γ |-[al] t ≅ u : A]
  | (tm_red_state;Γ;A;t;u), (success _) =>
      whnf A -> whnf t -> whnf u -> [Γ |-[al] t ≅h u : A]
  | (ne_state;Γ;_;m;n), (success T) => [Γ |-[al] m ~ n ▹ T]
  | (ne_red_state;Γ;_;m;n), (success T) => [Γ |-[al] m ~h n ▹ T] × whnf T
  end.

  Lemma _implem_conv_sound :
    funrect _conv (fun _ => True) conv_sound_type.
  Proof.
    intros x _.
    funelim_conv ; cbn.
    all: intros ; simp conv_sound_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : exception _ _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => simp conv_sound_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : (_;_;_;_) = (_;_;_;_) |- _ => injection H; clear H; intros; subst 
      end).
    all: try solve [now econstructor].
    - econstructor ; tea.
      now econstructor.
    - econstructor ; tea.
      destruct H ; simp build_nf_view3 build_ty_view1 in Heq ; try solve [inversion Heq].
      all: try now econstructor.
    - econstructor; tea; [intuition (auto with *)| now rewrite 2!Weakening.wk1_ren_on].
    - eapply convne_meta_conv.
      2: reflexivity.
      + econstructor.
        now eapply ctx_access_correct.
      + f_equal.
        symmetry.
        now eapply Nat.eqb_eq.
    - split; tea. now econstructor.
  Qed.

  Arguments conv_full_cod _ /.
  Arguments conv_cod _/.

  Corollary implem_conv_sound Γ T V r :
    graph tconv (Γ,T,V) (success r) ->
    [Γ |-[al] T ≅ V].
  Proof.
    assert (funrect tconv (fun _ => True)
      (fun '(Γ,T,V) r => match r with | success _ => [Γ |-[al] T ≅ V] | _ => True end)) as Hrect.
    {
     intros ? _.
     funelim (tconv _) ; cbn.
     intros [] ; cbn ; [|easy].
     eintros ?%funrect_graph.
     2: now apply _implem_conv_sound.
     all: now cbn in *.
    }
    eintros ?%funrect_graph.
    2: eassumption.
    all: now cbn in *.
  Qed.

End ConversionSound.

Ltac funelim_typing :=
  funelim (typing _ _); 
    [ funelim (typing_inf _ _) | 
      funelim (typing_check _ _) |
      funelim (typing_inf_red _ _) | 
      funelim (typing_wf_ty _ _) ].

Section TypingSound.

  Variable conv : (context × term × term) ⇀ exn errors unit.

  Hypothesis conv_sound : forall Γ T V r,
    graph conv (Γ,T,V) (success r) ->
    [Γ |-[al] T ≅ V].

  Lemma ty_view1_small_can T n : build_ty_view1 T = ty_view1_small n -> ~ isCanonical T.
  Proof.
    destruct T ; cbn.
    all: inversion 1.
    all: inversion 1.
  Qed.

  #[universes(polymorphic)]Definition typing_sound_type
    (x : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term)
    (r : exn errors (tstate_output x.π1)) : Type :=
  match x, r with
  | _, (exception _) => True
  | (wf_ty_state;Γ;_;T), (success _) => [Γ |-[al] T]
  | (inf_state;Γ;_;t), (success T) => [Γ |-[al] t ▹ T]
  | (inf_red_state;Γ;_;t), (success T) => [Γ |-[al] t ▹h T]
  | (check_state;Γ;T;t), (success _) => [Γ |-[al] t ◃ T]
  end.

  Lemma _implem_typing_sound :
    funrect (typing conv) (fun _ => True) typing_sound_type.
  Proof.
    intros x _.
    funelim_typing ; cbn.
    all: intros ; simp typing_sound_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : exception _ _, _ => intros [|] ; simp typing_sound_type ; try easy ; cbn
      | |- _ -> _ => simp typing_sound_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; simp typing_sound_type ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : graph conv _ _ |- _ => eapply implem_conv_sound in H ; simp conv_sound_type in H
      | H : ctx_access _ _ = _ |- _ => eapply ctx_access_correct in H
      | H : (build_ty_view1 _ = ty_view1_small _) |- _ => eapply ty_view1_small_can in H
      | H : (_;_;_) = (_;_;_) |- _ => injection H; clear H; intros; subst 
      end).
    all: try now econstructor.
    econstructor; tea; now rewrite 2!Weakening.wk1_ren_on.
  Qed.

  Lemma implem_typing_sound x r:
    graph (typing conv) x r ->
    typing_sound_type x r.
  Proof.
    eapply funrect_graph.
    1: now apply _implem_typing_sound.
    easy.
  Qed.

  Lemma _check_ctx_sound :
    funrect (check_ctx conv) (fun _ => True) (fun Γ r => if r then [|- Γ] else True).
  Proof.
    intros ? _.
    funelim (check_ctx _ _) ; cbn.
    - now constructor.
    - split ; [easy|].
      intros [|] ; cbn ; try easy.
      intros ? [] ?%implem_typing_sound ; cbn in *.
      2: easy.
      now econstructor.
  Qed.
     
  Lemma check_ctx_sound Γ :
    graph (check_ctx conv) Γ (success tt) ->
    [|-[al] Γ].
  Proof.
    eintros ?%funrect_graph.
    2: eapply _check_ctx_sound.
    all: easy.
  Qed.

End TypingSound.