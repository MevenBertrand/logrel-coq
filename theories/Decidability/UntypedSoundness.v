(** * LogRel.Decidability.Soundness: the implementations imply the inductive predicates. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction GenericTyping NormalForms.
From LogRel Require Import AlgorithmicTyping UntypedAlgorithmicConversion.
From LogRel.Decidability Require Import Functions UntypedFunctions Soundness.
From PartialFun Require Import Monad PartialFun MonadExn.

Import AlgorithmicTypingData.

Set Universe Polymorphism.

Section ConversionSound.

  #[universes(polymorphic)]Definition uconv_sound_type
    (x : uconv_state × term × term)
    (r : exn errors unit) : Type :=
  match x, r with
  | _, (exception _) => True
  | (tm_state,t,u), (success _) =>  [t ≅ u]
  | (tm_red_state,t,u), (success _) =>
      whnf t -> whnf u -> [t ≅h u]
  | (ne_state,m,n), (success _) => [m ~ n]
  end.

  Lemma _implem_uconv_sound :
    funrect _uconv (fun _ => True) uconv_sound_type.
  Proof.
    intros x _.
    funelim (_uconv _); 
      [ funelim (uconv_tm _) | funelim (uconv_tm_red _) | funelim (uconv_ne _) ].
    all: intros ; cbn ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : exn _ _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => cbn ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : (_,_,_) = (_,_,_) |- _ => injection H; clear H; intros; subst 
      end).
    all: try solve [now econstructor].
    1-4: econstructor ; tea.
    1-4: match goal with | H : whnf ?t |- whne ?t =>
      now destruct H ; simp build_nf_view3 build_ty_view1 in Heq ; try solve [inversion Heq]
      end.
    eapply Nat.eqb_eq in Heq as ->.
    now constructor.
  Qed.

  Corollary implem_conv_graph x r :
    graph _uconv x r ->
    uconv_sound_type x r.
  Proof.
    eapply funrect_graph.
    1: now apply _implem_uconv_sound.
    easy.
  Qed.

  Corollary implem_uconv_sound Γ T V :
    graph uconv (Γ,T,V) ok ->
    [T ≅ V].
  Proof.
    assert (funrect uconv (fun _ => True)
      (fun '(Γ,T,V) r => match r with | success _ => [T ≅ V] | _ => True end)) as Hrect.
    {
     intros ? _.
     funelim (uconv _) ; cbn.
     intros [] ; cbn ; [|easy].
     eintros ?%funrect_graph.
     2: now apply _implem_uconv_sound.
     all: now cbn in *.
    }
    eintros ?%funrect_graph.
    2: eassumption.
    all: now cbn in *.
  Qed.

End ConversionSound.