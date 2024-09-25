(** * LogRel.Normalisation: well-typed terms always reduce to a normal form. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeNeutralConv.
From LogRel Require Import LogicalRelation Validity Fundamental.
From LogRel.LogicalRelation Require Import Escape Neutral Induction ShapeView Reflexivity.
From LogRel.Substitution Require Import Escape Poly.

Record WN (t : term) := {
  wn_val : term;
  wn_red : [ t ⤳* wn_val ];
  wn_whnf : whnf wn_val;
}.

Lemma WN_wk : forall t (ρ : nat -> nat), WN t -> WN t⟨ρ⟩.
Proof.
intros * [r].
exists r⟨ρ⟩.
+ now apply credalg_wk.
+ now apply whnf_ren.
Qed.

Lemma WN_exp : forall t u, [t ⤳* u] -> WN u -> WN t.
Proof.
intros t u ? [r].
exists r; tea.
now etransitivity.
Qed.

Lemma WN_whnf : forall t, whnf t -> WN t.
Proof.
intros; exists t; tea.
reflexivity.
Qed.

Lemma WN_isFun : forall t, isFun t -> WN t.
Proof.
intros t []; apply WN_whnf; now constructor.
Qed.

Lemma WN_isPair : forall t, isPair t -> WN t.
Proof.
intros t []; apply WN_whnf; now constructor.
Qed.

Module Nf.

Definition nf : tag.
Proof.
constructor.
Qed.

#[export] Instance WfContextNf : WfContext nf := fun Γ => True.
#[export] Instance WfTypeNf : WfType nf := fun Γ A => True.
#[export] Instance TypingNf : Typing nf := fun Γ A t => True.
#[export] Instance ConvTypeNf : ConvType nf := fun Γ A B => WN A × WN B.
#[export] Instance ConvTermNf : ConvTerm nf := fun Γ A t u => WN t × WN u.
#[export] Instance ConvNeuConvNf : ConvNeuConv nf := fun Γ A m n => whne m × whne n.
#[export] Instance RedTypeNf : RedType nf := fun Γ A B => [A ⤳* B].
#[export] Instance RedTermNf : RedTerm nf := fun Γ A t u => [t ⤳* u].

#[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance TypingDeclProperties : TypingProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := nf) := {}.
Proof.
all: try (intros; split; apply WN_whnf; now constructor).
+ intros * []; now split.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * ? []; split; now apply WN_wk.
+ intros * ? ? []; split; now eapply WN_exp.
Qed.

#[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := nf) := {}.
Proof.
all: try (intros; split; apply WN_whnf; now constructor).
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * [] ?; now split.
+ intros * ? []; split; now apply WN_wk.
+ intros * ? ? ? ? ? ? []; split; now eapply WN_exp.
+ intros * ? []; split; now apply WN_whnf, whnf_whne.
+ intros * ? ? ? Hf ? Hg []; split.
  - apply WN_isFun; destruct Hf as [|? []]; now constructor.
  - apply WN_isFun; destruct Hg as [|? []]; now constructor.
+ intros * ? ? ? Hp ? Hp' ?; split; apply WN_isPair.
  - destruct Hp as [|? []]; now constructor.
  - destruct Hp' as [|? []]; now constructor.
Qed.

#[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := nf) := {}.
Proof.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * [] ?; now split.
+ intros * ? []; split; now apply whne_ren.
+ intros * []; assumption.
+ intros; split; constructor.
+ intros * [] ?; split; now constructor.
+ intros * ? ? ? []; split; now constructor.
+ intros * ? []; split; now constructor.
+ intros * []; split; now constructor.
+ intros * []; split; now constructor.
+ intros * ??????? []; split; now constructor.
Qed.

#[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := nf) := {}.
Proof.
all: try now (intros; apply redalg_one_step; constructor).
+ intros; now apply credalg_wk.
+ intros; eassumption.
+ now constructor.
+ intros; now apply redalg_app.
+ intros; now apply redalg_natElim.
+ intros; now apply redalg_natEmpty.
+ intros; now apply redalg_fst.
+ intros; now apply redalg_snd.
+ intros; now eapply redalg_idElim.
+ intros; assumption.
+ intros; reflexivity.
Qed.

#[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := nf) := {}.
Proof.
all: try now intros; eassumption.
+ intros; now apply credalg_wk.
+ constructor.
+ intros; reflexivity.
Qed.

#[export] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ _ _ := {}.

End Nf.

Section Normalisation.

  Import Nf DeclarativeTypingData.

  Corollary normalisation {Γ A t} : [Γ |-[de] t : A] -> WN t.
  Proof. 
    intros [???? H]%TermRefl%Fundamental.
    eapply (escapeTmEq (ta := nf)) in H as [].
    assumption.
  Qed.

  Corollary type_normalisation {Γ A} : [Γ |-[de] A] -> WN A.
  Proof. 
    intros [??? H]%TypeRefl%Fundamental.
    eapply (escapeEq (ta := nf)) in H as [].
    assumption.
  Qed.

End Normalisation.

Import DeclarativeTypingProperties.

Record cored t t' : Prop := { _ : [t' ⤳ t] }.

Theorem typing_acc_cored Γ t :
  well_formed Γ t ->
  Acc cored t.
Proof.
  intros [[] Hty].
  all: first [
    apply type_normalisation in Hty as [wh red] |
    apply normalisation in Hty as [wh red]].
  all: induction red.
  - econstructor.
    intros t' [red].
    exfalso.
    eapply whnf_nored ; tea.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
  - econstructor.
    intros t' [red].
    exfalso.
    now eapply whnf_nored.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
Qed.