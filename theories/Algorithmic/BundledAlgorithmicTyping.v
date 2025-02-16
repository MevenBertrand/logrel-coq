(** * LogRel.BundledAlgorithmicTyping: algorithmic typing bundled with its pre-conditions, and a tailored induction principle. *)

From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicTyping.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences TypeConstructorsInj NeutralConvProperties.

Import DeclarativeTypingProperties AlgorithmicTypedConvData AlgorithmicTypingData.

(** ** Definition of bundled algorithmic typing *)

Definition bn : tag.
Proof.
constructor.
Qed.

Definition bni : tag.
Proof.
constructor.
Qed.

(** The idea of these definitions is to put together an algorithmic derivation with the
pre-conditions that ensure it is sensible. Indeed, for instance [Γ |-[al] A] does not
re-check that Γ is well-typed: in the algorithm, this information is instead maintained as
an invariant. But this means that algorithmic variants, do not unconditionally
imply its declarative counterpart, they only do so if their pre-conditions are fulfilled,
eg if the context or type are well-formed. *)

(** Also note that in the case of judgements that “output” a type, ie type inference and
neutral conversion, we allow for an arbitrary conversion to “rectify” the output type.
This makes it easier to handle these in the logical relation, because it means the interface
is stable by arbitrary conversion. *)

(** In the case of a context, there is no judgement, only a pre-condition, as algorithmic
typing never re-checks a context. *)

Record WfContextBun Γ :=
{
  bn_wf_ctx : [|-[de] Γ] ;
}.

Record WfTypeBun Γ A :=
{
  bun_wf_ty_ctx : [|-[de] Γ] ;
  bun_wf_ty : [Γ |-[al] A] ;
}.

Record InferBun Γ A t :=
{
  bun_inf_ctx : [|-[de] Γ] ;
  bun_inf : [Γ |-[al] t ▹ A]
}.

Record InferConvBun Γ A t :=
{
  bun_inf_conv_ctx : [|-[de] Γ] ;
  bun_inf_conv_ty : term ;
  bun_inf_conv_inf : [Γ |-[al] t ▹ bun_inf_conv_ty] ;
  (** Allows to change the type to any convertible one. *)
  bun_inf_conv_conv : [Γ |-[de] bun_inf_conv_ty ≅ A]
}.

Record InferRedBun Γ A t :=
{
  bun_inf_red_ctx : [|-[de] Γ] ;
  bun_inf_red : [Γ |-[al] t ▹h A]
}.

Record CheckBun Γ A t :=
{
  bun_chk_ctx : [|-[de] Γ] ;
  bun_chk_ty : [Γ |-[de] A] ;
  bun_chk : [Γ |-[al] t ◃ A]
}.

Record ConvTypeBun Γ A B :=
{
  bun_conv_ty_ctx : [|-[de] Γ] ;
  bun_conv_ty_l : [Γ |-[de] A] ;
  bun_conv_ty_r : [Γ |-[de] B] ;
  bun_conv_ty : [Γ |-[al] A ≅ B]
}.

Record ConvTypeRedBun Γ A B :=
{
  bun_conv_ty_red_ctx : [|-[de] Γ] ;
  bun_conv_ty_red_l : [Γ |-[de] A] ;
  bun_conv_ty_red_wh_l : isType A ;
  bun_conv_ty_red_r : [Γ |-[de] B] ;
  bun_conv_ty_red_wh_r : isType B ;
  bun_conv_ty_red : [Γ |-[al] A ≅h B]
}.

Record ConvTermBun Γ A t u :=
{
  bun_conv_tm_ctx : [|-[de] Γ] ;
  bun_conv_tm_ty : [Γ |-[de] A] ;
  bun_conv_tm_l : [Γ |-[de] t : A] ;
  bun_conv_tm_r : [Γ |-[de] u : A] ;
  bun_conv_tm : [Γ |-[al] t ≅ u : A]
}.

Record ConvTermRedBun Γ A t u :=
{
  bun_conv_tm_red_ctx : [|-[de] Γ] ;
  bun_conv_tm_red_ty : [Γ |-[de] A] ;
  bun_conv_tm_red_wh_ty : isType A ;
  bun_conv_tm_red_l : [Γ |-[de] t : A] ;
  bun_conv_tm_red_wh_l : whnf t ;
  bun_conv_tm_red_r : [Γ |-[de] u : A] ;
  bun_conv_tm_red_wh_r : whnf u ;
  bun_conv_tm_red : [Γ |-[al] t ≅h u : A]
}.

Record ConvNeuBun Γ A m n :=
{
  bun_conv_ne_ctx : [|-[de] Γ] ;
  bun_conv_ne_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_r : well_typed (ta := de) Γ n ;
  bun_conv_ne : [Γ |-[al] m ~ n ▹ A]
}.

Record ConvNeuRedBun Γ A m n :=
{
  bun_conv_ne_red_ctx : [|-[de] Γ] ;
  bun_conv_ne_red_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_red_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_red : [Γ |-[al] m ~h n ▹ A]
}.

Record ConvNeuConvBun Γ A m n :=
{
  bun_conv_ne_conv_ctx : [|-[de] Γ] ;
  bun_conv_ne_conv_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_conv_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_conv_ty : term ;
  bun_conv_ne_conv : [Γ |-[al] m ~ n ▹ bun_conv_ne_conv_ty] ;
  bun_conv_ne_conv_conv : [Γ |-[de] bun_conv_ne_conv_ty ≅ A]
}.

Record RedTypeBun Γ A B :=
{
  bun_red_ty_ctx : [|-[de] Γ] ;
  bun_red_ty_ty : [Γ |-[al] A] ;
  bun_red_ty : [A ⤳* B] ;
}.

Record OneStepRedTermBun Γ A t u :=
{
  bun_osred_tm_ctx : [|-[de] Γ] ;
  (** We do not have the instance yet, so we have to specify it by hand,
  but this really is [Γ |-[bn] t : A]. *)
  bun_osred_tm_tm : typing (ta := bn) (Typing := InferConvBun) Γ A t ;
  bun_osred_tm : [t ⤳ u]
}.

Record RedTermBun Γ A t u :=
{
  bun_red_tm_ctx : [|-[de] Γ] ;
  bun_red_tm_tm : typing (ta := bn) (Typing := InferConvBun) Γ A t ;
  bun_red_tm : [t ⤳* u] ;
}.

Record RedTypeBunI Γ A B :=
{
  buni_red_ty_ctx : [|-[de] Γ] ;
  buni_red_ty_ty : [Γ |-[de] A] ;
  buni_red_ty : [A ⤳* B] ;
}.

Record OneStepRedTermBunI Γ A t u :=
{
  buni_osred_tm_ctx : [|-[de] Γ] ;
  buni_osred_tm_tm : [Γ |-[de] t : A] ;
  buni_osred_tm : [t ⤳ u]
}.

Record RedTermBunI Γ A t u :=
{
  buni_red_tm_ctx : [|-[de] Γ] ;
  buni_red_tm_tm : [Γ |-[de] t : A] ;
  buni_red_tm : [t ⤳* u] ;
}.

(** ** Instances *)

(** We actually define two instances, one fully-algorithmic and one where only conversion
is algorithmic, but typing is not. This is needed because we cannot show right away that
(bundled) algorithmic typing has all the properties to be an instance of the generic interface.
The issue is that the logical relation does not give enough properties of neutrals, in particular
we cannot derive that neutral application is injective, ie if [tApp n u] and [tApp n' u'] are
convertible then [n] and [n'] are and so are [u] and [u']. Thus, we use the mixed instance, which
we can readily show, to gather more properties of conversion, enough to show the fully 
algorithmic one. *)

Module BundledTypingData.

  #[export] Instance WfContext_Bundle : WfContext bn := WfContextBun.
  #[export] Instance WfType_Bundle : WfType bn := WfTypeBun.
  #[export] Instance Inferring_Bundle : Inferring bn := InferBun. 
  #[export] Instance InferringRed_Bundle : InferringRed bn := InferRedBun.
  #[export] Instance Typing_Bundle : Typing bn := InferConvBun.
  #[export] Instance Checking_Bundle : Checking bn := CheckBun.
  #[export] Instance ConvType_Bundle : ConvType bn := ConvTypeBun.
  #[export] Instance ConvTypeRed_Bundle : ConvTypeRed bn :=  ConvTypeRedBun.
  #[export] Instance ConvTerm_Bundle : ConvTerm bn := ConvTermBun.
  #[export] Instance ConvTermRed_Bundle : ConvTermRed bn := ConvTermRedBun.
  #[export] Instance ConvNeu_Bundle : ConvNeu bn := ConvNeuBun.
  #[export] Instance ConvNeuRed_Bundle : ConvNeuRed bn := ConvNeuRedBun.
  #[export] Instance ConvNeuConv_Bundle : ConvNeuConv bn := ConvNeuConvBun.
  #[export] Instance RedType_Bundle : RedType bn := RedTypeBun.
  #[export] Instance OneStepRedTerm_Bundle : OneStepRedTerm bn := OneStepRedTermBun.
  #[export] Instance RedTerm_Bundle : RedTerm bn := RedTermBun.

  Ltac fold_bun :=
    change WfContextBun with (wf_context (ta := bn)) in *;
    change WfTypeBun with (wf_type (ta := bn)) in *;
    change InferBun with (inferring (ta := bn)) in * ;
    change InferRedBun with (infer_red (ta := bn)) in * ;
    change InferConvBun with (typing (ta := bn)) in * ;
    change CheckBun with (check (ta := bn)) in * ;
    change ConvTypeBun with (conv_type (ta := bn)) in * ;
    change ConvTermBun with (conv_term (ta := bn)) in * ;
    change ConvNeuBun with (conv_neu (ta := bn)) in * ;
    change ConvTypeRedBun with (conv_type_red (ta := bn)) in * ;
    change ConvTermRedBun with (conv_term_red (ta := bn)) in * ;
    change ConvNeuRedBun with (conv_neu_red (ta := bn)) in *;
    change ConvNeuConvBun with (conv_neu_ty (ta := bn)) in *;
    change RedTypeBun with (red_ty (ta := bn)) in * ;
    change OneStepRedTermBun with (osred_tm (ta := bn)) in * ;
    change RedTermBun with (red_tm (ta := bn)) in *.

End BundledTypingData.

Import BundledTypingData.

Module BundledIntermediateData.

  #[export] Instance WfContext_BundleInt : WfContext bni := WfContextDecl.
  #[export] Instance WfType_BundleInt : WfType bni := WfTypeDecl.
  #[export] Instance Typing_BundleInt : Typing bni := TypingDecl.
  #[export] Instance ConvType_BundleInt : ConvType bni := ConvTypeBun.
  #[export] Instance ConvTerm_BundleInt : ConvTerm bni := ConvTermBun.
  #[export] Instance ConvNeuConv_BundleInt : ConvNeuConv bni := ConvNeuConvBun.
  #[export] Instance RedType_BundleInt : RedType bni := RedTypeBunI.
  #[export] Instance OneStepRedTerm_BundleInt : OneStepRedTerm bni := OneStepRedTermBunI.
  #[export] Instance RedTerm_BundleInt : RedTerm bni := RedTermBunI.

  Ltac unfold_bni :=
    change (wf_context (ta := bni)) with (wf_context (ta := de)) in *;
    change (wf_type (ta := bni)) with (wf_type (ta := de)) in *;
    change (typing (ta := bni)) with (typing (ta := de)) in * ;
    change (conv_type (ta := bni)) with (conv_type (ta := bn)) in * ;
    change (conv_term (ta := bni)) with (conv_term (ta := bn)) in * ;
    change (conv_neu_ty (ta := bni)) with (conv_neu_ty (ta := bn)) in *.

End BundledIntermediateData.

Set Universe Polymorphism.

(** ** Invariants of algorithmic typing (aka McBride discipline):
  for each rule,
  - assuming pre-conditions to the conclusion and post-conditions of previous premises
    implies the pre-condition of a premise;
  - assuming pre-conditions to the conclusion and post-conditions of all premises
    implies the post-condition of the conclusion.

  This is so regular that the statements used to be generated using meta-programming.
  This is not the case anymore to avoid a nasty dependency on MetaCoq which caused
  proof engineering problems in places, but might be added again in the future.
    
  These lemmas are proven one by one rather than "inlined" in a proof of soundness
  because they appear again and again, when working with the untyped algorithm, and
  the functions.

*)

Section Invariants.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

  Lemma typeConvRed_prem2 (Γ : context) (A A' B B' : term) :
    [A ⤳* A'] ->
    [B ⤳* B'] ->
    [Γ |-[ de ] A] × [Γ |-[ de ] B] ->
    [Γ |-[ de ] A'] × [Γ |-[ de ] B'].
  Proof.
    intros * HA HB [].
    eapply subject_reduction_type, reddecl_conv in HA, HB ; tea.
    split ; boundary.
  Qed.

  Lemma typeConvRed_concl (Γ : context) (A A' B B' : term) :
    [A ⤳* A'] ->
    [B ⤳* B'] ->
    [Γ |-[ de ] A' ≅ B'] ->
    [Γ |-[ de ] A] × [Γ |-[ de ] B] ->
    [Γ |-[ de ] A ≅ B].
  Proof.
    intros * HA HB IHA' [? ?].
    eapply subject_reduction_type, reddecl_conv in HA, HB ; tea.
    do 2 etransitivity ; tea.
    all: now econstructor.
  Qed.

  Lemma typePiCongAlg_prem0 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] tProd A B] × [Γ |-[ de ] tProd A' B'] ->
    [Γ |-[ de ] A] × [Γ |-[ de ] A'].
  Proof.
    now intros * [[]%prod_ty_inv []%prod_ty_inv].
  Qed.

  Lemma typePiCongAlg_prem1 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A'] ->
    [Γ |-[ de ] tProd A B] × [Γ |-[ de ] tProd A' B'] ->
    [Γ,, A |-[ de ] B] × [Γ,, A |-[ de ] B'].
  Proof.
    intros * ? [[]%prod_ty_inv []%prod_ty_inv].
    split ; [gen_typing|..].
    now eapply stability1.
  Qed.
  
  Lemma typePiCongAlg_concl (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A'] ->
    [Γ,, A |-[ de ] B ≅ B'] ->
    [Γ |-[ de ] tProd A B] × [Γ |-[ de ] tProd A' B'] ->
    [Γ |-[ de ] tProd A B ≅ tProd A' B'].
  Proof.
    intros * ?? _.
    econstructor ; tea.
    boundary.
  Qed.

  Lemma typeSigCongAlg_prem0 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] tSig A B] × [Γ |-[ de ] tSig A' B'] ->
    [Γ |-[ de ] A] × [Γ |-[ de ] A'].
  Proof.
    now intros * [[]%sig_ty_inv []%sig_ty_inv].
  Qed.

  Lemma typeSigCongAlg_prem1 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A'] ->
    [Γ |-[ de ] tSig A B] × [Γ |-[ de ] tSig A' B'] ->
    [Γ,, A |-[ de ] B] × [Γ,, A |-[ de ] B'].
  Proof.
    intros * ? [[]%sig_ty_inv []%sig_ty_inv].
    split ; [gen_typing|..].
    now eapply stability1.
  Qed.
  
  Lemma typeSigCongAlg_concl (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A'] ->
    [Γ,, A |-[ de ] B ≅ B'] ->
    [Γ |-[ de ] tSig A B] × [Γ |-[ de ] tSig A' B'] ->
    [Γ |-[ de ] tSig A B ≅ tSig A' B'].
  Proof.
    intros * ?? _.
    econstructor ; tea.
    boundary.
  Qed.

  Lemma typeIdCongAlg_prem0 (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] tId A x y] × [Γ |-[ de ] tId A' x' y'] ->
    [Γ |-[ de ] A] × [Γ |-[ de ] A'].
  Proof.
    now intros * [[]%id_ty_inv []%id_ty_inv].
  Qed.
  
  Lemma typeIdCongAlg_prem1 (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] A ≅ A'] ->
    [Γ |-[ de ] tId A x y] × [Γ |-[ de ] tId A' x' y'] ->
    [Γ |-[ de ] x : A] × [Γ |-[ de ] x' : A].
  Proof.
    intros * ? [[]%id_ty_inv []%id_ty_inv].
    split ; [assumption|now econstructor].
  Qed.

  Lemma typeIdCongAlg_prem2 (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] A ≅ A'] ->
    [Γ |-[ de ] x ≅ x' : A] ->
    [Γ |-[ de ] tId A x y] × [Γ |-[ de ] tId A' x' y'] ->
    [Γ |-[ de ] y : A] × [Γ |-[ de ] y' : A].
  Proof.
    intros * ?? [[]%id_ty_inv []%id_ty_inv].
    split ; [assumption|now econstructor].
  Qed.

  Lemma typeIdCongAlg_concl (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] A ≅ A'] ->
    [Γ |-[ de ] x ≅ x' : A] ->
    [Γ |-[ de ] y ≅ y' : A] ->
    [Γ |-[ de ] tId A x y] × [Γ |-[ de ] tId A' x' y'] ->
    [Γ |-[ de ] tId A x y ≅ tId A' x' y'].
  Proof.
    intros * ??? [[]%id_ty_inv []%id_ty_inv].
    now econstructor.
  Qed.


  Lemma typeNeuConvAlg_prem2 (Γ : context) (M N : term) :
    whne M -> whne N ->
    [Γ |-[ de ] M] × [Γ |-[ de ] N] ->
    well_typed (ta := de) Γ M × well_typed (ta := de) Γ N.
  Proof.
    intros * ?? [?%neutral_ty_inv ?%neutral_ty_inv] ; tea.
    now split ; eexists.
  Qed.

  Lemma typeNeuConvAlg_concl (Γ : context) (M N T : term) :
    whne M ->
    whne N ->
    [× [Γ |-[ de ] M ≅ N : T], forall T' : term, [Γ |-[ de ] M : T'] -> [Γ |-[ de ] T ≅ T']
      & forall T' : term, [Γ |-[ de ] N : T'] -> [Γ |-[ de ] T ≅ T']] ->
    [Γ |-[ de ] M] × [Γ |-[ de ] N] -> [Γ |-[ de ] M ≅ N].
  Proof.
    intros * ?? [? HM] [?%neutral_ty_inv] ; tea.
    do 2 econstructor ; tea.
    now eapply HM.
  Qed.

  Lemma neuVarConvAlg_concl (Γ : context) (n : nat) (decl : term) :
    in_ctx Γ n decl ->
    well_typed (ta := de) Γ (tRel n) × well_typed (ta := de) Γ (tRel n) ->
    [× [Γ |-[ de ] tRel n ≅ tRel n : decl],
      forall T : term, [Γ |-[ de ] tRel n : T] -> [Γ |-[ de ] decl ≅ T]
      & forall T : term, [Γ |-[ de ] tRel n : T] -> [Γ |-[ de ] decl ≅ T]].
  Proof.
    intros * Hin [_ []].
    split.
    - do 2 constructor ; gen_typing.
    - intros T Hty.
      eapply termGen' in Hty as [? [[? [->]] ?]].
      eapply in_ctx_inj in Hin ; tea ; subst.
      eassumption.
    - intros T Hty.
      eapply termGen' in Hty as [? [[? [->]] ?]].
      eapply in_ctx_inj in Hin ; tea ; subst.
      eassumption.
  Qed.

  Lemma neuAppCongAlg_prem0 (Γ : context) (m n t u : term) :
    well_typed (ta := de) Γ (tApp m t) × well_typed (ta := de) Γ (tApp n u) ->
    well_typed (ta := de) Γ m × well_typed (ta := de) Γ n.
  Proof.
    intros * [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuAppCongAlg_prem1 (Γ : context) (m n t u A B : term) :
    [× [Γ |-[ de ] m ≅ n : tProd A B],
      forall T : term, [Γ |-[ de ] m : T] -> [Γ |-[ de ] tProd A B ≅ T]
      & forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tProd A B ≅ T]] ->
    well_typed (ta := de) Γ (tApp m t) × well_typed (ta := de) Γ (tApp n u) ->
    [Γ |-[ de ] t : A] × [Γ |-[ de ] u : A].
  Proof.
    intros * [? Hm Hn] [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    eapply prod_ty_inj in Hm as [] ; tea.
    eapply prod_ty_inj in Hn as [] ; tea.
    split ; now econstructor.
  Qed.

  Lemma neuAppCongAlg_concl (Γ : context) (m n t u A B : term) :
    [× [Γ |-[ de ] m ≅ n : tProd A B],
      forall T : term, [Γ |-[ de ] m : T] -> [Γ |-[ de ] tProd A B ≅ T]
      & forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tProd A B ≅ T]] ->
    [Γ |-[ de ] t ≅ u : A] ->
    well_typed (ta := de) Γ (tApp m t) × well_typed (ta := de) Γ (tApp n u) ->
    [× [Γ |-[ de ] tApp m t ≅ tApp n u : B[t..]],
      forall T : term, [Γ |-[ de ] tApp m t : T] -> [Γ |-[ de ] B[t..] ≅ T]
      & forall T : term, [Γ |-[ de ] tApp n u : T] -> [Γ |-[ de ] B[t..] ≅ T]].
  Proof.
    intros * [? Hm Hn] ? [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split.
    + econstructor ; gen_typing.
    + intros ? Happ.
      eapply termGen' in Happ as [? [(?&?&[-> Htym']) ?]].
      eapply prod_ty_inj in Hm as [] ; tea.
      etransitivity ; [..|eassumption].
      eapply typing_subst1 ; tea.
      now econstructor.
    + intros ? Happ.
      eapply termGen' in Happ as [? [(?&?&[-> Htym']) ?]].
      eapply prod_ty_inj in Hn as [] ; tea.
      etransitivity ; [..|eassumption].
      eapply typing_subst1.
      2: eassumption.
      econstructor ; tea.
      now symmetry.
  Qed.

  Lemma neuNatElimCong_prem0  (Γ : context) (n n' P P' hz hz' hs hs' : term) :
    well_typed (ta := de) Γ (tNatElim P hz hs n) ×
      well_typed (ta := de) Γ (tNatElim P' hz' hs' n') ->
    well_typed (ta := de) Γ n × well_typed (ta := de) Γ n'.
  Proof.
    intros * [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuNatElimCong_prem1 (Γ : context) (n n' P P' hz hz' hs hs' : term) :
    [× [Γ |-[ de ] n ≅ n' : tNat], forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tNat ≅ T]
      & forall T : term, [Γ |-[ de ] n' : T] -> [Γ |-[ de ] tNat ≅ T]] ->
    well_typed (ta := de) Γ (tNatElim P hz hs n) ×
      well_typed (ta := de) Γ (tNatElim P' hz' hs' n') ->
    [Γ,, tNat |-[ de ] P] × [Γ,, tNat |-[ de ] P'].
  Proof.
    intros * [? Hn Hn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    now split.
  Qed.

  Lemma neuNatElimCong_prem2 (Γ : context) (n n' P P' hz hz' hs hs' : term) :
    [× [Γ |-[ de ] n ≅ n' : tNat], forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tNat ≅ T]
      & forall T : term, [Γ |-[ de ] n' : T] -> [Γ |-[ de ] tNat ≅ T]] ->
    [Γ,, tNat |-[ de ] P ≅ P'] ->
    well_typed (ta := de) Γ (tNatElim P hz hs n) ×
      well_typed (ta := de) Γ (tNatElim P' hz' hs' n') ->
    [Γ |-[ de ] hz : P[tZero..]] × [Γ |-[ de ] hz' : P[tZero..]].
  Proof.
    intros * [? Hn Hn'] HP [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    1: eassumption.
    econstructor ; tea.
    symmetry.
    eapply typing_subst1 ; tea.
    gen_typing.
  Qed.

  Lemma neuNatElimCong_prem3 (Γ : context) (n n' P P' hz hz' hs hs' : term) :
    [× [Γ |-[ de ] n ≅ n' : tNat], forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tNat ≅ T]
      & forall T : term, [Γ |-[ de ] n' : T] -> [Γ |-[ de ] tNat ≅ T]] ->
    [Γ,, tNat |-[ de ] P ≅ P'] ->
    [Γ |-[ de ] hz ≅ hz' : P[tZero..]] ->
    well_typed (ta := de) Γ (tNatElim P hz hs n) ×
      well_typed (ta := de) Γ (tNatElim P' hz' hs' n') ->
    [Γ |-[ de ] hs : elimSuccHypTy P] × [Γ |-[ de ] hs' : elimSuccHypTy P].
  Proof.
    intros * [? Hn Hn'] HP _ [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    1: eassumption.
    econstructor ; tea.
    symmetry.
    eapply elimSuccHypTy_conv.
    all: gen_typing.
  Qed.

  Lemma neuNatElimCong_concl (Γ : context) (n n' P P' hz hz' hs hs' : term) :
    [× [Γ |-[ de ] n ≅ n' : tNat], forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tNat ≅ T]
      & forall T : term, [Γ |-[ de ] n' : T] -> [Γ |-[ de ] tNat ≅ T]] ->
    [Γ,, tNat |-[ de ] P ≅ P'] ->
    [Γ |-[ de ] hz ≅ hz' : P[tZero..]] ->
    [Γ |-[ de ] hs ≅ hs' : elimSuccHypTy P] ->
    well_typed (ta := de) Γ (tNatElim P hz hs n) ×
      well_typed (ta := de) Γ (tNatElim P' hz' hs' n') ->
    [× [Γ |-[ de ] tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : P[n..]],
      forall T : term, [Γ |-[ de ] tNatElim P hz hs n : T] -> [Γ |-[ de ] P[n..] ≅ T]
      & forall T : term, [Γ |-[ de ] tNatElim P' hz' hs' n' : T] -> [Γ |-[ de ] P[n..] ≅ T]].
  Proof.
    intros * [? Hn Hn'] HP ? ? [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    + now econstructor.
    + now intros ?[? [[->]]]%termGen'.
    + intros ?[? [[->]]]%termGen'.
      etransitivity.
      1: eapply typing_subst1.
      all: eassumption.
  Qed.

  Lemma neuEmptyElimCong_prem0 (Γ : context) (P P' e e' : term) :
    well_typed (ta := de) Γ (tEmptyElim P e) × well_typed (ta := de) Γ (tEmptyElim P' e') ->
    well_typed (ta := de) Γ e × well_typed (ta := de) Γ e'.
  Proof.
    intros * [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuEmptyElimCong_prem1 (Γ : context) (P P' e e' : term) :
    [× [Γ |-[ de ] e ≅ e' : tEmpty], forall T : term, [Γ |-[ de ] e : T] -> [Γ |-[ de ] tEmpty ≅ T]
      & forall T : term, [Γ |-[ de ] e' : T] -> [Γ |-[ de ] tEmpty ≅ T]] ->
    well_typed (ta := de) Γ (tEmptyElim P e) × well_typed (ta := de) Γ (tEmptyElim P' e') ->
    [Γ,, tEmpty |-[ de ] P] × [Γ,, tEmpty |-[ de ] P'].
  Proof.
    intros * [? Hn Hn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    now split.
  Qed.

  Lemma neuEmptyElimCong_concl (Γ : context) (P P' e e' : term) :
    [× [Γ |-[ de ] e ≅ e' : tEmpty], forall T : term, [Γ |-[ de ] e : T] -> [Γ |-[ de ] tEmpty ≅ T]
      & forall T : term, [Γ |-[ de ] e' : T] -> [Γ |-[ de ] tEmpty ≅ T]] ->
    [Γ,, tEmpty |-[ de ] P ≅ P'] ->
    well_typed (ta := de) Γ (tEmptyElim P e) × well_typed (ta := de) Γ (tEmptyElim P' e') ->
    [× [Γ |-[ de ] tEmptyElim P e ≅ tEmptyElim P' e' : P[e..]],
      forall T : term, [Γ |-[ de ] tEmptyElim P e : T] -> [Γ |-[ de ] P[e..] ≅ T]
      & forall T : term, [Γ |-[ de ] tEmptyElim P' e' : T] -> [Γ |-[ de ] P[e..] ≅ T]].
  Proof.
    intros * [? Hn Hn'] HP [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split.
    + now econstructor.
    + now intros ?[? [[->]]]%termGen'.
    + intros ?[? [[->]]]%termGen'.
      etransitivity.
      1: eapply typing_subst1.
      all: eassumption.
  Qed.

  Lemma neuFstCongAlg_prem0 (Γ : context) (m n : term) :
    well_typed (ta := de) Γ (tFst m) × well_typed (ta := de) Γ (tFst n) ->
    well_typed (ta := de) Γ m × well_typed (ta := de) Γ n.
  Proof.
    intros * [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuFstCongAlg_concl (Γ : context) (m n A B : term) :
    [× [Γ |-[ de ] m ≅ n : tSig A B],
      forall T : term, [Γ |-[ de ] m : T] -> [Γ |-[ de ] tSig A B ≅ T]
      & forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tSig A B ≅ T]] ->
    well_typed (ta := de) Γ (tFst m) × well_typed (ta := de) Γ (tFst n) ->
    [× [Γ |-[ de ] tFst m ≅ tFst n : A],
      forall T : term, [Γ |-[ de ] tFst m : T] -> [Γ |-[ de ] A ≅ T]
      & forall T : term, [Γ |-[ de ] tFst n : T] -> [Γ |-[ de ] A ≅ T]].
  Proof.
    intros * [? Hm Hn] [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split.
    + now econstructor.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hm as [].
      2: eassumption.
      now etransitivity.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hn as [].
      2: eassumption.
      now etransitivity.
  Qed.

  Lemma neuSndCongAlg_prem0 (Γ : context) (m n : term) :
    well_typed (ta := de) Γ (tSnd m) × well_typed (ta := de) Γ (tSnd n) ->
    well_typed (ta := de) Γ m × well_typed (ta := de) Γ n.
  Proof.
    intros * [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuSndCongAlg_concl  (Γ : context) (m n A B : term) :
    [× [Γ |-[ de ] m ≅ n : tSig A B],
      forall T : term, [Γ |-[ de ] m : T] -> [Γ |-[ de ] tSig A B ≅ T]
      & forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] tSig A B ≅ T]] ->
    well_typed (ta := de) Γ (tSnd m) × well_typed (ta := de) Γ (tSnd n) ->
    [× [Γ |-[ de ] tSnd m ≅ tSnd n : B[(tFst m)..]],
      forall T : term, [Γ |-[ de ] tSnd m : T] -> [Γ |-[ de ] B[(tFst m)..] ≅ T]
      & forall T : term, [Γ |-[ de ] tSnd n : T] -> [Γ |-[ de ] B[(tFst m)..] ≅ T]].
  Proof.
    intros * [? Hm Hn] [[? (?&(?&?&[->])&?)%termGen'] [? (?&(?&?&[->])&?)%termGen']].
    split.
    + now econstructor.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hm as [].
      2: eassumption.
      etransitivity; tea.
      eapply typing_subst1; tea ; do 2 econstructor.
      boundary.
    + intros ? ?%termGen' ; cbn in * ; prod_hyp_splitter ; subst.
      eapply sig_ty_inj in Hn as [].
      2: eassumption.
      etransitivity; tea.
      eapply typing_subst1; tea.
      now econstructor.
  Qed.

  Lemma neuIdElimCong_prem0 (Γ : context) (A A' x x' P P' hr hr' y y' e e' : term) :
    well_typed (ta := de) Γ (tIdElim A x P hr y e) ×
      well_typed (ta := de) Γ (tIdElim A' x' P' hr' y' e') ->
    well_typed (ta := de) Γ e × well_typed (ta := de) Γ e'.
  Proof.
    intros * [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']].
    split ; now eexists.
  Qed.

  Lemma neuIdElimCong_prem1 (Γ : context) (A A' A'' x x' x'' P P' hr hr' y y' y'' e e' : term) :
    [× [Γ |-[ de ] e ≅ e' : tId A'' x'' y''],
      forall T : term, [Γ |-[ de ] e : T] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T]
      & forall T : term, [Γ |-[ de ] e' : T] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T]] ->
    well_typed (ta := de) Γ (tIdElim A x P hr y e) ×
      well_typed (ta := de) Γ (tIdElim A' x' P' hr' y' e') ->
    [(Γ,, A),, tId A⟨wk1 (Γ := Γ) A⟩ x⟨wk1 (Γ := Γ) A⟩ (tRel 0) |-[ de ] P]
    × [(Γ,, A),, tId A⟨wk1 (Γ := Γ) A⟩ x⟨wk1 (Γ := Γ) A⟩ (tRel 0) |-[ de ] P'].
  Proof.
    intros * [? Hn Hn'] [[Hwn Hwn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']]]%dup.
    split.
    1: eassumption.
    epose proof (idElimConv Hwn Hwn') as (?&?&?&[]) ; tea.
    1: eapply TypeRefl ; refold ; boundary.
    1: constructor.
    eapply stability; tea.
    eapply idElimMotiveCtxConv; tea.
    1: eapply ctx_refl ; boundary.
    2: econstructor ; tea.
    all: now symmetry.
  Qed.

  Lemma neuIdElimCong_prem2 (Γ : context) (A A' A'' x x' x'' P P' hr hr' y y' y'' e e' : term) :
    [× [Γ |-[ de ] e ≅ e' : tId A'' x'' y''],
      forall T : term, [Γ |-[ de ] e : T] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T]
      & forall T : term, [Γ |-[ de ] e' : T] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T]] ->
    [(Γ,, A),, tId A⟨wk1 (Γ := Γ) A⟩ x⟨wk1 (Γ := Γ) A⟩ (tRel 0) |-[ de ] P ≅ P'] ->
    well_typed (ta := de) Γ (tIdElim A x P hr y e) ×
      well_typed (ta := de) Γ (tIdElim A' x' P' hr' y' e') ->
    [Γ |-[ de ] hr : P[tRefl A x .: x..]] × [Γ |-[ de ] hr' : P[tRefl A x .: x..]].
  Proof.
    intros * [? Hn Hn'] HP [[Hwn Hwn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']]]%dup.
    split.
    1: eassumption.
    epose proof (idElimConv Hwn Hwn') as (?&?&?&[]) ; tea.
    1: eapply TypeRefl ; refold ; boundary.
    1: constructor.
    econstructor ; tea.
    symmetry.
    eapply typing_subst2 ; tea.
    1: boundary.
    cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq; now econstructor.
  Qed.

  Lemma neuIdElimCong_concl (Γ : context) (A A' A'' x x' x'' P P' hr hr' y y' y'' e e' : term) :
    [× [Γ |-[ de ] e ≅ e' : tId A'' x'' y''],
      forall T : term, [Γ |-[ de ] e : T] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T]
      & forall T : term, [Γ |-[ de ] e' : T] -> [Γ |-[ de ] tId A'' x'' y'' ≅ T]] ->
    [(Γ,, A),, tId A⟨wk1 (Γ := Γ) A⟩ x⟨wk1 (Γ := Γ) A⟩ (tRel 0) |-[ de ] P ≅ P'] ->
    [Γ |-[ de ] hr ≅ hr' : P[tRefl A x .: x..]] ->
    well_typed (ta := de) Γ (tIdElim A x P hr y e) ×
      well_typed (ta := de) Γ (tIdElim A' x' P' hr' y' e') ->
    [× [Γ |-[ de ] tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : P[e .: y..]],
      forall T : term, [Γ |-[ de ] tIdElim A x P hr y e : T] -> [Γ |-[ de ] P[e .: y..] ≅ T]
      & forall T : term,
        [Γ |-[ de ] tIdElim A' x' P' hr' y' e' : T] -> [Γ |-[ de ] P[e .: y..] ≅ T]].
  Proof.
    intros * [? Hn Hn'] HP Hr [[Hwn Hwn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']]]%dup.
    epose proof (idElimConv Hwn Hwn') as (?&?&?&[He]) ; tea.
    1: eapply TypeRefl ; refold ; boundary.
    1: constructor.
    inversion_clear He.
    split.
    + econstructor ; tea.
      econstructor ; tea.
      symmetry.
      now econstructor.
    + now intros ?[? [[->]]]%termGen'.
    + intros ?[? [[->]]]%termGen'.
      etransitivity.
      2: eassumption.
      eapply typing_subst2 ; tea.
      1: boundary.
      econstructor ; tea.
      symmetry.
      cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
      now constructor.
  Qed.

  Lemma neuConvRed_prem0 (Γ : context) (m n : term) :
    well_typed (ta := de) Γ m × well_typed (ta := de) Γ n ->
    well_typed (ta := de) Γ m × well_typed (ta := de) Γ n.
  Proof.
    easy.
  Qed.

  Lemma neuConvRed_concl (Γ : context) (m n A A' : term) :
    [× [Γ |-[ de ] m ≅ n : A], forall T : term, [Γ |-[ de ] m : T] -> [Γ |-[ de ] A ≅ T]
      & forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] A ≅ T]] ->
    [A ⤳* A'] ->
    whnf A' ->
    well_typed (ta := de) Γ m × well_typed (ta := de) Γ n ->
    [× [Γ |-[ de ] m ≅ n : A'], forall T : term, [Γ |-[ de ] m : T] -> [Γ |-[ de ] A' ≅ T]
      & forall T : term, [Γ |-[ de ] n : T] -> [Γ |-[ de ] A' ≅ T]].
  Proof.
    eintros * [] ?%subject_reduction_type%reddecl_conv ? [].
    2: boundary.
    split.
    - now econstructor.
    - intros.
      etransitivity.
      2: eauto.
      now symmetry.
    - intros.
      etransitivity.
      2: eauto.
      now symmetry.
  Qed.

  Lemma termConvRed_prem3 (Γ : context) (t t' u u' A A' : term) :
    [A ⤳* A'] ->
    [t ⤳* t'] ->
    [u ⤳* u'] ->
    [Γ |-[ de ] t : A] × [Γ |-[ de ] u : A] -> [Γ |-[ de ] t' : A'] × [Γ |-[ de ] u' : A'].
  Proof.
    eintros * HA Ht Hu [].
    eapply subject_reduction_type, reddecl_conv in HA.
    2: boundary.
    eapply subject_reduction in Ht ; tea.
    eapply subject_reduction in Hu ; tea.
    split.
    all: econstructor ; tea.
    all: boundary.
  Qed.

  Lemma termConvRed_concl (Γ : context) (t t' u u' A A' : term) :
    [A ⤳* A'] ->
    [t ⤳* t'] ->
    [u ⤳* u'] ->
    [Γ |-[ de ] t' ≅ u' : A'] -> [Γ |-[ de ] t : A] × [Γ |-[ de ] u : A] -> [Γ |-[ de ] t ≅ u : A].
  Proof.
    eintros * HA Ht Hu ? [].
    eapply subject_reduction_type, reddecl_conv in HA.
    2: boundary.
    eapply subject_reduction, RedConvTeC in Ht ; tea.
    eapply subject_reduction, RedConvTeC in Hu ; tea.
    etransitivity ; tea.
    etransitivity.
    1: now econstructor.
    now symmetry.
  Qed.

  Lemma termPiCongAlg_prem0 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] tProd A B : U] × [Γ |-[ de ] tProd A' B' : U] ->
    [Γ |-[ de ] A : U] × [Γ |-[ de ] A' : U].
  Proof.
    intros * [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    now split.
  Qed.

  Lemma termPiCongAlg_prem1 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A' : U] ->
    [Γ |-[ de ] tProd A B : U] × [Γ |-[ de ] tProd A' B' : U] ->
    [Γ,, A |-[ de ] B : U] × [Γ,, A |-[ de ] B' : U].
  Proof.
    intros * ? [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    split.
    1: eassumption.
    eapply stability1 ; tea.
    now constructor.
  Qed.

  Lemma termPiCongAlg_concl (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A' : U] ->
    [Γ,, A |-[ de ] B ≅ B' : U] ->
    [Γ |-[ de ] tProd A B : U] × [Γ |-[ de ] tProd A' B' : U] ->
    [Γ |-[ de ] tProd A B ≅ tProd A' B' : U].
  Proof.
    intros.
    constructor ; tea.
    boundary.
  Qed.

  Lemma termSuccCongAlg_prem0 (Γ : context) (t t' : term) :
    [Γ |-[ de ] tSucc t : tNat] × [Γ |-[ de ] tSucc t' : tNat] ->
    [Γ |-[ de ] t : tNat] × [Γ |-[ de ] t' : tNat].
  Proof.
    now intros * [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
  Qed.
  
  Lemma termSuccCongAlg_concl (Γ : context) (t t' : term) :
    [Γ |-[ de ] t ≅ t' : tNat] ->
    [Γ |-[ de ] tSucc t : tNat] × [Γ |-[ de ] tSucc t' : tNat] ->
    [Γ |-[ de ] tSucc t ≅ tSucc t' : tNat].
  Proof.
    now constructor.
  Qed.

  Lemma termFunConvAlg_prem2 (Γ : context) (f g A B : term) :
    whnf f ->
    whnf g ->
    [Γ |-[ de ] f : tProd A B] × [Γ |-[ de ] g : tProd A B] ->
    [Γ,, A |-[ de ] tApp f⟨↑⟩ (tRel 0) : B] × [Γ,, A |-[ de ] tApp g⟨↑⟩ (tRel 0) : B].
  Proof.
    intros * ?? [?%typing_eta' ?%typing_eta'].
    now split.
  Qed.

  Lemma termFunConvAlg_concl (Γ : context) (f g A B : term) :
    whnf f ->
    whnf g ->
    [Γ,, A |-[ de ] tApp f⟨↑⟩ (tRel 0) ≅ tApp g⟨↑⟩ (tRel 0) : B] ->
    [Γ |-[ de ] f : tProd A B] × [Γ |-[ de ] g : tProd A B] -> [Γ |-[ de ] f ≅ g : tProd A B].
  Proof.
    intros * ?? ? [].
    etransitivity; [|now eapply TermFunEta].
    etransitivity; [symmetry; now eapply TermFunEta|].
    econstructor ; tea.
    2-3: constructor.
    all: boundary.
  Qed.

  Lemma termSigCongAlg_prem0 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] tSig A B : U] × [Γ |-[ de ] tSig A' B' : U] ->
    [Γ |-[ de ] A : U] × [Γ |-[ de ] A' : U].
  Proof.
    intros * [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    now split.
  Qed.

  Lemma termSigCongAlg_prem1 (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A' : U] ->
    [Γ |-[ de ] tSig A B : U] × [Γ |-[ de ] tSig A' B' : U] ->
    [Γ,, A |-[ de ] B : U] × [Γ,, A |-[ de ] B' : U].
  Proof.
    intros * ? [[? [[->] _]]%termGen' [? [[->] _]]%termGen'].
    split.
    1: eassumption.
    eapply stability1 ; tea.
    now constructor.
  Qed.

  Lemma termSigCongAlg_concl (Γ : context) (A B A' B' : term) :
    [Γ |-[ de ] A ≅ A' : U] ->
    [Γ,, A |-[ de ] B ≅ B' : U] ->
    [Γ |-[ de ] tSig A B : U] × [Γ |-[ de ] tSig A' B' : U] ->
    [Γ |-[ de ] tSig A B ≅ tSig A' B' : U].
  Proof.
    intros.
    constructor ; tea.
    boundary.
  Qed.

  Lemma termPairConvAlg_prem2 (Γ : context) (p q A B : term) :
    whnf p ->
    whnf q ->
    [Γ |-[ de ] p : tSig A B] × [Γ |-[ de ] q : tSig A B] ->
    [Γ |-[ de ] tFst p : A] × [Γ |-[ de ] tFst q : A].
  Proof.
    intros * ?? [].
    split.
    all: now econstructor.
  Qed.

  Lemma termPairConvAlg_prem3 (Γ : context) (p q A B : term) :
    whnf p ->
    whnf q ->
    [Γ |-[ de ] tFst p ≅ tFst q : A] ->
    [Γ |-[ de ] p : tSig A B] × [Γ |-[ de ] q : tSig A B] ->
    [Γ |-[ de ] tSnd p : B[(tFst p)..]] × [Γ |-[ de ] tSnd q : B[(tFst p)..]].
  Proof.
    intros * ?? ? [Hp ].
    split.
    1: now econstructor.
    econstructor.
    1: now econstructor.
    eapply typing_subst1.
    1: now symmetry.
    constructor.
    now eapply boundary, sig_ty_inv in Hp as [].
  Qed.

  Lemma termPairConvAlg_concl (Γ : context) (p q A B : term) :
    whnf p ->
    whnf q ->
    [Γ |-[ de ] tFst p ≅ tFst q : A] ->
    [Γ |-[ de ] tSnd p ≅ tSnd q : B[(tFst p)..]] ->
    [Γ |-[ de ] p : tSig A B] × [Γ |-[ de ] q : tSig A B] -> [Γ |-[ de ] p ≅ q : tSig A B].
  Proof.
    intros * ?? ? ? [Hp].
    etransitivity; [|now eapply TermPairEta].
    etransitivity; [symmetry; now eapply TermPairEta|].
    eapply boundary, sig_ty_inv in Hp as [].
    econstructor ; tea.
    all: constructor ; boundary.
  Qed.

  Lemma termIdCongAlg_prem0 (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] tId A x y : U] × [Γ |-[ de ] tId A' x' y' : U] ->
    [Γ |-[ de ] A : U] × [Γ |-[ de ] A' : U].
  Proof.
    now intros * [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
  Qed.
  
  Lemma termIdCongAlg_prem1 (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] A ≅ A' : U] ->
    [Γ |-[ de ] tId A x y : U] × [Γ |-[ de ] tId A' x' y' : U] ->
    [Γ |-[ de ] x : A] × [Γ |-[ de ] x' : A].
  Proof.
    intros * ? [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
    split.
    1: assumption.
    econstructor ; tea.
    now constructor. 
  Qed.

  Lemma termIdCongAlg_prem2  (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] A ≅ A' : U] ->
    [Γ |-[ de ] x ≅ x' : A] ->
    [Γ |-[ de ] tId A x y : U] × [Γ |-[ de ] tId A' x' y' : U] ->
    [Γ |-[ de ] y : A] × [Γ |-[ de ] y' : A].
  Proof.
    intros * ?? [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
    split.
    1: assumption.
    econstructor ; tea.
    now constructor. 
  Qed.

  Lemma termIdCongAlg_concl (Γ : context) (A A' x x' y y' : term) :
    [Γ |-[ de ] A ≅ A' : U] ->
    [Γ |-[ de ] x ≅ x' : A] ->
    [Γ |-[ de ] y ≅ y' : A] ->
    [Γ |-[ de ] tId A x y : U] × [Γ |-[ de ] tId A' x' y' : U] ->
    [Γ |-[ de ] tId A x y ≅ tId A' x' y' : U].
  Proof.
    intros * ??? [(?&[->]&?)%termGen' (?&[->]&?)%termGen'].
    now econstructor.
  Qed.

  Lemma termIdReflCong_concl (Γ : context) (A A' A'' x x' y y' : term) :
    [Γ |-[ de ] tRefl A x : tId A'' y y'] × [Γ |-[ de ] tRefl A' x' : tId A'' y y'] ->
    [Γ |-[ de ] tRefl A x ≅ tRefl A' x' : tId A'' y y'].
  Proof.
    intros * [[?[[-> ??] []%id_ty_inj]]%termGen' [?[[-> ??] []%id_ty_inj]]%termGen'].
    assert [Γ |-[de] A ≅ A'] by
        (etransitivity ; tea ; now symmetry).
    econstructor.
    1: econstructor.
    3: econstructor.
    + eassumption. 
    + etransitivity ; tea.
      symmetry.
      now econstructor.
    + now symmetry.
    + eassumption.
    + eassumption.
  Qed.

  Lemma termNeuConvAlg_prem0 (Γ : context) (m n P : term) :
    [Γ |-[ de ] m : P] × [Γ |-[ de ] n : P] ->
    well_typed (ta := de) Γ m × well_typed (ta := de) Γ n.
  Proof.
    intros * [].
    split ; now eexists.
  Qed.

  Lemma termNeuConvAlg_concl (Γ : context) (m n T P : term) :
    [× [Γ |-[ de ] m ≅ n : T], forall T' : term, [Γ |-[ de ] m : T'] -> [Γ |-[ de ] T ≅ T']
      & forall T' : term, [Γ |-[ de ] n : T'] -> [Γ |-[ de ] T ≅ T']] ->
    isPosType P -> [Γ |-[ de ] m : P] × [Γ |-[ de ] n : P] -> [Γ |-[ de ] m ≅ n : P].
  Proof.
    intros * [] ? [].
    now econstructor.
  Qed.

End Invariants.

(** ** Induction principle for bundled algorithmic conversion *)

(** We show an induction principle tailored for the bundled predicates: it threads the invariants
of the algorithm through the derivation, giving us stronger hypothesis in the minor premises,
corresponding to both the pre-conditions being true, and the post-conditions of the induction
hypotheses holding. *)

Section BundledConv.
  Universe u.

  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.


  Context (PTyEq PTyRedEq : context -> term -> term -> Type@{u})
  (PNeEq PNeRedEq PTmEq PTmRedEq : context -> term -> term -> term -> Type@{u}).

  (** Rather than writing by hand the various large statements of the induction principles,
  we use Ltac to derive them generically. Hopefully, there is no need to touch any part of
  this code when extending modifying the language with more features. *)
  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTyEq ?Γ ?A ?B] =>
        constr:([Γ |-[de] A] × [Γ |-[de] B] -> Hyp)
    | context [PTyRedEq ?Γ ?A ?B] =>
        constr:([Γ |-[de] A] × [Γ |-[de] B] -> Hyp)
    | context [PNeEq ?Γ ?A ?t ?u] =>
        constr:((well_typed (ta := de) Γ t) × (well_typed (ta := de) Γ u) -> Hyp)
    | context [PNeRedEq ?Γ ?A ?t ?u] =>
        constr:((well_typed (ta := de) Γ t) × (well_typed (ta := de) Γ u) -> Hyp)
    | context [PTmEq ?Γ ?A ?t ?u] =>
        constr:(([Γ |-[de] t : A]) × ([Γ |-[de] u : A]) -> Hyp)
    | context [PTmRedEq ?Γ ?A ?t ?u] =>
        constr:(([Γ |-[de] t : A]) × ([Γ |-[de] u : A]) -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTyEq ?Γ ?A ?B] =>
        context C [PTyEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PTyRedEq ?Γ ?A ?B] =>
        context C [PTyRedEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PNeEq ?Γ ?A ?m ?n] =>
        context C [PNeEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PNeRedEq ?Γ ?A ?m ?n] =>
        context C [PNeRedEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PTmEq ?Γ ?A ?t ?u] =>
        context C [PTmEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | context C [PTmRedEq ?Γ ?A ?t ?u] =>
        context C [PTmRedEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A ≅ ?B] => constr:([Γ |-[bn] A ≅ B])
      | [?Γ |-[al] ?A ≅h ?B] => constr:([Γ |-[bn] A ≅h B])
      | [?Γ |-[al] ?t ≅ ?u : ?A] => constr:([Γ |-[bn] t ≅ u : A])
      | [?Γ |-[al] ?t ≅h ?u : ?A] => constr:([Γ |-[bn] t ≅h u : A])
      | [?Γ |-[al] ?m ~ ?n ▹ ?A] => constr:([Γ |-[bn] m ~ n ▹ A])
      | [?Γ |-[al] ?m ~h ?n ▹ ?A] => constr:([Γ |-[bn] m ~h n ▹ A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  #[local] Definition algo_conv_discipline_stmt := 
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq)) in
      let ind := strong_statement t in
      exact ind).

  (** The main theorem *)
  Theorem algo_conv_discipline : algo_conv_discipline_stmt.
  Proof.
    unfold algo_conv_discipline_stmt; intros.
    apply AlgoConvInduction.
    - intros * ?? ? IHA [? Hconcl]%dup.
      eapply typeConvRed_prem2, IHA in Hconcl as [? [? Hpre2]%dup] ; eauto.
      eapply typeConvRed_concl in Hpre2 ; eauto.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply typePiCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply typePiCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply typePiCongAlg_concl in Hpre1 ; eauto.
    - intros * [].
      split ; [now eauto|..].
      now constructor.
    - intros * [].
      split ; [now eauto|..].
      now constructor.
    - intros * [].
      split ; [now eauto|..].
      now constructor.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply typeSigCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply typeSigCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply typeSigCongAlg_concl in Hpre1 ; eauto.
    - intros * ? IHA ? IHx ? IHy [? Hconcl]%dup.
      eapply typeIdCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply typeIdCongAlg_prem1, IHx in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply typeIdCongAlg_prem2, IHy in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply typeIdCongAlg_concl in Hpre2 ; eauto 20.
    - intros * ?? Hconv IH [? Hconcl]%dup.
      eapply typeNeuConvAlg_prem2, IH in Hconcl as [? [? Hpre2]%dup] ; eauto.
      eapply typeNeuConvAlg_concl in Hpre2 ; eauto.
    - intros * ? [? Hconcl]%dup.
      eapply neuVarConvAlg_concl in Hconcl ; eauto.
    - intros * ? IHm ? IHt [? Hconcl]%dup.
      eapply neuAppCongAlg_prem0, IHm in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuAppCongAlg_prem1, IHt in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuAppCongAlg_concl in Hpre1 ; eauto.
    - intros * ? IHn ? IHP ? IHz ? IHs [? Hconcl]%dup.
      eapply neuNatElimCong_prem0, IHn in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuNatElimCong_prem1, IHP in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuNatElimCong_prem2, IHz in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply neuNatElimCong_prem3, IHs in Hpre2 as [? [? Hpre3]%dup] ; eauto.
      eapply neuNatElimCong_concl in Hpre3 ; eauto 20.
    - intros * ? IHe ? IHP [? Hconcl]%dup.
      eapply neuEmptyElimCong_prem0, IHe in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuEmptyElimCong_prem1, IHP in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuEmptyElimCong_concl in Hpre1 ; eauto.
    - intros * ? IH [? Hconcl]%dup.
      eapply neuFstCongAlg_prem0, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuFstCongAlg_concl in Hpre0 ; eauto.
    - intros * ? IH [? Hconcl]%dup.
      eapply neuSndCongAlg_prem0, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuSndCongAlg_concl in Hpre0 ; eauto.
    - intros * ? IHn ? IHP ? IHe [? Hconcl]%dup.
      eapply neuIdElimCong_prem0, IHn in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply neuIdElimCong_prem1, IHP in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply neuIdElimCong_prem2, IHe in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply neuIdElimCong_concl in Hpre2 ; eauto 20.
    - intros * ? IHm ?? [? Hconcl]%dup.
      eapply IHm in Hconcl as [? [? Hpre0]]%dup.
      eapply neuConvRed_concl in Hpre0 as [? Hconcl]%dup ; eauto.
    - intros * ??? ? IH [? Hconcl]%dup.
      eapply termConvRed_prem3, IH in Hconcl as [? [? Hpre3]%dup] ; eauto.
      eapply termConvRed_concl in Hpre3 ; eauto.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply termPiCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termPiCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply termPiCongAlg_concl in Hpre1 ; eauto.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHt [? Hconcl]%dup.
      eapply termSuccCongAlg_prem0, IHt in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termSuccCongAlg_concl in Hpre0 ; eauto.
    - intros.
      split ; [eauto|..].
      now econstructor. 
    - intros * ??? IH [? Hconcl]%dup.
      eapply termFunConvAlg_prem2, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termFunConvAlg_concl in Hpre0 ; eauto.
    - intros * ? IHA ? IHB [? Hconcl]%dup.
      eapply termSigCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termSigCongAlg_prem1, IHB in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply termSigCongAlg_concl in Hpre1 ; eauto.
    - intros * ??? IHf ? IHs [? Hconcl]%dup.
      eapply termPairConvAlg_prem2, IHf in Hconcl as [? [? Hpre2]%dup] ; eauto.
      eapply termPairConvAlg_prem3, IHs in Hpre2 as [? [? Hpre3]%dup] ; eauto.
      eapply termPairConvAlg_concl in Hpre3 ; eauto.
    - intros * ? IHA ? IHx ? IHy [? Hconcl]%dup.
      eapply termIdCongAlg_prem0, IHA in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termIdCongAlg_prem1, IHx in Hpre0 as [? [? Hpre1]%dup] ; eauto.
      eapply termIdCongAlg_prem2, IHy in Hpre1 as [? [? Hpre2]%dup] ; eauto.
      eapply termIdCongAlg_concl in Hpre2 ; eauto 20.
    - intros * [? Hconcl]%dup.
      eapply termIdReflCong_concl in Hconcl ; eauto.
    - intros * ? IH ? [? Hconcl]%dup.
      eapply termNeuConvAlg_prem0, IH in Hconcl as [? [? Hpre0]%dup] ; eauto.
      eapply termNeuConvAlg_concl in Hpre0 ; eauto.
Qed.

  Definition BundledConvInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) in
      let t' := weak_statement t in exact t').

  (** As a corollary, we get the desired induction principle. The difference with the above one
  is that we do not get the post-condition of the algorithm in the conclusion, but this is
  in general not necessary. *)
  Corollary BundledConvInduction :
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat split.
    all: intros * [].
    all: now apply algo_conv_discipline.
  Qed.

End BundledConv.

(** ** Soundness of algorithmic conversion *)

(** Contrarily to the induction principle above, if we instantiate the main principle with
only constant true predicates, we get only the post-conditions, ie a soundness theorem: bundled algorithmic conversion judgments imply their declarative counterparts. *)

Section ConvSoundness.

  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

  Let PTyEq (Γ : context) (A B : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] B] ->
    [Γ |-[de] A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) :=
    [Γ |-[de] t : A] -> [Γ |-[de] u : A] ->
    [Γ |-[de] t ≅ u : A].
  Let PNeEq (Γ : context) (A : term) (m n : term) :=
    (well_typed (ta := de) Γ m) ->
    (well_typed (ta := de) Γ n) ->
    [× [Γ |-[de] m ≅ n : A],
      (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
      (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])].

  Theorem algo_conv_sound : AlgoConvInductionConcl PTyEq PTyEq PNeEq PNeEq PTmEq PTmEq.
  Proof.
    subst PTyEq PTmEq PNeEq.
    red.
    pose proof (algo_conv_discipline 
      (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)) as [H' H] ;
    cycle -1.
    1:{
      repeat (split ; [intros ; apply H' ; eauto |..] ; clear H' ; try destruct H as [H' H]).
      intros ; apply H ; eauto. 
    }
    all: now constructor.
  Qed.

  Corollary algo_conv_sound_ty Γ A B :
    [Γ |-[ de ] A] -> [Γ |-[ de ] B] -> [Γ |-[al] A ≅ B] -> [Γ |-[ de ] A ≅ B].
  Proof.
    now intros ???%algo_conv_sound.
  Qed.

End ConvSoundness.

Theorem bn_conv_sound
  `{!TypingSubst de}
  `{!TypeConstructorsInj de} :

  BundledConvInductionConcl
    (fun Γ A B => [Γ |-[de] A ≅ B])
    (fun Γ A B => [Γ |-[de] A ≅ B])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A])
    (fun Γ A t u => [Γ |-[de] t ≅ u : A]).
Proof.
  red.
  prod_splitter.
  all: intros * [].
  all: match goal with H : context [al] |- _ => eapply algo_conv_sound in H end.
  all: prod_hyp_splitter.
  all: try eassumption.
  all: now eexists.
Qed.

(** ** Induction principle for bundled algorithmic typing *)

(** This is repeating the same ideas as before, but for typing. *)

Section BundledTyping.

  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.
  Context `{ta : tag} `{ConvType ta}.

  Context (PTy : context -> term -> Type)
    (PInf PInfRed PCheck : context -> term -> term -> Type).

  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTy ?Γ ?A] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInf ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInfRed ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PCheck ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTy ?Γ ?A] =>
        context C [PTy Γ A × [Γ |-[de] A]]
    | context C [PInf ?Γ ?A ?t] =>
        context C [PInf Γ A t ×
          ([Γ |-[de] t : A] × forall T, [Γ |-[de] t : T] -> [Γ |-[de] A ≅ T])]
    | context C [PInfRed ?Γ ?A ?t] =>
        context C [PInfRed Γ A t × 
          ([Γ |-[de] t : A] × forall T, [Γ |-[de] t : T] -> [Γ |-[de] A ≅ T])]
    | context C [PCheck ?Γ ?A ?t] =>
        context C [PCheck Γ A t × [Γ |-[de] t : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[ta] ?A] => constr:([Γ |-[bn] A])
      | [?Γ |-[ta] ?t ▹ ?A] => constr:([Γ |-[bn] t ▹ A])
      | [?Γ |-[ta] ?t ▹h ?A] => constr:([Γ |-[bn] t ▹h A])
      | [?Γ |-[ta] ?t ◃ ?A] => constr:([Γ |-[bn] t ◃ A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  #[local] Ltac crush := repeat unshelve (
    match reverse goal with
      | IH : context [prod] |- _ => destruct IH as (?&IH) ; [..|shelve] ; prod_hyp_splitter ; gen_typing
    end) ;
  split ; prod_splitter ; [idtac|econstructor|..] ; eauto.

  (** The main theorem *)
  Theorem algo_typing_discipline : ltac:(
    let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
    let ind := strong_statement t in
    exact (
      (forall Γ A A', [Γ |-[de] A] -> [Γ |-[de] A'] -> [Γ |-[ta] A ≅ A'] -> [Γ |-[de] A ≅ A']) ->
      ind)).
  Proof.
    intros Hconv **.
    apply AlgoTypingInduction.
    1-7: intros ; crush.

    - intros * Hin ? ; crush.

      intros ? (?&(?&[-> ])&?)%termGen'.
      eapply in_ctx_inj in Hin ; tea ; subst.
      assumption.

    - intros * ? IHA ? IHB ? ; crush.
      1: eauto 10.

      intros ? (?&[-> ]&?)%termGen'.
      assumption.

    - intros * ? IHA ? IHt ? ; crush.
      
      intros ? (?&(?&[-> ])&?)%termGen'.
      etransitivity ; tea.
      constructor ; eauto.
      now eapply TypeRefl.

    - intros * ? IHI ? IHC ?.
    
      destruct IHI as [? [IHt]] ; tea.
      destruct IHC ; tea.
      1: now eapply boundary, prod_ty_inv in IHt as [].
      split ; [|split ; [econstructor|]] ; eauto.

      intros ? (?&(?&?&[->])&?)%termGen'.
      etransitivity ; tea.
      eapply typing_subst1 ; tea.
      1: now eapply TermRefl.
      now eapply prod_ty_inj.

    - intros.
      split ; [eauto|..].
      split ; [now econstructor|].
      now intros ? (?&[]&?)%termGen'.
    - intros.
      split ; [eauto|..].
      split ; [now econstructor|].
      now intros ? (?&[]&?)%termGen'.
    - intros.
      split ; [eauto|..].
      split ; [now econstructor|].
      now intros ? (?&[->]&?)%termGen'.
    
    - intros * ? IHn ? IHP ? IHz ? IHs ?.
      assert [|-[de] Γ,, tNat]
        by (econstructor ; tea ; now econstructor).
      assert [Γ |-[ de ] P[tZero..]].
      {
        eapply typing_subst1.
        1: now econstructor.
        now eapply IHP.
      }
      assert [Γ |-[de] elimSuccHypTy P]
        by now eapply elimSuccHypTy_ty.
      split ; [eauto 10 |..].
      split ; [econstructor|].
      + now eapply IHP.
      + now eapply IHz.
      + now eapply IHs.
      + now eapply IHn.
      + now intros ? (?&[->]&?)%termGen'.
    - intros.
      split ; [eauto|..].
      split ; [now econstructor|].
      now intros ? (?&->&?)%termGen'.
    - intros * ? IHe ? IHP ?.
      assert [|-[de] Γ,, tEmpty]
        by (econstructor ; tea ; now econstructor).
      split ; [eauto|..].
      split ; [econstructor|].
      + now eapply IHP.
      + now eapply IHe.
      + now intros ? (?&[->]&?)%termGen'.
    - intros * ? ihA ? ihB ?.
      edestruct ihA as (?&?&?); tea.
      edestruct ihB as (?&?&?).
      1: gen_typing.
      split; [eauto|..].
      split ; [econstructor|..] ; eauto.
      now intros ? (?&[->]&?)%termGen'.
    - intros * ? ihA ? ihB ? iha ? ihb ?.
      edestruct ihA as []; tea.
      edestruct ihB as [].
      1: gen_typing.
      edestruct iha as []; tea.
      edestruct ihb as []; tea.
      1: now eapply typing_subst1.
      split;[eauto 10|..].
      split ; [econstructor|..] ; eauto.
      now intros ? (?&[->]&?)%termGen'.
    - intros * ? ih ?.
      edestruct ih as (?&?&?); tea.
      split;[eauto|..].
      split ; [econstructor|..] ; eauto.
      intros ? (?&(?&?&[->])&?)%termGen'.
      etransitivity ; tea.
      now eapply sig_ty_inj.
    - intros * ? ih ?.
      edestruct ih as (?&?&?); tea.
      split;[eauto|..].
      split ; [econstructor|..] ; eauto.
      intros ? (?&(?&?&[->])&?)%termGen'.
      etransitivity ; tea.
      eapply typing_subst1.
      1: now eapply TermRefl ; econstructor.
      now eapply sig_ty_inj.
    - intros * ? ihA ? ihx ? ihy ?.
      edestruct ihA as []; tea.
      assert [Γ |-[de] A] by now econstructor.
      split; [eauto|].
      split.
      1: econstructor; [now eapply ihA | now eapply ihx | now eapply ihy].
      now intros ? (?&[->]&?)%termGen'.
    - intros * ? ihA ? ihx ?.
      assert [Γ |-[de] A] by now eapply ihA.
      split; [eauto|].
      split ; [econstructor; tea; now eapply ihx|..].
      now intros ? (?&[->]&?)%termGen'.
    - intros * ? ihA ? ihx ? ihP ? ihhr ? ihy ? ihe ?.
      assert [Γ |-[de] A] by now eapply ihA.
      assert [Γ |-[de] x : A] by now eapply ihx.
      assert [ |-[ de ] (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)] by now eapply idElimMotiveCtx.
      assert [Γ |-[de] P[tRefl A x .: x..]].
      1:{
          eapply typing_subst2; tea;[| now eapply ihP].
          cbn;rewrite 2!wk1_ren_on, 2!shift_one_eq; now econstructor.
      }
      assert [Γ |-[de] tId A x y] by now econstructor.
      split. 1:eauto 10.
      split ; [econstructor; tea; [eapply ihP| eapply ihhr| eapply ihy | eapply ihe]; eauto|..].
      now intros ? (?&[->]&?)%termGen'.
    - eintros * ? IH [HA ?]%dup ? ?.
      destruct IH as (?&?&?) ; tea.
      eapply subject_reduction_type, reddecl_conv in HA ; refold.
      2: boundary.
      split ; [eauto|..].
      split ; [econstructor ; tea|..].
      
      intros.
      etransitivity ; eauto.
      now symmetry.

    - intros * ? IHt HA ?.
      destruct IHt as (?&?&?) ; eauto.
      split ; [eauto|].
      econstructor ; tea.
      eapply Hconv in HA ; tea.
      now boundary.
  Qed.

  Definition BundledTypingInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoTypingInductionConcl PTy PInf PInfRed PCheck) in
      let t' := weak_statement t in exact t').

  Definition BundledTypingInduction_stmt :=
    ltac:(
      let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
      let ind := weak_statement t in
      exact ind).

End BundledTyping.

Corollary BundledTypingInduction `{!TypingSubst de} `{!TypeConstructorsInj de}
  PTy PInf PInfRed PCheck :
  BundledTypingInduction_stmt (ta := al) PTy PInf PInfRed PCheck.
Proof.
  red.
  intros.
  repeat match goal with |- prod _ _ => split end.
  all: intros * [].
  all: apply (algo_typing_discipline (ta := al) PTy PInf PInfRed PCheck) ;
    auto using algo_conv_sound_ty.
Qed.

Section TypingSoundness.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.
  Context `{ta : tag} `{conv : ConvType ta}.
  Hypothesis conv_sound :
    forall Γ A A', [Γ |-[de] A] -> [Γ |-[de] A'] -> [Γ |-[ta] A ≅ A'] -> [Γ |-[de] A ≅ A'].

  Let PTy (Γ : context) (A : term) :=
    [|-[de] Γ] -> [Γ |-[de] A].
  Let PInf (Γ : context) (A t : term) :=
    [|-[de] Γ] ->
    [Γ |-[de] t : A].
  Let PCheck (Γ : context) (A t : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] t : A].

  Theorem algo_typing_sound_generic : AlgoTypingInductionConcl PTy PInf PInf PCheck.
  Proof.
    subst PTy PInf PCheck.
    red.
    pose proof (algo_typing_discipline
      (fun _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)) as [H' H] 
      ;
    cycle -1.
    1: repeat (split ; [
      intros ; apply H' ; tea ; match goal with H : sigT _ |- _ => destruct H | _ => idtac end ; gen_typing 
      | ..] ; clear H' ; try destruct H as [H' H]).
    1: now intros ; apply H ; gen_typing.
    all: tea ; now constructor.
  Qed.

  Theorem algo_infer_unique Γ A T t :
    [|-[de] Γ] ->
    [Γ |-[de] t : T] ->
    ([Γ |-[ta] t ▹ A] -> [Γ |-[de] A ≅ T]) × ([Γ |-[ta] t ▹h A] -> [Γ |-[de] A ≅ T]).
  Proof.
    pose proof (algo_typing_discipline 
      (fun _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)) as [H' H] 
      ;
    cycle -1.
    1: shelve.
    all: easy.
    Unshelve.
    intros ; split ; intros Hal.
    all: eapply H in Hal ; eauto.
    all: now prod_hyp_splitter.
  Qed.

  Corollary algo_context_sound Γ : [|-[ta] Γ] -> [|-[de] Γ ].
  Proof.
    induction 1 as [| ???? HA] ; constructor ; tea.
    now eapply algo_typing_sound_generic in HA.
  Qed.

End TypingSoundness.

Definition algo_typing_sound `{!TypingSubst de} `{!TypeConstructorsInj de} :=
  algo_typing_sound_generic (ta := al) algo_conv_sound_ty.

Theorem bn_alg_typing_sound
  `{!TypingSubst de}
  `{!TypeConstructorsInj de} :

  BundledTypingInductionConcl
    (fun Γ A => [Γ |-[de] A])
    (fun Γ A t => [Γ |-[de] t : A])
    (fun Γ A t => [Γ |-[de] t : A])
    (fun Γ A t => [Γ |-[de] t : A]).
Proof.
  red.
  prod_splitter.
  all: intros * [].
  all: match goal with H : context [al] |- _ => eapply (algo_typing_sound_generic (ta := al)) in H end ;
    auto using algo_conv_sound_ty.
Qed.

Lemma bn_typing_sound 
  `{!TypingSubst de}
  `{!TypeConstructorsInj de}
  Γ t A :
  [Γ |-[bn] t : A] -> [Γ |-[de] t : A].
Proof.
  intros [???Hty?].
  econstructor ; tea.
  eapply algo_typing_sound_generic in Hty ; eauto using algo_conv_sound_ty.
Qed.

Corollary inf_conv_decl
  `{!TypingSubst de}
  `{!TypeConstructorsInj de}
  Γ t A A' :
  [Γ |-[al] t ▹ A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ |-[de] t : A'].
Proof.
  intros Ht Hconv.
  apply algo_typing_sound in Ht.
  all: gen_typing.
Qed.