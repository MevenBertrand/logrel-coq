(** * LogRel.BundledAlgorithmicTyping: algorithmic typing bundled with its pre-conditions, and a tailored induction principle. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping DeclarativeSubst TypeConstructorsInj.

Import DeclarativeTypingProperties AlgorithmicTypingData.

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
  bun_conv_ne_wh_l : whne m ;
  bun_conv_ne_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_wh_r : whne n ;
  bun_conv_ne : [Γ |-[al] m ~ n ▹ A]
}.

Record ConvNeuRedBun Γ A m n :=
{
  bun_conv_ne_red_ctx : [|-[de] Γ] ;
  bun_conv_ne_red_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_red_wh_l : whne m ;
  bun_conv_ne_red_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_red_wh_r : whne n ;
  bun_conv_ne_red : [Γ |-[al] m ~h n ▹ A]
}.

Record ConvNeuConvBun Γ A m n :=
{
  bun_conv_ne_conv_ctx : [|-[de] Γ] ;
  bun_conv_ne_conv_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_conv_wh_l : whne m ;
  bun_conv_ne_conv_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_conv_wh_r : whne n ;
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
    change ConvNeuConvBun with (conv_neu_conv (ta := bn)) in *;
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
    change (conv_neu_conv (ta := bni)) with (conv_neu_conv (ta := bn)) in *.

End BundledIntermediateData.

Set Universe Polymorphism.

(** ** Induction principle for bundled algorithmic conversion *)

(** We show an induction principle tailored for the bundled predicates: it threads the invariants
of the algorithm through the derivation, giving us stronger hypothesis in the minor premises,
corresponding to both the pre-conditions being true, and the post-conditions of the induction
hypotheses holding. *)

Section BundledConv.
  Universe u.

  Context (PTyEq PTyRedEq : context -> term -> term -> Type@{u})
  (PNeEq PNeRedEq PTmEq PTmRedEq : context -> term -> term -> term -> Type@{u}).

  (** Rather than writing by hand the various large statements of the induction principles,
  we use Ltac to derive them generically. Hopefully, there is no need to touch any part of
  this code when extending modifying the language with more features. *)
  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTyEq ?Γ ?A ?B] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> [Γ |-[de] B] -> Hyp)
    | context [PTyRedEq ?Γ ?A ?B] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> [Γ |-[de] B] -> Hyp)
    | context [PNeEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> (well_typed (ta := de) Γ t) -> (well_typed (ta := de) Γ u) -> Hyp)
    | context [PNeRedEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> (well_typed (ta := de) Γ t) -> (well_typed (ta := de) Γ u) -> Hyp)
    | context [PTmEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> ([Γ |-[de] t : A]) -> ([Γ |-[de] u : A]) -> Hyp)
    | context [PTmRedEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> ([Γ |-[de] t : A]) -> ([Γ |-[de] u : A]) -> Hyp)
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

  (* Eval cbn beta in ltac:(let T := strong_step (forall (Γ : context) (na' : aname) (A B A' B' : term),
    [Γ |-[ al ] A ≅ A'] ->
    PTyEq Γ A A' ->
    [Γ,, A |-[ al ] B ≅ B'] ->
    PTyEq (Γ,, A) B B' -> PTyRedEq Γ (tProd A B) (tProd na' A' B')) in exact T).
  *)

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
    - intros * HA HB ? IHA' ? ? ?.
      pose proof (HA' := HA).
      pose proof (HB' := HB).
      eapply subject_reduction_type, RedConvTyC in HA', HB' ; tea.
      destruct IHA'.
      1-3: boundary.
      split ; [now eauto|..].
      symmetry in HB'.
      do 2 etransitivity ; tea.
      now econstructor.
    - intros * ? IHA ? IHB ? HP HP'.
      eapply prod_ty_inv in HP as [], HP' as [? HB'].
      assert [Γ,, A |-[de] B'].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        now eapply IHA.
      }
      split ; [gen_typing|..].
      destruct IHB as [].
      1-3: gen_typing.
      now econstructor.
    - intros.
      split ; [now eauto|..].
      now gen_typing.
    - intros * ?? _.
      split ; [gen_typing|..].
      now econstructor.
    - intros * ?? _.
      split ; [gen_typing|..].
      now econstructor. 
    - intros * ? IHA ? IHB ? HP HP'.
      eapply sig_ty_inv in HP as [], HP' as [? HB'].
      assert [Γ,, A |-[de] B'].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        now eapply IHA.
      }
      split ; [gen_typing|..].
      destruct IHB as [].
      1-3: gen_typing.
      now econstructor.
    - intros * Hconv IHA ? IHx ? IHy ? HM HN.
      pose proof HM as [? []]%id_ty_inv.
      pose proof HN as [? []]%id_ty_inv.
      assert [Γ |-[de] x' : A] by (eapply wfTermConv; tea; refold; now symmetry). 
      assert [Γ |-[de] y' : A] by (eapply wfTermConv; tea; refold; now symmetry). 
      split; [eauto|].
      econstructor; [eapply IHA| eapply IHx | eapply IHy]; eauto.
    - intros * Hconv IH ? HM HN.
      assert [Γ |-[de] M : U].
      {
        eapply algo_conv_wh in Hconv as [neM neN].
        now eapply neutral_ty_inv.
      }
      assert [Γ |-[de] N : U].
      {
        eapply algo_conv_wh in Hconv as [neM neN].
        now eapply neutral_ty_inv.
      }
      assert (well_typed (ta := de) Γ M) by now eexists.
      assert (well_typed (ta := de) Γ N) by now eexists.
      split ; [now eauto|..].
      do 2 econstructor.
      all: now apply IH.
    - intros * Hin ? ? _.
      split ; [now eauto|..].
      split.
      + do 2 constructor ; gen_typing.
      + intros T Hty.
        eapply termGen' in Hty as [? [[? [->]] ?]].
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
      + intros T Hty.
        eapply termGen' in Hty as [? [[? [->]] ?]].
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
    - intros * ? IHm ? IHt ? Htym Htyn.
      pose proof Htym as [? Htym'].
      pose proof Htyn as [? Htyn'].
      eapply termGen' in Htym' as [? [[? [? [-> Htym']]] ?]].
      eapply termGen' in Htyn' as [? [[? [? [-> Htyn']]] ?]].
      edestruct IHm as [? [IHmc IHm' IHn']].
      1: easy.
      1-2: now econstructor.
      unshelve eapply IHm', prod_ty_inj in Htym' as [].
      unshelve eapply IHn', prod_ty_inj in Htyn' as [].
      edestruct IHt.
      1: easy.
      1-2: now gen_typing.
      split ; [now eauto|..].
      split.
      + econstructor ; gen_typing.
      + intros ? Happ.
        eapply termGen' in Happ as [? [(?&?&[-> Htym']) ?]].
        eapply IHm', prod_ty_inj in Htym' as [].
        etransitivity ; [..|eassumption].
        eapply typing_subst1 ; tea.
        now econstructor.
      + intros ? Happ.
        eapply termGen' in Happ as [? [(?&?&[-> Htyn']) ?]].
        eapply IHn', prod_ty_inj in Htyn' as [HA ?].
        etransitivity ; [..|eassumption].
        eapply typing_subst1.
        2: eassumption.
        symmetry in HA.
        now gen_typing.
    - intros * ? IHn ? IHP ? IHz ? IHs ? Hty Hty'.
      pose proof Hty as [? Hty2].
      pose proof Hty' as [? Hty2'].
      eapply termGen' in Hty2 as [? [[->]]].
      eapply termGen' in Hty2' as [? [[->]]].
      edestruct IHn as [? [IHnc IHnty IHnty']].
      1: easy.
      1-2: now eexists.
      assert [|-[de] Γ,, tNat] by boundary.
      assert [Γ,, tNat |-[de] P ≅ P']
        by now edestruct IHP.
      assert [Γ |-[de] hz' : P[tZero..]].
      {
       econstructor ; tea.
       symmetry.
       eapply typing_subst1 ; tea.
       now do 2 econstructor. 
      }
      assert [Γ |-[de] hs' : elimSuccHypTy P].
      {
       econstructor ; tea.
       symmetry.
       now eapply elimSuccHypTy_conv.
      }
      split ; [eauto 10 |..].
      split.
      + now econstructor.
      + now intros ?[? [[->]]]%termGen'.
      + intros ?[? [[->]]]%termGen'.
        etransitivity.
        1: eapply typing_subst1.
        all: eassumption.
    - intros * ? IHe ? IHP ? Hty Hty'.
      pose proof Hty as [? Hty2].
      pose proof Hty' as [? Hty2'].
      eapply termGen' in Hty2 as [? [[->]]].
      eapply termGen' in Hty2' as [? [[->]]].
      edestruct IHe as [? [IHec IHnty IHnty']].
      1: easy.
      1-2: now eexists.
      assert [|-[de] Γ,, tEmpty] by boundary.
      assert [Γ,, tEmpty |-[de] P ≅ P']
        by now edestruct IHP.
      split ; [eauto |..].
      split.
      + now econstructor.
      + now intros ?[? [[->]]]%termGen'.
      + intros ?[? [[->]]]%termGen'.
        etransitivity.
        1: eapply typing_subst1.
        all: eassumption.
    - intros * ? ih ? hm hn.
      pose proof hm as [? [?[[?[?[->]]]]]%termGen'].
      pose proof hn as [? [?[[?[?[->]]]]]%termGen'].
      edestruct ih as [? [? ihm ihn]]; tea.
      1,2: now eexists.
      split; [eauto| split].
      + now econstructor.
      + intros ? [?[[?[?[-> []%ihm%sig_ty_inj]]]]]%termGen'.
        now etransitivity.
      + intros ? [?[[?[?[-> []%ihn%sig_ty_inj]]]]]%termGen'.
        now etransitivity.
    - intros * ? ih ? hm hn.
      pose proof hm as [? [?[[?[?[-> hm']]]]]%termGen'].
      pose proof hn as [? [?[[?[?[->]]]]]%termGen'].
      edestruct ih as [? [? ihm ihn]]; tea.
      1,2: now eexists.
      split; [eauto| split].
      + now econstructor.
      + intros ? [?[[?[?[-> h%ihm]]]]]%termGen'.
        pose proof h as []%sig_ty_inj.
        etransitivity; tea.
        eapply typing_subst1; tea ; do 2 econstructor.
        boundary.
      + intros ? [?[[?[?[-> h%ihn]]]]]%termGen'.
        pose proof h as []%sig_ty_inj.
        etransitivity; tea.
        eapply typing_subst1; tea.
        now  econstructor.
    - intros * ? ihe (*? ihA'' ? ihx'' ? ihy''*) (* ? ihA ? ihx ? ihy *) ? ihP ? ihhr ? hm hn.
      pose proof hm as [? [? [[-> ????? he]]]%termGen'].
      pose proof hn as [? [? [[-> ????? he']]]%termGen'].
      edestruct ihe as [? [? ihm ihn]]; tea.
      1,2: now eexists.
      epose proof (idElimConv hm hn) as (?&?&?&[]) ; tea.
      1: eapply TypeRefl ; refold ; boundary.
      1: constructor.
      assert [ |-[ de ] (Γ,, A),, tId A⟨wk1 A⟩ x⟨wk1 A⟩ (tRel 0)] by boundary.
      assert [(Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |-[ de ] P'].
      {
        eapply stability; tea; symmetry; eapply idElimMotiveCtxConv;
        tea; now boundary + eapply ctx_refl.
      }
      assert [(Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |-[ de ] P ≅ P'] by now eapply ihP.
      assert [Γ |-[ de ] hr' : P[tRefl A x .: x..]].
      {
        econstructor; tea; refold; symmetry.
        eapply typing_subst2; tea.
        cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq; now econstructor.
      }
      split ; [now eauto 20|..].
      split.
      + econstructor; tea.
        * now eapply ihhr.
        * econstructor ; tea.
          symmetry.
          now econstructor. 
      + now intros ? [? [[->]]]%termGen'.
      + intros ? [? [[->]]]%termGen'.
        etransitivity ; [..|eassumption].
        eapply typing_subst2; tea.
        cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq.
        econstructor ; tea.
        symmetry.
        now econstructor.
    - intros * ? IHm HA ? ? Htym Htyn.
      pose proof Htym as [? Htym'].
      pose proof Htyn as [? Htyn'].
      edestruct IHm as [_ [IHmc IHm' IHn']].
      1: easy.
      1-2: now eexists.
      pose proof (HA' := HA).
      eapply subject_reduction_type, RedConvTyC in HA'.
      2: boundary.
      split ; [now eauto|..].
      split.
      + gen_typing.
      + intros.
        symmetry in HA'.
        etransitivity ; gen_typing.
      + intros.
        symmetry in HA'.
        etransitivity ; gen_typing.
    - intros * HA Ht Hu ? IH ? Htyt Htyu.
      pose proof (HA' := HA).
      pose proof (Ht' := Ht).
      pose proof (Hu' := Hu).
      eapply subject_reduction_type, RedConvTyC in HA'.
      2: boundary.
      eapply subject_reduction, RedConvTeC in Ht' ; tea.
      eapply subject_reduction, RedConvTeC in Hu' ; tea.
      pose proof (Ht'' := Ht').
      pose proof (Hu'' := Hu').
      eapply boundary in Ht'' as [], Hu'' as [].
      split ; [now gen_typing|..].
      etransitivity ; [..|etransitivity].
      1: eassumption.
      2: now symmetry.
      econstructor.
      2: now symmetry.
      eapply IH.
      all: gen_typing.
    - intros * ? IHA ? IHB ? Hty Hty'.
      pose proof (Htyd := Hty).
      pose proof (Htyd' := Hty').
      eapply termGen' in Htyd as [? [[->] _]].
      eapply termGen' in Htyd' as [? [[->] _]].
      assert [Γ,, A |-[de] B' : U].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        now econstructor.
      }
      split ; [now gen_typing|..].
      econstructor.
      + assumption.
      + now eapply IHA.
      + now eapply IHB ; gen_typing.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHt ? Htyt Htyt'.
      pose proof (Htyd := Htyt).
      pose proof (Htyd' := Htyt').
      eapply termGen' in Htyd as [? [[->] _]].
      eapply termGen' in Htyd' as [? [[->] _]].
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; eauto.
      now econstructor. 
    - intros * ? ? ? IH ? Hf Hg.
      assert [Γ |-[de] A] by
        (now eapply boundary, prod_ty_inv in Hf).
      pose proof (Hf' := Hf).
      pose proof (Hg' := Hg).
      eapply typing_eta' in Hf'.
      eapply typing_eta' in Hg'.
      split ; [now gen_typing|..].
      etransitivity; [|now eapply TermFunEta].
      etransitivity; [symmetry; now eapply TermFunEta|].
      econstructor ; tea; try now constructor.
      now eapply IH ; gen_typing.
    - intros * ? ihA ? ihB ? hty hty'.
      pose proof hty as [?[[->]]]%termGen'.
      pose proof hty' as [?[[->]]]%termGen'.
      edestruct ihA as []; tea.
      edestruct ihB as []; tea.
      1: gen_typing.
      1: eapply stability1; tea; gen_typing.
      split ; [eauto|now econstructor].
    - intros * ??? ihfst ? ihsnd ? hp hq.
      edestruct ihfst as []; tea.
      1,2: now econstructor.
      pose proof hp as []%boundary%sig_ty_inv.
      edestruct ihsnd as []; tea.
      1: now econstructor.
      2:{ split; [eauto|].
          eapply TermTrans; [|now constructor].
          eapply TermTrans; [eapply TermSym; now constructor|].
          constructor; tea; now apply TypeRefl. }
      eapply wfTermConv; [now econstructor|].
      eapply typing_subst1; [now symmetry|].
      now eapply TypeRefl.
    - intros * ? ihA ? ihx ? ihy ? hm hn.
      pose proof hm as [?[[->]]]%termGen'.
      pose proof hn as [?[[->]]]%termGen'.
      assert [Γ |-[de] A ≅ A'] by (econstructor; now eapply ihA).
      assert [Γ |-[de] x' : A] by (eapply wfTermConv; tea; refold; now symmetry). 
      assert [Γ |-[de] y' : A] by (eapply wfTermConv; tea; refold; now symmetry). 
      split; [eauto|].
      econstructor; [eapply ihA|eapply ihx| eapply ihy]; tea.
    - intros * ? hm hn.
      pose proof hm as [?[[-> ??] []%id_ty_inj]]%termGen'.
      pose proof hn as [?[[-> ??] []%id_ty_inj]]%termGen'.
      split ; [eauto|].
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
    - intros * ? IHm ? ? Htym Htyn.
      edestruct IHm as [? [? Hm']].
      1: easy.
      1-2: now eexists.
      split ; [now eauto|..].
      econstructor ; tea.
      now eapply Hm'.
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
    all: apply algo_conv_discipline ; assumption.
  Qed.

End BundledConv.

(** ** Soundness of algorithmic conversion *)

(** Contrarily to the induction principle above, if we instantiate the main principle with
only constant true predicates, we get only the post-conditions, ie a soundness theorem: bundled algorithmic conversion judgments imply their declarative counterparts. *)

Section ConvSoundness.

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
      repeat (split ; [
      intros ; apply H' ; tea ; match goal with H : well_typed _ _ |- _ => destruct H | _ => idtac end ; gen_typing 
      | ..] ; clear H' ; try destruct H as [H' H]).
      intros ; apply H ; gen_typing. }
    all: now constructor.
  Qed.

End ConvSoundness.

Theorem bn_conv_sound :
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
        context C [PInf Γ A t × [Γ |-[de] t : A]]
    | context C [PInfRed ?Γ ?A ?t] =>
        context C [PInfRed Γ A t × [Γ |-[de] t : A]]
    | context C [PCheck ?Γ ?A ?t] =>
        context C [PCheck Γ A t × [Γ |-[de] t : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A] => constr:([Γ |-[bn] A])
      | [?Γ |-[al] ?t ▹ ?A] => constr:([Γ |-[bn] t ▹ A])
      | [?Γ |-[al] ?t ▹h ?A] => constr:([Γ |-[bn] t ▹h A])
      | [?Γ |-[al] ?t ◃ ?A] => constr:([Γ |-[bn] t ◃ A])
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

  Let PTy' (c : context) (t : term) :=
        [ |-[ de ] c] -> PTy c t × [c |-[ de ] t].
  Let PInf' (c : context) (t t1 : term) :=
     [ |-[ de ] c] -> PInf c t t1 × [c |-[ de ] t1 : t].
  Let PInfRed' (c : context) (t t1 : term) :=
       [ |-[ de ] c] -> PInfRed c t t1 × [c |-[ de ] t1 : t].
  Let PCheck' (c : context) (t t1 : term) :=
         [ |-[ de ] c] ->
         [c |-[ de ] t] -> PCheck c t t1 × [c |-[ de ] t1 : t].

  (** The main theorem *)
  Theorem algo_typing_discipline : ltac:(
    let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
    let ind := strong_statement t in
    exact ind).
  Proof.
    intros.
    subst PTy' PInf' PInfRed' PCheck'.
    apply AlgoTypingInduction.
    1-10: solve [intros ;
      repeat unshelve (
        match reverse goal with
          | IH : context [prod] |- _ => destruct IH ; [..|shelve] ; gen_typing
        end) ;
      now split ; [|econstructor] ; eauto].
    - intros * ? IHI ? IHC ?.
      destruct IHI as [? IHt].
      1: gen_typing.
      destruct IHC ; tea.
      1: now eapply boundary, prod_ty_inv in IHt as [].
      split ; [|econstructor] ; eauto.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
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
      econstructor.
      + now eapply IHP.
      + now eapply IHz.
      + now eapply IHs.
      + now eapply IHn.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHe ? IHP ?.
      assert [|-[de] Γ,, tEmpty]
        by (econstructor ; tea ; now econstructor).
      split ; [eauto|..].
      econstructor.
      + now eapply IHP.
      + now eapply IHe.
    - intros * ? ihA ? ihB ?.
      edestruct ihA as []; tea.
      edestruct ihB as [].
      1: gen_typing.
      split; [eauto|now econstructor].
    - intros * ? ihA ? ihB ? iha ? ihb ?.
      edestruct ihA as []; tea.
      edestruct ihB as [].
      1: gen_typing.
      edestruct iha as []; tea.
      edestruct ihb as []; tea.
      1: now eapply typing_subst1.
      split;[eauto|now econstructor].
      (* why is that not found by eauto ? *)
      eapply X17; tea; now split.
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ihA ? ihx ? ihy ?.
      edestruct ihA as []; tea.
      assert [Γ |-[de] A] by now econstructor.
      split; [eauto|].
      econstructor; tea; [now eapply ihx | now eapply ihy].
    - intros * ? ihA ? ihx ?.
      assert [Γ |-[de] A] by now eapply ihA.
      split; [eauto|]. 
      econstructor; tea; now eapply ihx.
    - intros * ? ihA ? ihx ? ihP ? ihhr ? ihy ? ihe ?.
      assert [Γ |-[de] A] by now eapply ihA.
      assert [Γ |-[de] x : A] by now eapply ihx.
      assert [ |-[ de ] (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)] by now eapply idElimMotiveCtx.
      assert [Γ |-[de] P[tRefl A x .: x..]].
      1:{
          eapply typing_subst2; tea;[| now eapply ihP].
          cbn;rewrite 2!wk1_ren_on, 2!shift_subst_eq; now econstructor.
      }
      assert [Γ |-[de] tId A x y] by now econstructor.
      split. 1:eapply X22; eauto. (* ??? *)
      econstructor; tea; [eapply ihP| eapply ihhr| eapply ihy | eapply ihe]; eauto.
    - intros * ? IH HA ?.
      destruct IH as [? IH] ; tea.
      split ; [eauto|..].
      econstructor ; tea.
      eapply subject_reduction_type, RedConvTyC in HA.
      1: eassumption.
      now boundary.
    - intros * ? IHt HA ?.
      destruct IHt as [? IHt] ; eauto.
      split ; [eauto|].
      econstructor ; tea.
      eapply algo_conv_sound in HA ; tea.
      now boundary.
  Qed.

  Definition BundledTypingInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoTypingInductionConcl PTy PInf PInfRed PCheck) in
      let t' := weak_statement t in exact t').

  Corollary BundledTypingInduction :
    ltac:(
      let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat match goal with |- prod _ _ => split end.
    all: intros * [].
    all: apply algo_typing_discipline ; assumption.
  Qed.

End BundledTyping.

Section TypingSoundness.

  Let PTy (Γ : context) (A : term) :=
    [|-[de] Γ] -> [Γ |-[de] A].
  Let PInf (Γ : context) (A t : term) :=
    [|-[de] Γ] ->
    [Γ |-[de] t : A].
  Let PCheck (Γ : context) (A t : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] t : A].

  Theorem algo_typing_sound : AlgoTypingInductionConcl PTy PInf PInf PCheck.
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
    all: now constructor.
  Qed.

End TypingSoundness.

Theorem bn_alg_typing_sound :
BundledTypingInductionConcl
  (fun Γ A => [Γ |-[de] A])
  (fun Γ A t => [Γ |-[de] t : A])
  (fun Γ A t => [Γ |-[de] t : A])
  (fun Γ A t => [Γ |-[de] t : A]).
Proof.
  red.
  prod_splitter.
  all: intros * [].
  all: match goal with H : context [al] |- _ => eapply algo_typing_sound in H end.
  all: prod_hyp_splitter.
  all: now eassumption.
Qed.

Lemma bn_typing_sound Γ t A :
  [Γ |-[bn] t : A] -> [Γ |-[de] t : A].
Proof.
  intros [???Hty?].
  econstructor ; tea.
  now eapply algo_typing_sound in Hty.
Qed.

Corollary inf_conv_decl Γ t A A' :
[Γ |-[al] t ▹ A] ->
[Γ |-[de] A ≅ A'] ->
[Γ |-[de] t : A'].
Proof.
  intros Ht Hconv.
  apply algo_typing_sound in Ht.
  2: boundary.
  now econstructor.
Qed.