(** * LogRel.Weakening: definition of well-formed weakenings, and some properties. *)
From Coq Require Import Lia ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms.

(** ** Raw weakenings *)

(** Weakenings are an intentional representation of a subclass of renamings 
(order-preserving ones), to allow easy proofs by induction. There is a unique
representation for extensionally equal renamings. *)

Inductive weakening : Set :=
  | _wk_empty : weakening
  | _wk_step (w : weakening) : weakening
  | _wk_up (w : weakening) : weakening.

Fixpoint _wk_id (Γ : context) : weakening :=
  match Γ with
    | nil => _wk_empty
    | cons _ Γ' => _wk_up (_wk_id Γ')
  end.

(** Transforms an (intentional) weakening into a renaming. *)
Fixpoint wk_to_ren (ρ : weakening) : nat -> nat :=
  match ρ with
    | _wk_empty => id
    | _wk_step ρ' => (wk_to_ren ρ') >> S
    | _wk_up ρ' => up_ren (wk_to_ren ρ')
  end.

Lemma wk_to_ren_id Γ : (wk_to_ren (_wk_id Γ)) =1 id.
Proof.
  induction Γ.
  1: reflexivity.
  intros [] ; cbn.
  2: rewrite IHΓ.
  all: reflexivity.
Qed.

Coercion wk_to_ren : weakening >-> Funclass.


(** ** Instance: how to rename by a well-formed weakening. *)

#[global] Instance Ren1_wk {Y Z : Type} `(ren : Ren1 (nat -> nat) Y Z) :
(Ren1 weakening Y Z) := fun ρ t => t⟨wk_to_ren ρ⟩.

Arguments Ren1_wk {_ _ _} _ _/.

Fixpoint wk_compose (ρ ρ' : weakening) : weakening :=
  match ρ, ρ' with
    | _wk_empty , _ => ρ'
    | _wk_step ν , _ => _wk_step (wk_compose ν ρ')
    | _wk_up ν, _wk_empty => ρ
    | _wk_up ν, _wk_step ν' => _wk_step (wk_compose ν ν')
    | _wk_up ν, _wk_up ν' => _wk_up (wk_compose ν ν')
  end.

Lemma wk_compose_compose (ρ ρ' : weakening) : wk_to_ren (wk_compose ρ ρ') =1 ρ' >> ρ.
Proof.
  induction ρ in ρ' |- *.
  - reflexivity.
  - cbn.
    rewrite IHρ.
    now fsimpl.
  - destruct ρ'.
    + reflexivity.
    + cbn.
      rewrite IHρ.
      now asimpl.
    + cbn.
      asimpl.
      rewrite IHρ.
      now asimpl.
Qed.

(** ** Well-formed weakenings between two contexts *)

(** To avoid dependency issues, we define well-formed weakenings as
a predicate on raw weakenings defined above, rather than directly
using indexed weakenings. *)

Inductive well_weakening : weakening -> context -> context -> Type :=
  | well_empty : well_weakening _wk_empty ε ε
  | well_step {Γ Δ : context} (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (_wk_step ρ) (Γ,, A) Δ
  | well_up {Γ Δ : context} (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (_wk_up ρ) (Γ,, A⟨ρ⟩) (Δ,, A).

Lemma well_wk_id (Γ : context) : well_weakening (_wk_id Γ) Γ Γ.
Proof.
  induction Γ as [|d].
  1: econstructor.
  replace d with (d⟨wk_to_ren (_wk_id Γ)⟩) at 2.
  1: now econstructor.
  cbn.
  f_equal.
  rewrite wk_to_ren_id.
  now asimpl.
Qed.

Lemma well_wk_compose {ρ ρ' : weakening} {Δ Δ' Δ'' : context} :
  well_weakening ρ Δ Δ' -> well_weakening ρ' Δ' Δ'' -> well_weakening (wk_compose ρ ρ') Δ Δ''.
Proof.
  intros H H'.
  induction H as [| | ? ? ? ν] in ρ', Δ'', H' |- *.
  all: cbn.
  - eassumption.
  - econstructor. auto.
  - inversion H' as [| | ? ? A' ν']; subst ; clear H'.
    1: now econstructor ; auto.
    asimpl ; refold.
    erewrite extRen_term ; refold.
    2: symmetry ; now apply wk_compose_compose.
    econstructor ; auto.
Qed.

#[projections(primitive)]Record wk_well_wk {Γ Δ : context} :=
  { wk :> weakening ; well_wk :> well_weakening wk Γ Δ}.
Arguments wk_well_wk : clear implicits.
Arguments Build_wk_well_wk : clear implicits.
Notation "Γ ≤ Δ" := (wk_well_wk Γ Δ).

#[global] Hint Resolve well_wk : core.

(** ** Instance: how to rename by a well-formed weakening. *)

#[global] Instance Ren1_well_wk {Y Z : Type} `{Ren1 (nat -> nat) Y Z} {Γ Δ : context} :
  (Ren1 (Γ ≤ Δ) Y Z) :=
  fun ρ t => t⟨wk_to_ren ρ.(wk)⟩.

Arguments Ren1_well_wk {_ _ _ _ _} _ _/.

Ltac fold_wk_ren :=
  change (@ren1 _ _ _ Ren_term (wk_to_ren (@wk _ _ ?ρ)))
    with (@ren1 _ _ _ (@Ren1_well_wk _ _ _ _ _) ρ);
  change (@ren1 _ _ _ (@Ren1_wk _ _ _) (@wk _ _ ?ρ))
    with (@ren1 _ _ _ (@Ren1_well_wk _ _ _ _ _) ρ).

Smpl Add 20 fold_wk_ren : refold.

Ltac change_well_wk :=
    change ren_term with (@ren1 _ _ _ Ren1_well_wk) in *.

Smpl Add 10 change_well_wk : refold.

(** Constructors of well-typed weakenings *)

Definition wk_empty : (ε ≤ ε) := {| wk := _wk_empty ; well_wk := well_empty |}.

Definition wk_step {Γ Δ} A (ρ : Γ ≤ Δ) : (Γ,,A) ≤ Δ :=
  {| wk := _wk_step ρ ; well_wk := well_step A ρ ρ |}.

Definition wk_up {Γ Δ} A (ρ : Γ ≤ Δ) : (Γ,,  A⟨ρ⟩) ≤ (Δ ,, A) :=
  {| wk := _wk_up ρ ; well_wk := well_up A ρ ρ |}.

Definition wk_id {Γ} : Γ ≤ Γ :=
  {| wk := _wk_id Γ ; well_wk := well_wk_id Γ |}.

Definition wk_well_wk_compose {Γ Γ' Γ'' : context} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') : Γ ≤ Γ'' :=
  {| wk := wk_compose ρ.(wk) ρ'.(wk) ; well_wk := well_wk_compose ρ.(well_wk) ρ'.(well_wk) |}.
Notation "ρ ∘w ρ'" := (wk_well_wk_compose ρ ρ').

(** ** The ubiquitous operation of adding one variable at the end of a context *)

Definition wk1 {Γ} A : Γ,, A ≤ Γ := wk_step A (wk_id (Γ := Γ)).

Lemma well_length {Γ Δ : context} (ρ : Γ ≤ Δ) : #|Δ| <= #|Γ|.
Proof.
  destruct ρ as [ρ wellρ].
  induction wellρ.
  all: cbn ; lia.
Qed.

Lemma id_ren (Γ : context) (ρ : Γ ≤ Γ) : ρ.(wk) = (_wk_id Γ).
Proof.
  destruct ρ as [ρ wellρ] ; cbn.
  pose proof (@eq_refl _ #|Γ|) as eΓ.
  revert eΓ wellρ.
  generalize Γ at 2 4.
  intros Δ e wellρ.
  induction wellρ in e |- *.
  all: cbn.
  - reflexivity.
  - pose proof (well_length {| wk := ρ ; well_wk := wellρ |}).
    now cbn in * ; lia.
  - rewrite IHwellρ.
    2: now cbn in * ; lia.
    reflexivity.
Qed.

Lemma wk1_ren {Γ A} : @wk1 Γ A =1 ↑.
Proof.
  intros ? ; cbv -[wk_to_ren _wk_id]. cbn.
  now rewrite wk_to_ren_id.
Qed.

Lemma wk_up_ren {Γ Δ A} (ρ : Δ ≤ Γ) : 
  wk_up A ρ =1 upRen_term_term ρ.
Proof.
  intros; cbn; now asimpl.
Qed.

Section RenWlWhnf.

  Context {Γ Δ} (ρ : Δ ≤ Γ).

  Lemma whne_ren_wl t : whne t -> whne (t⟨ρ⟩).
  Proof.
    apply whne_ren.
  Qed.

  Lemma whnf_ren_wl t : whnf t -> whnf (t⟨ρ⟩).
  Proof.
    apply whnf_ren.
  Qed.
  
  Lemma isType_ren_wl A : isType A -> isType (A⟨ρ⟩).
  Proof.
    apply isType_ren.
  Qed.
  
  Lemma isPosType_ren_wl A : isPosType A -> isPosType (A⟨ρ⟩).
  Proof.
    apply isPosType_ren.
  Qed.
  
  Lemma isFun_ren_wl f : isFun f -> isFun (f⟨ρ⟩).
  Proof.
    apply isFun_ren.
  Qed.

  Lemma isPair_ren_wl f : isPair f -> isPair (f⟨ρ⟩).
  Proof.
    apply isPair_ren. 
  Qed.

  Lemma isCanonical_ren_wl t : isCanonical t <~> isCanonical (t⟨ρ⟩).
  Proof.
    symmetry.
    apply isCanonical_ren.
  Qed.

End RenWlWhnf.

#[global] Hint Resolve whne_ren_wl whnf_ren_wl isType_ren_wl isPosType_ren_wl isFun_ren_wl isCanonical_ren_wl : gen_typing.

(** ** Adaptation of AutoSubst's asimpl to well typed weakenings *)

Ltac bsimpl' :=
  repeat (first
    [ progress setoid_rewrite substSubst_term_pointwise
    | progress setoid_rewrite substSubst_term
    | progress setoid_rewrite substRen_term_pointwise
    | progress setoid_rewrite substRen_term
    | progress setoid_rewrite renSubst_term_pointwise
    | progress setoid_rewrite renSubst_term
    | progress setoid_rewrite renRen'_term_pointwise
    | progress setoid_rewrite renRen_term
    | progress setoid_rewrite varLRen'_term_pointwise
    | progress setoid_rewrite varLRen'_term
    | progress setoid_rewrite varL'_term_pointwise
    | progress setoid_rewrite varL'_term
    | progress setoid_rewrite rinstId'_term_pointwise
    | progress setoid_rewrite rinstId'_term
    | progress setoid_rewrite instId'_term_pointwise
    | progress setoid_rewrite instId'_term
    | progress setoid_rewrite wk_to_ren_id
    | progress setoid_rewrite wk_compose_compose
    | progress setoid_rewrite id_ren
    | progress setoid_rewrite wk1_ren
    | progress unfold
        up_term_term, upRen_term_term, up_ren, wk_well_wk_compose,
        wk_id, wk_step, wk_up, wk_empty (**, _wk_up, _wk_step *)
    | progress cbn[subst_term ren_term wk wk_to_ren]
    | progress fsimpl ]).

Ltac bsimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1,
                  Ren1_subst, Ren1_wk, Ren1_well_wk
                  in *; bsimpl'; minimize.


(** ** Weakenings play well with context access *)

Lemma in_ctx_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
in_ctx Γ n decl ->
in_ctx Δ (ρ n) (decl⟨ρ⟩).
Proof.
intros Hdecl.
destruct ρ as [ρ wfρ] ; cbn in *.
induction wfρ in n, decl, Hdecl |- *.
- inversion Hdecl.
- cbn.
  replace (decl⟨_⟩) with (decl⟨ρ⟩⟨↑⟩) by now asimpl.
  now econstructor.
- destruct n ; cbn.
  + inversion Hdecl ; subst ; clear Hdecl.
    replace (A⟨↑⟩⟨_⟩) with (A⟨ρ⟩⟨↑⟩) by now asimpl.
    now constructor.
  + inversion Hdecl ; subst ; cbn in * ; refold.
    replace (d⟨_⟩⟨_⟩) with (d⟨ρ⟩⟨↑⟩) by now asimpl.
    now econstructor.
Qed.

Lemma in_ctx_str (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
in_ctx Δ (ρ n) decl ->
∑ decl', decl = decl'⟨ρ⟩ × in_ctx Γ n decl'.
Proof.
intros Hdecl.
destruct ρ as [ρ wfρ] ; cbn in *.
induction wfρ in n, decl, Hdecl |- *.
- inversion Hdecl.
- cbn in *.
inversion Hdecl ; subst.
edestruct IHwfρ as [? []]; tea ; subst.
eexists ; split ; tea.
now bsimpl.
- destruct n ; cbn in *.
+ inversion Hdecl ; subst ; clear Hdecl.
  eexists ; split.
  2: now constructor.
  now bsimpl.
+ inversion Hdecl ; subst ; clear Hdecl ; cbn in *.
  edestruct IHwfρ as [? []]; tea ; subst.
  eexists ; split.
  2: now econstructor.
  now bsimpl.
Qed.

(** Lemmas for easier rewriting *)

Lemma subst_ren_wk_up {Γ Δ P A n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P⟨wk_up A ρ⟩[n⟨ρ⟩..].
Proof. now bsimpl. Qed.

Lemma subst_ren_wk_up2 {Γ Δ P A B a b} (ρ : Γ ≤ Δ): 
  P[a .: b..]⟨ρ⟩ = P⟨wk_up A (wk_up B ρ)⟩[a⟨ρ⟩ .: b⟨ρ⟩..].
Proof. now bsimpl. Qed.

Lemma subst_ren_subst_mixed {Γ Δ P n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P[n⟨ρ⟩ .: ρ >> tRel].
Proof. now bsimpl. Qed.

Lemma subst_ren_subst_mixed2 {Γ Δ P a b} (ρ : Γ ≤ Δ): P[a .: b..]⟨ρ⟩ = P[a⟨ρ⟩ .: (b⟨ρ⟩ .: ρ >> tRel)].
Proof. now bsimpl. Qed.


Lemma wk_up_ren_subst {Γ Δ Ξ P A n}  (ρ : Γ ≤ Δ) (ρ' : Δ ≤ Ξ) : 
  P[n .: ρ ∘w ρ' >> tRel] = P⟨wk_up A ρ'⟩[n .: ρ >> tRel].
Proof. now bsimpl. Qed.

Lemma shift_subst_scons {B a Γ Δ} (ρ : Δ ≤ Γ) : B⟨↑⟩[a .: ρ >> tRel] = B⟨ρ⟩.
Proof. bsimpl; now rewrite rinstInst'_term. Qed.

Lemma shift_upRen ρ t : t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨upRen_term_term ρ⟩.
Proof. now asimpl. Qed.

Lemma wk_comp_ren_on {Γ Δ Ξ} (H : term) (ρ1 : Γ ≤ Δ) (ρ2 : Δ ≤ Ξ) :
  H⟨ρ2⟩⟨ρ1⟩ = H⟨ρ1 ∘w ρ2⟩.
Proof. now bsimpl. Qed.

Lemma wk_id_ren_on Γ (H : term) : H⟨@wk_id Γ⟩ = H.
Proof. now bsimpl. Qed.

Lemma wk1_ren_on Γ F (H : term) : H⟨@wk1 Γ F⟩ = H⟨↑⟩.
Proof. now bsimpl. Qed.
  
Lemma wk_up_ren_on Γ Δ (ρ : Γ ≤ Δ) F (H : term) : H⟨wk_up F ρ⟩ = H⟨upRen_term_term ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_up_wk1_ren_on Γ F G (H : term) : H⟨wk_up F (@wk1 Γ G)⟩ = H⟨upRen_term_term ↑⟩.
Proof. now bsimpl. Qed.

Lemma wk_arr {A B Γ Δ} (ρ : Δ ≤ Γ) : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_elimSuccHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimSuccHypTy P⟨wk_up A ρ⟩ = (elimSuccHypTy P)⟨ρ⟩.
Proof.
  unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
Qed.

Lemma wk_prod {A B Γ Δ} (ρ : Δ ≤ Γ) : tProd A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tProd A B)⟨ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_sig {A B Γ Δ} (ρ : Δ ≤ Γ) : tSig A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tSig A B)⟨ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_pair {A B a b Γ Δ} (ρ : Δ ≤ Γ) : tPair A⟨ρ⟩ B⟨wk_up A ρ⟩ a⟨ρ⟩ b⟨ρ⟩ = (tPair A B a b)⟨ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_fst {p Γ Δ} (ρ : Δ ≤ Γ) : tFst p⟨ρ⟩ = (tFst p)⟨ρ⟩.
Proof. now cbn. Qed.

Lemma wk_snd {p Γ Δ} (ρ : Δ ≤ Γ) : tSnd p⟨ρ⟩ = (tSnd p)⟨ρ⟩.
Proof. now cbn. Qed.

Lemma wk_comp {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp A f g)⟨ρ⟩ = comp A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_Id {A x y Γ Δ} (ρ : Δ ≤ Γ) : tId A⟨ρ⟩ x⟨ρ⟩ y⟨ρ⟩ = (tId A x y)⟨ρ⟩.
Proof. now cbn. Qed.

Lemma wk_refl {A x Γ Δ} (ρ : Δ ≤ Γ) : tRefl A⟨ρ⟩ x⟨ρ⟩ = (tRefl A x)⟨ρ⟩.
Proof. now cbn. Qed.


Lemma wk_step_wk1 {A t Γ Δ} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟩ = t⟨wk_step A ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_up_wk1 {A t Γ Δ} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟨ρ⟩⟩ = t⟨@wk1 Γ A⟩⟨wk_up A ρ⟩.
Proof. now bsimpl. Qed.


Lemma wk_idElim {A x P hr y e Δ Γ} (ρ : Δ ≤ Γ) :
  tIdElim A⟨ρ⟩ x⟨ρ⟩ P⟨wk_up (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) (wk_up A ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩ e⟨ρ⟩ = (tIdElim A x P hr y e)⟨ρ⟩.
Proof.  now cbn. Qed.

Lemma wk_comp_lunit {Γ Δ} (ρ : Δ ≤ Γ) : wk_id ∘w ρ =1 ρ.
Proof. now bsimpl. Qed.

Lemma wk_comp_runit {Γ Δ} (ρ : Δ ≤ Γ) : ρ ∘w wk_id =1 ρ.
Proof. now bsimpl. Qed.

Lemma wk_comp_assoc {Γ Δ Ξ ζ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Δ) (ρ'' : ζ ≤ Ξ) :
  (ρ'' ∘w ρ') ∘w ρ =1 ρ'' ∘w (ρ' ∘w ρ).
Proof. now bsimpl. Qed.


Lemma wk1_irr {Γ Γ' A A' t} : t⟨@wk1 Γ A⟩ = t⟨@wk1 Γ' A'⟩.
Proof. intros; now rewrite 2!wk1_ren_on. Qed.