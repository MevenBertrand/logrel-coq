From Ltac2 Require Import Ltac2 Printf.
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation PERTactics.
From LogRel.Validity Require Import Validity Irrelevance Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Definition packed_valid_ty `{GenericTypingProperties} l :=
  packed_ciper (VAdequate VR) (fun Γ Γ' VΓ => typeValidity Γ Γ' VΓ l).

Instance packed_valid_tyPER `{GenericTypingProperties} l : PER (packed_valid_ty l) :=
  packed_ciper_per.

Definition mkVty `{GenericTypingProperties} {l Γ Γ' A A'} {VΓ : [||-v Γ ≅ Γ']} (VA : [_ ||-v<l> A ≅ A' | VΓ]) :
  packed_valid_ty l (& Γ, A)  (& Γ', A') := (& VΓ ; VA ).


Definition packed_valid_tm `{GenericTypingProperties} l :=
  packed_ciper (packed_valid_ty l) (fun _ _ VΓA t u => [_ ||-v<l> t ≅ u : _ | dfst VΓA | dsnd VΓA]).

Instance iperValidTm `{GenericTypingProperties} l :
  IPER (packed_valid_ty l) (fun _ => term) (fun _ _ VΓA t u => [_ ||-v<l> t ≅ u : _ | dfst VΓA | dsnd VΓA]).
Proof.
  constructor.
  - intros; now eapply symValidTm.
  - intros; now eapply transValidTm.
Defined.

Instance packed_valid_tmPER `{GenericTypingProperties} l : PER (packed_valid_tm l) :=
  packed_ciper_per.

Definition mkVtm `{GenericTypingProperties} {l Γ Γ' A A' t t'} {VΓ : [||-v Γ ≅ Γ']} {VA : [_ ||-v<l> A ≅ A' | VΓ]} (Vt : [_ ||-v<l> t ≅ t' : _ | VΓ | VA]) :
  packed_valid_tm l (&(& Γ, A), t) (&(& Γ', A'), t') := (& mkVty VA; Vt ).

Ltac2 mkvty c := preterm:(mkVty $preterm:c).
Ltac2 mkvtm c := preterm:(mkVtm $preterm:c).
Ltac2 pair a b := constr:((& $a, $b)).


Ltac2 pose_proof c :=
  let h := Fresh.in_goal @pprf in
  Std.assert (Std.AssertValue h c);
  Control.hyp h.


Ltac2 valid_ctx_matcher ty pfopt :=
  lazy_match! ty with
  | VAdequate VR ?g ?g' => Some (g, g'), pfopt
  | typeValidity ?g ?g' (VAd.pack ?vg) _ _ _ => Some (g, g'), Some vg
  | termEqValidity ?g ?g' _ _ _ ?vg _ _ _ => Some (g, g'), Some vg
  | _ => None, None
  end.

Ltac2 valid_ctx_rel h c :=
  match valid_ctx_matcher c (Some (Control.hyp h)) with
  | Some (g, g'), Some vg => [g,g',preterm:($vg)]
  | _, _ => []
  end.

Ltac2 valid_ty_matcher ty pfopt :=
  lazy_match! ty with
  | typeValidity ?g ?g' (VAd.pack ?vg) ?l ?a ?a' => Some (g, g', vg, a, a', l), pfopt
  | termEqValidity ?g ?g' ?l ?a ?a' ?vg ?va _ _ => Some (g, g', vg, a, a', l), Some va
  | _ => None, None
  end.

Ltac2 valid_ty_rel st h c :=
  match valid_ty_matcher c (Some (Control.hyp h)) with
  | Some (g, _g', vg, a, a', _l), Some va =>
    let (g0, wgg0) := Option.get (PER.repr st g) in
    let va0 := mkvty preterm:(let wgg0 := $preterm:wgg0 in irrValidTy (VΓ0:=$vg) (VΓ1:=urefl wgg0) wgg0 $va) in
    [pair g0 a, pair g0 a',  va0 ]
  | _, _ => []
  end.


Ltac2 valid_tm_matcher ty pfopt :=
  lazy_match! ty with
  | termEqValidity ?g ?g' ?_l ?a ?a' ?_vg ?va ?t ?t' => Some (pair g a, pair g' a', mkvty preterm:($va), t, t'), pfopt
  | _ => None, None
  end.

Definition ureflValidTy `{GenericTypingProperties} {Γ Γ' l A B} {VΓ : [||-v Γ ≅ Γ']} (VΓ' := urefl VΓ) :
  [Γ ||-v<l> A ≅ B | VΓ] -> [_ ||-v<l> B ≅ B | VΓ'].
Proof. apply ureflValidTy. Defined.

Ltac2 valid_tm_rel st h c :=
  lazy_match! c with
  | termEqValidity ?g ?_g' ?_l ?a ?_a' ?_vg ?va ?t ?t' =>
    let h := Control.hyp h in
    let (g0, wgg0) := Option.get_bt (PER.repr st g) in
    (* let va0 := mkvty constr:(irrValidTy (VΓ0:=$vg) (VΓ1:=urefl $wgg0) $wgg0 $va) in *)
    let (ga0, waa0) := Option.get_bt (PER.repr st (pair g0 a)) in
    let vt0 := mkvtm preterm:(
      let wgg0 := $preterm:wgg0 in
      let vaa0 := convValidTy' _ wgg0 (dsnd $preterm:waa0) in
      irrValidTm wgg0 $va (ureflValidTy vaa0) vaa0 $h)
    in
    [pair ga0 t, pair ga0 t', vt0]
  | _ => []
  end.

Ltac2 fail s := Control.throw (Tactic_failure (Some (Message.of_string s))).

Ltac2 solve_ctx st g g' :=
  let witness := match Constr.is_evar g, Constr.is_evar g' with
    | true, true => fail "Only evars"
    | true, false => Std.unify g g' ; PER.qrefl st g'
    | false, true => Std.unify g g' ; PER.qrefl st g
    | false, false => PER.get_witness_cstr st (g, g')
  end in
  match witness with
  | Some w =>
    (* Control.time (Some "pretype:") (fun () =>  *)
      Control.refine (fun _ => Constr.pretype w)
    (* ) *)
  | None => fail "Contexts are not convertibles"
  end.

Ltac2 solve_ty st g g' vg _l a a' :=
  match Constr.is_evar g, Constr.is_evar g' with
    | true, true => fail "Only evars (context)"
    | true, false => Std.unify g g'
    | false, true => Std.unify g g'
    | false, false => ()
  end ;
  let (g0, wgg0) := Option.get (PER.repr st g) in
  let witness := match Constr.is_evar a, Constr.is_evar a' with
    | true, true => fail "Only evars (types)"
    | true, false => Std.unify a a' ; PER.qrefl st (pair g0 a')
    | false, true => Std.unify a a' ; PER.qrefl st (pair g0 a)
    | false, false => PER.get_witness_cstr st (pair g0 a, pair g0 a')
  end in
  match witness with
  | Some w =>
    (* Control.time (Some "pretype:") (fun () => *)
      let wgg0 := pose_proof (Constr.pretype wgg0) in
      let w := pose_proof (Constr.pretype w) in
      Control.refine (fun _ => constr:(irrValidTy (VΓ1:=$vg) (symmetry $wgg0) (dsnd $w)))
    (* ) *)
  | None => fail "Types are not convertibles"
  end.

Ltac2 solve_tm st g g' vg a a' va _l t t' :=
  match Constr.is_evar g, Constr.is_evar g' with
    | true, true => fail "Only evars (context)"
    | true, false => Std.unify g g'
    | false, true => Std.unify g g'
    | false, false => ()
  end ;
  let (g0, wgg0) := Option.get (PER.repr st g) in
  match Constr.is_evar a, Constr.is_evar a' with
    | true, true => fail "Only evars (types)"
    | true, false => Std.unify a a'
    | false, true => Std.unify a a'
    | false, false => ()
  end ;
  let (ga0, waa0) := Option.get (PER.repr st (pair g0 a)) in
  let witness := match Constr.is_evar t, Constr.is_evar t' with
    | true, true => fail "Only evars (types)"
    | true, false => Std.unify t t' ; PER.qrefl st (pair ga0 t')
    | false, true => Std.unify t t' ; PER.qrefl st (pair ga0 t)
    | false, false => PER.get_witness_cstr st (pair ga0 t, pair ga0 t')
  end in
  match witness with
  | Some w =>
    (* Control.time (Some "pretype:") (fun () => *)
      let wgg0 := pose_proof (Constr.pretype wgg0) in
      let waa0 := pose_proof (Constr.pretype waa0) in
      let va0a := pose_proof constr:(convValidTy _ (symmetry $wgg0) (dsnd (symmetry $waa0))) in
      let w := pose_proof (Constr.pretype w) in
      Control.refine (fun _ => constr:(irrValidTm (VΓ1:=$vg) (symmetry $wgg0) _ $va $va0a (dsnd $w)))
    (* ) *)
  | None => fail "Terms are not convertibles"
  end.

Ltac2 solve_any get_st g :=
  lazy_match! g with
  | VAdequate VR ?g ?g' =>
    let st := get_st () in
    solve_ctx st g g'
    (* Control.time (Some "solveCtx:") (fun () => solve_ctx st g g') *)
  | typeValidity ?g ?g' (VAd.pack ?vg) ?l ?a ?a' =>
    let st := get_st () in
    solve_ty st g g' vg l a a'
    (* Control.time (Some "solveTy:") (fun () => solve_ty st g g' vg l a a') *)
  | termEqValidity ?g ?g' ?l ?a ?a' ?vg ?va ?t ?t' =>
    let st := get_st () in
    solve_tm st g g' vg a a' va l t t'
    (* Control.time (Some "solveTm:") (fun () => solve_tm st g g' vg a a' va l t t') *)
  | _ => fail "Term does not match"
  end.

Ltac2 init n :=
  let st := PER.make n in
  List.iter (PER.add_rel st valid_ctx_rel) (Control.hyps ());
  List.iter (PER.add_rel st (valid_ty_rel st)) (Control.hyps ()) ;
  List.iter (PER.add_rel st (valid_tm_rel st)) (Control.hyps ()) ; st.
  (* Control.time (Some "Init stage 1:") (fun () => List.iter (PER.add_rel st valid_ctx_rel) (Control.hyps ()));
  Control.time (Some "Init stage 2:") (fun () => List.iter (PER.add_rel st (valid_ty_rel st)) (Control.hyps ())) ;
  Control.time (Some "Init stage 3:") (fun () => List.iter (PER.add_rel st (valid_tm_rel st)) (Control.hyps ())) ; st. *)

Ltac2 irrValid () :=
  solve_any (fun () => init 42) (Control.goal ()).

Ltac irrValid := ltac2:(Control.enter irrValid).


Module Examples.
Section Examples.
Context `{GenericTypingProperties}.

Context {Γ0 Γ1 Γ2} (VΓ01 : [||-v Γ0 ≅ Γ1]) (VΓ02 : [||-v Γ0 ≅ Γ2]).

Lemma VΓ12 : [||-v Γ1 ≅ Γ2].
Proof.
  irrValid ().
Qed.

Context {l A B C D} (VAB : [_ ||-v<l> A ≅ B | VΓ01]) (VDC : [_ ||-v<l> C ≅ D | VΓ12]).

Lemma VBB2 (VΓ22 := urefl VΓ02) : [_ ||-v<l> B |VΓ22].
Proof.
  irrValid ().
Qed.

Lemma VAD10 (VΓ10 := symmetry VΓ01) (VCB : [_ ||-v<l> C ≅ B | VΓ12]) :
  [_ ||-v<l> A ≅ D | VΓ10].
Proof.
  irrValid ().
Qed.

Context {t u v} (Vtu : [_ ||-v<l> t ≅ u : _ | _ | VAB]) (Vvu : [_ ||-v<l> v ≅ u : _ | _ | VBB2]).

Lemma Vtt :  [_ ||-v<l> t ≅ t : _ | _ | VAB].
Proof.
  irrValid ().
Qed.

Lemma Vvt (VCB : [_ ||-v<l> C ≅ B | VΓ12]) : [_ ||-v<l> v ≅ t : _ | _ | VAD10 VCB].
Proof.
  irrValid ().
Qed.

End Examples.
End Examples.


(** Hoisting the let-in in the type of an hypothesis to the global context *)
(* Nothing to do with the rest of the file,
   to be moved to another place using Ltac2 when reasonable *)
Module HoistLetIn.

  Ltac2 rec hoist_let_in_aux cl t :=
    (* printf "Analysing %t" t ; *)
    lazy_match! t with
    | let x := ?b in @?t' x =>
      (* printf "Match: %t/ continuation %t" b t'; *)
      let h := Fresh.in_goal @hli in
      Std.set true (fun _ =>  Some h, b) cl ;
      let x := Control.hyp h in
      let k := Std.eval_cbn RedFlags.beta constr:($t' $x) in
      hoist_let_in_aux cl k
    | _ => ()
    end.

  Ltac2 hoist_let_in h :=
    hoist_let_in_aux {
      Std.on_hyps := Some [h, Std.AllOccurrences, Std.InHypTypeOnly] ;
      Std.on_concl := Std.NoOccurrences }
      (Constr.type (Control.hyp h)).

  (* Ltac hoist_let_in := ltac2:(h |- hoist_let_in (Option.get (Ltac1.to_ident h))). *)

End HoistLetIn.
