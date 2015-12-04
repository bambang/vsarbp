(** 
 Verified SAR-BP: A verified C implementation of SAR backprojection
 with a certified absolute error bound.
 
 Version 1.0 (2015-12-04)
 
 Copyright (C) 2015 Reservoir Labs Inc.
 All rights reserved.
 
 This file is free software. You can redistribute it and/or modify it
 under the terms of the GNU General Public License as published by the
 Free Software Foundation, either version 3 of the License (GNU GPL
 v3), or (at your option) any later version.  A verbatim copy of the
 GNU GPL v3 is included in gpl-3.0.txt.
 
 This file is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE for
 more details about the use and redistribution of this file and the
 whole Verified SAR-BP library.
 
 This work is sponsored in part by DARPA MTO as part of the Power
 Efficiency Revolution for Embedded Computing Technologies (PERFECT)
 program (issued by DARPA/CMO under Contract No: HR0011-12-C-0123). The
 views and conclusions contained in this work are those of the authors
 and should not be interpreted as representing the official policies,
 either expressly or implied, of the DARPA or the
 U.S. Government. Distribution Statement "A" (Approved for Public
 Release, Distribution Unlimited.)
 
 
 If you are using or modifying Verified SAR-BP in your work, please
 consider citing the following paper:
 
 Tahina Ramananandro, Paul Mountcastle, Benoit Meister and Richard
 Lethin.
 A Unified Coq Framework for Verifying C Programs with Floating-Point
 Computations.
 In CPP (5th ACM/SIGPLAN conference on Certified Programs and Proofs)
 2016.
 
 
 Verified SAR-BP derives from prior work listed in ACKS along with
 their copyright and licensing information.
 
 Verified SAR-BP requires third-party libraries listed in ACKS along
 with their copyright information.
*)
(**
Author: Tahina Ramananandro <ramananandro@reservoir.com>

Verification of a C implementation of 3D L2 norm
(norm() in backprojection.c)
*)

Require Import RAux.
Require Import List.
Require Import SARBackProjSource.
Require Import compcert.Integers.
Require Import compcert.Floats.
Require Import compcert.AST.
Require Import compcert.Values.
Require Import compcert.Memory.
Require Import compcert.Events.
Require Import compcert.Globalenvs.
Require Import compcert.Smallstep.
Require Import compcert.Clight.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Prop.Fprop_relative.
Require Import Fprop_absolute.
Require Import Clight2FPOpt.
Require Import SepLogic.
Require Import ClightFacts.
Require Import ClightTac.
Require Import ClightSep2.
Open Scope R_scope.

Local Existing Instance Clight2FP.nans.

Definition f_sqrt_correct ge fr_sqrt :=
  type_of_fundef fr_sqrt =
  Ctypes.Tfunction
    (Ctypes.Tcons (Clightdefs.tptr Clightdefs.tdouble)
                  (Ctypes.Tcons Clightdefs.tdouble Ctypes.Tnil)) Clightdefs.tvoid
    cc_default /\
  forall x,
  is_finite _ _ x = true ->
  0 <= B2R _ _ x ->
  forall pr,
    perm_order pr Writable ->
    forall o,
    (align_chunk Mfloat64 | Int.unsigned o)%Z ->
    forall P b m,
      holds (P ++ Pperm b (Int.unsigned o) pr (size_chunk_nat Mfloat64)) m ->
      let s0 := (Callstate fr_sqrt
                           (Vptr b o :: Vfloat x :: nil)
                           Kstop
                           m) in
      exists m',
        star Clight.step2 ge
             s0
             E0
             (Returnstate Vundef
                          Kstop
                          m')
        /\
        exists y,
          holds (P ++ Pval Mfloat64 b (Int.unsigned o) pr (Vfloat y)) m' /\
          y = FPLang.Bsqrt FPLang.Tdouble x
.

Definition f_sqrt_correct' ge fr_sqrt :=
  type_of_fundef fr_sqrt =
  Ctypes.Tfunction
    (Ctypes.Tcons (Clightdefs.tptr Clightdefs.tdouble)
                  (Ctypes.Tcons Clightdefs.tdouble Ctypes.Tnil)) Clightdefs.tvoid
    cc_default /\
  forall x,
  is_finite _ _ x = true ->
  0 <= B2R _ _ x ->
  forall pr,
    perm_order pr Writable ->
    forall o,
    (align_chunk Mfloat64 | Int.unsigned o)%Z ->
    forall P b m,
      holds (P ++ Pperm b (Int.unsigned o) pr (size_chunk_nat Mfloat64)) m ->
      let s0 := (Callstate fr_sqrt
                           (Vptr b o :: Vfloat x :: nil)
                           Kstop
                           m) in
      exists m',
        star Clight.step2 ge
             s0
             E0
             (Returnstate Vundef
                          Kstop
                          m')
        /\
        exists y,
          holds (P ++ Pval Mfloat64 b (Int.unsigned o) pr (Vfloat y)) m' /\
          y = FPLang.fval
                (env_
                   (Maps.PTree.set xH (Vfloat x) (Maps.PTree.empty _))
                )
                (FPLang.Unop (FPLang.Rounded1 FPLang.SQRT None) (FPLang.Var FPLang.Tdouble xH))
.

Lemma f_sqrt_correct'_eq: f_sqrt_correct' = f_sqrt_correct.
Proof.
  reflexivity.
Qed.

Require Import SARBackProjSourceOpt1.

Definition f_norm2_correct BOUNDS :=
  let '(norm2_error, norm2_left, norm2_right) := BOUNDS
  in
  forall
    os
    ps

    m bs P
    (Hm:
       holds
         (P ++
            Pperm bs (Int.unsigned os) ps (size_chunk_nat Mfloat64)
         )
         m)

    (Hos_align: (align_chunk Mfloat64 | Int.unsigned os)%Z )
    (Hps: perm_order ps Writable)

   x'
   (Hx'_range: xdiff_left <= B2R _ _ x' <= xdiff_right )

   y'
   (Hy'_range: ydiff_left <= B2R _ _ y' <= ydiff_right )

   z'
   (Hz'_range: zdiff_left <= B2R _ _ z' <= zdiff_right )

   (Hx'_finite: is_finite _ _ x' = true)
   (Hy'_finite: is_finite _ _ y' = true)
   (Hz'_finite: is_finite _ _ z' = true)

  ge,

   exists v1 : val,
     eval_expr ge empty_env
                (Maps.PTree.set _z (Vfloat z')
                   (Maps.PTree.set _y (Vfloat y')
                      (Maps.PTree.set _x (Vfloat x')
                         (Maps.PTree.set _n (Vptr bs os)
                            (create_undef_temps (fn_temps f_norm)))))) m
       (Ebinop Oadd
          (Ebinop Oadd
             (Ebinop Omul (Etempvar _x tdouble) (Etempvar _x tdouble) tdouble)
             (Ebinop Omul (Etempvar _y tdouble) (Etempvar _y tdouble) tdouble)
             tdouble)
          (Ebinop Omul (Etempvar _z tdouble) (Etempvar _z tdouble) tdouble)
          tdouble) v1
     /\
     exists f,
       v1 = Vfloat f /\
       is_finite _ _ f = true /\
       norm2_left <= B2R _ _ f <= norm2_right /\
       Rabs (B2R _ _ f - (B2R _ _ x' * B2R _ _ x' + B2R _ _ y' * B2R _ _ y' + B2R _ _ z' * B2R _ _ z')) <= norm2_error.

Lemma f_norm2_body_correct' :
  { BOUNDS |
    f_norm2_correct BOUNDS }.
Proof.
  eexists (_, _, _).
  unfold f_norm2_correct.
  intros os ps m bs P Hm Hos_align.
  intros Hps x' Hx'_range y'.
  intros Hy'_range z' Hz'_range Hx'_finite Hy'_finite Hz'_finite ge.

  unfold xdiff_left, xdiff_right in Hx'_range.
  unfold ydiff_left, ydiff_right in Hy'_range.
  unfold zdiff_left, zdiff_right in Hz'_range.

  apply eval_expr_exists_filter_float.
  apply eval_expr_exists_filter_domain.
  apply Vfloat_exists.
  (* here comes the framework into play! *)
  Transparent Float.of_bits.
  Transparent Int64.repr.
  C_to_float_as r Hr.
  compute_fval_as Hr Hr_finite Hr_val.

  Require Import Interval.Interval_tactic.
  match type of Hr_val with
      ?z = _ =>
      interval_intro z with (i_prec 128) as Hr_range
  end.
  rewrite Hr_val in Hr_range.
  destruct (rememb (B2R _ _ r - (B2R _ _ x' * B2R _ _ x' + B2R _ _ y' * B2R _ _ y' + B2R _ _ z' * B2R _ _ z'))) as (err & Herr).
  generalize Herr. intro Herr'.
  rewrite <- Hr_val in Herr'.
  ring_simplify in Herr'.
  match type of Herr' with
      _ = ?z =>
      interval_intro (Rabs z) upper with (i_prec 128) as Hr_error
  end.
  rewrite <- Herr' in Hr_error.
  clear Herr'.
  subst err.

  solve_trivial.
  eassumption.
Defined.

Definition norm2_error' :=
  let (x, _) := f_norm2_body_correct' in 
  let '(y, _, _) := x in y
.

Definition norm2_error'_eq := $( field_eq norm2_error' )$ .

Definition norm2_error := $( match type of norm2_error'_eq with _ = ?z => exact z end )$ .

Definition norm2_left' :=
  let (x, _) := f_norm2_body_correct' in 
  let '(_, y, _) := x in y
.

Definition norm2_left'_eq := $( field_eq norm2_left' )$ .

Definition norm2_left := $( match type of norm2_left'_eq with _ = ?z => exact z end )$ .

Definition norm2_right' :=
  let (x, _) := f_norm2_body_correct' in 
  let '(_, _, y) := x in y
.

Definition norm2_right'_eq := $( field_eq norm2_right' )$ .

Definition norm2_right := $( match type of norm2_right'_eq with _ = ?z => exact z end )$ .

Lemma f_norm2_body_correct:
  f_norm2_correct (norm2_error, norm2_left, norm2_right).
Proof.
  unfold norm2_error. rewrite <- norm2_error'_eq.
  unfold norm2_left. rewrite <- norm2_left'_eq.
  unfold norm2_right. rewrite <- norm2_right'_eq.
  unfold norm2_error', norm2_left', norm2_right'.
  destruct f_norm2_body_correct'.
  destruct x.
  destruct p.
  assumption.
Qed.

Local Existing Instances
      FPLang.map_nat FPLang.compcert_map
.

Lemma fshift_correct:
  forall (V : Type) (NANS : FPLang.Nans)
    (env : forall ty : FPLang.type, V -> FPLang.ftype ty) 
    (e : FPLang.expr) o,
           FPLang.fval env e = o ->
           {
             u : _ &
                   {v |
                    u = (FPLangOpt.fshift e) /\
                    FPLang.fval env u =
                    eq_rect_r FPLang.ftype o v} }
.
Proof.
  intros.
  subst o.
  esplit.
  esplit.
  split; eauto.
  apply FPLangOpt.fshift_correct.
Defined.

Ltac interval_with c :=
  match goal with
    |- ?a <= ?b =>
    interval_intro (a - b) with c;
      lra
    | |- ?a < ?b =>
    let K := fresh in
    interval_intro (a - b) with c;
      lra
  end.

Definition f_norm_correct BOUNDS ge fn_norm :=
  let '(f_norm_error, norm_left, norm_right) := BOUNDS in
type_of_fundef fn_norm =
   Ctypes.Tfunction
     (Ctypes.Tcons (Clightdefs.tptr Clightdefs.tdouble)
        (Ctypes.Tcons Clightdefs.tdouble
           (Ctypes.Tcons Clightdefs.tdouble
              (Ctypes.Tcons Clightdefs.tdouble
                 Ctypes.Tnil)))) Clightdefs.tvoid cc_default
/\
  forall
    os
    (Hos_align: (align_chunk Mfloat64 | Int.unsigned os)%Z )
    ps
    (Hps: perm_order ps Writable)

    m bs P
    (Hm:
       holds
         (P ++
            Pperm bs (Int.unsigned os) ps (size_chunk_nat Mfloat64)
         )
         m)

   x'
   (Hx'_finite: is_finite _ _ x' = true)
   (Hx'_range: xdiff_left <= B2R _ _ x' <= xdiff_right )

   y'
   (Hy'_finite: is_finite _ _ y' = true)
   (Hy'_range: ydiff_left <= B2R _ _ y' <= ydiff_right )

   z'
   (Hz'_finite: is_finite _ _ z' = true)
   (Hz'_range: zdiff_left <= B2R _ _ z' <= zdiff_right )

  ,
    let st0 := (Callstate fn_norm
                          (Vptr bs os :: Vfloat x' :: Vfloat y' :: Vfloat z' :: nil)
                          Kstop
                          m) in
    exists m',
      star Clight.step2 ge
           st0
           E0
           (Returnstate Vundef Kstop m')
      /\
      exists res,
      is_finite _ _ res = true
      /\
      Rabs (B2R _ _ res - R_sqrt.sqrt (B2R _ _ x' * B2R _ _ x' + B2R _ _ y' * B2R _ _ y' + B2R _ _ z' * B2R _ _ z')) <= f_norm_error
      /\
      norm_left <= B2R _ _ res <= norm_right
      /\
      holds
        (P ++
           Pval Mfloat64 bs (Int.unsigned os) ps (Vfloat res)
        )
        m'
.

Require Import SARBackProjSourceSqrt.

Lemma f_norm_body_correct': { f_norm_error | forall
      (ge: Clight.genv)
      b_sqrt fn_sqrt
      (Hb_sqrt_symb: Genv.find_symbol ge _sqrt = Some b_sqrt)
      (Hb_sqrt_funct: Genv.find_funct_ptr ge b_sqrt = Some fn_sqrt)

      (Hf_sqrt_correct: _sqrt_correct ge fn_sqrt)
,
  f_norm_correct f_norm_error ge (Internal f_norm)
}.
Proof.
  eexists (_, _, _).
  intros ge b_sqrt fn_sqrt Hb_sqrt_symb Hb_sqrt_funct.
  intros Hf_sqrt_correct. 
  destruct Hf_sqrt_correct as (sqrt_type & Hf_sqrt_correct).

  split.
  {
    reflexivity.
  }
  intros os Hos_align ps Hps.
  intros m bs P Hm x'.
  intros Hx'_finite Hx'_range y' Hy'_finite Hy'_range z' Hz'_finite Hz'_range st0.

  unfold st0; clear st0.

  match goal with
    |- exists m', Smallstep.star step2 ?ge ?s Events.E0 (Returnstate Vundef Kstop m') /\ ?P =>
    cut 
      (exists s',
         Smallstep.star step2 ge s Events.E0 s' /\
         exists m',
           s' = Returnstate Vundef Kstop m' /\
           P)
  end.
  {
    let H := fresh in
    intro H;  break H; subst; eauto 15.
  }
  
  apply star_call_eval_funcall_exists.
  apply eval_funcall_exists_internal.
  solve_trivial.

  simpl fn_vars.
  unfold alloc_variables_prop.
  solve_trivial.

  simpl fn_body.
  apply exec_Sseq_exists.
  apply exec_Scall_exists.
  solve_trivial.
  repeat ClightSep2.run.

  edestruct f_norm2_body_correct with (ge := ge) as (? & EVAL & n2 & ? & Hn2_finite & Hn2_range & Hn2_error); try eassumption.
  subst.
  solve_trivial.
  clear EVAL.
  unfold out_normal_b.

  apply eval_funcall_exists_star_call.  
  apply exec_call_exists.
  solve_trivial.
  eapply exists_modus_ponens.
  {
    eapply exists_double_elim.
    eapply Hf_sqrt_correct.
    { assumption. }
    { unfold norm2_left in Hn2_range. lra. }
  }
  intros s1 (v & ? & Hv).
  subst s1.
  unfold Bsqrt in Hv.
  match type of Hv with
      _ = Fappli_IEEE.Bsqrt ?prec ?emax ?gt ?lt ?nan ?mode ?u =>
      generalize (Bsqrt_correct prec emax gt lt nan mode u)
  end.
  rewrite <- Hv; clear Hv.
  intros (Hv_val & Hv_finite_ & _).
  assert (is_finite _ _ v = true) as Hv_finite.
  {
    destruct n2; auto.
    destruct b; auto.
    simpl in Hn2_range.
    unfold Fcore_defs.F2R in Hn2_range.
    simpl in Hn2_range.
    unfold norm2_left in Hn2_range.
    rewrite P2R_INR in Hn2_range.
    generalize (bpow_gt_0 radix2 e).
    generalize (INR_pos m0).
    intros U V.
    generalize (Rmult_lt_0_compat _ _ U V).
    lra.
  }
  clear Hv_finite_.
  simpl round_mode in Hv_val.
  match type of Hv_val with
      _ = round ?beta (Fcore_FLT.FLT_exp ?emin ?prec) (Znearest ?choice) ?x =>
      generalize (error_N_FLT beta emin prec $( vm_compute; congruence )$ choice x)
  end.
  intros (d & e & Hd & He & _ & Hv_).
  rewrite Hv_ in Hv_val; clear Hv_.
  unfold fprec in Hv_val.
  simpl in Hv_val.
  simpl in Hd, He.
  solve_trivial.

  apply star_exists_refl.
  solve_trivial.

  apply exec_Sassign_exists.
  repeat run.

  holds_storev_solve.
  intros m Hm.
  solve_trivial.

  simpl outcome_result_value_exists.
  solve_trivial.

  apply and_assoc.
  split; eauto.
    
  unfold xdiff_left, ydiff_left, zdiff_left, norm2_left, norm2_error in *.
  generalize Hn2_error. intro Hn2_error'.
  apply Fcore_Raux.Rabs_le_inv in Hn2_error'.
  apply sqrt_abs_error_bound in Hn2_error; try lra.
  match type of Hn2_error with
    _ <= ?z =>
    destruct (rememb z) as (c & Hc);
      rewrite <- Hc in Hn2_error
  end.
  unfold norm2_right, xdiff_left, xdiff_right, ydiff_left, ydiff_right, zdiff_left, zdiff_right in *.
  match type of Hc with
      _ = ?z =>
      interval_intro z upper as Hc_range';
        rewrite <- Hc in Hc_range';
        clear Hc
  end.
  generalize (Rle_trans _ _ _ Hn2_error Hc_range').
  clear c Hn2_error Hc_range'.
  intro Hc.

  assert (B2R _ _ v - sqrt (B2R _ _ n2) = sqrt (B2R _ _ n2) * d + e) as Hy_error_eq.
  {
    rewrite Hv_val.
    ring.
  }
  match type of Hy_error_eq with
      _ = ?z =>
      interval_intro (Rabs z) upper with (i_prec 128) as Hy_error
  end.
  rewrite <- Hy_error_eq in Hy_error; clear Hy_error_eq.
  split.
  {
    eexact (Rabs_triang2 _ _ _ _ _ Hy_error Hc).
  }
  match type of Hv_val with
      _ = ?z =>
      interval_intro z with (i_prec 128) as Hy_range
  end.
  rewrite <- Hv_val in Hy_range.
  eexact Hy_range.

Defined.

Definition f_norm_error' :=
 let (x, _) := f_norm_body_correct' in 
 let '(y, _, _) := x in y.

Definition f_norm_error'_eq := 
  $( field_eq f_norm_error' )$ .

Definition f_norm_error := 
  $( match type of f_norm_error'_eq with _ = ?z => exact z end )$ .

Definition f_norm_left' :=
 let (x, _) := f_norm_body_correct' in 
 let '(_, y, _) := x in y.

Definition f_norm_left'_eq := 
  $( field_eq f_norm_left' )$ .

Definition f_norm_left := 
  $( match type of f_norm_left'_eq with _ = ?z => exact z end )$ .

Definition f_norm_right' :=
 let (x, _) := f_norm_body_correct' in 
 let '(_, _, y) := x in y.

Definition f_norm_right'_eq := 
  $( field_eq f_norm_right' )$ .

Definition f_norm_right := 
  $( match type of f_norm_right'_eq with _ = ?z => exact z end )$ .

Lemma f_norm_body_correct: forall
      (ge: Clight.genv)
      b_sqrt fn_sqrt
      (Hb_sqrt_symb: Genv.find_symbol ge _sqrt = Some b_sqrt)
      (Hb_sqrt_funct: Genv.find_funct_ptr ge b_sqrt = Some fn_sqrt)

      (Hf_sqrt_correct: _sqrt_correct ge fn_sqrt)
,
  f_norm_correct (f_norm_error, f_norm_left, f_norm_right) ge (Internal f_norm)
.
Proof.
  unfold f_norm_error.
  rewrite <- f_norm_error'_eq.
  unfold f_norm_left.
  rewrite <- f_norm_left'_eq.
  unfold f_norm_right.
  rewrite <- f_norm_right'_eq.
  unfold f_norm_error', f_norm_left', f_norm_right'.
  destruct f_norm_body_correct'.
  destruct x.
  destruct p.
  assumption.
Qed.
