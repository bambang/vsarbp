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

Specifications of ISO C99 sine/cosine.
*)

Require Import Reals.
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
Require Import LibTac.
Require Import RAux.

Ltac solve_no_overflow :=
  apply Fcore_Raux.Rlt_bool_true;
  simpl Fcore_Raux.bpow in * |- *;
  apply Fcore_Raux.Rabs_lt;
  lra.

(* The "remember" built-in tactic is very costly at proof-checking
   time (Qed), so we provide an alternative which works at least for
   non-dependent arguments. *)

Ltac rememb t y H :=
  destruct (rememb t) as (y & H);
  rewrite <- H in * |- *
.

Require Import ClightFacts.

(* We assume that sin and cos are correctly rounded,
   at least in the argument range -2^30..2^30.
*)

Definition x_right := Eval vm_compute in Fcore_Raux.Z2R (2 ^ 30).

Definition x_left := Eval vm_compute in - x_right.

Require Import FPLang.

Definition f_unary_correct f ge cef :=
  type_of_fundef cef =
  Ctypes.Tfunction (Ctypes.Tcons Clightdefs.tdouble
                                 Ctypes.Tnil)
                   Clightdefs.tdouble cc_default /\
  forall x m,
    is_finite _ _ x = true ->
    x_left <= B2R _ _ x <= x_right ->
    let s0 := (Callstate cef
                         (Vfloat x :: nil)
                         Kstop
                         m) in
    exists y,
      star Clight.step2 ge
           s0
           E0
           (Returnstate (Vfloat y)
                        Kstop
                        m)
      /\
      is_finite _ _ y = true 
      /\
      B2R _ _ y = round Fcore_Zaux.radix2 (Fcore_FLT.FLT_exp (3 - femax Tdouble - fprec Tdouble) (fprec Tdouble))
         (round_mode mode_NE) (f (B2R _ _ x))
.

(* Let us provide more general correctness statements with explicit error bounds *)

Definition f_unary_correct_gen_ f BOUND ge cef :=
  type_of_fundef cef =
  Ctypes.Tfunction (Ctypes.Tcons Clightdefs.tdouble
                                 Ctypes.Tnil)
                   Clightdefs.tdouble cc_default /\
  forall x m,
    is_finite _ _ x = true ->
    x_left <= B2R _ _ x <= x_right ->
    let s0 := (Callstate cef
                         (Vfloat x :: nil)
                         Kstop
                         m) in
    exists y,
      star Clight.step2 ge
           s0
           E0
           (Returnstate (Vfloat y)
                        Kstop
                        m)
      /\
      is_finite _ _ y = true 
      /\
      Rabs (B2R _ _ y - f (B2R _ _ x)) <= BOUND
.

Lemma f_unary_correct_generalize_: 
  { BOUND |
    forall f,
      (forall x, -1 <= f x <= 1) ->
      forall ge cef,
        f_unary_correct f ge cef ->
        f_unary_correct_gen_ f BOUND ge cef }.
Proof.
  esplit.
  intros f Hf ge cef (Hcef_type & Hcef_correct).
  split; auto.
  intros x m Hx_finite Hx_range s0.
  specialize (Hcef_correct x m Hx_finite Hx_range).
  destruct Hcef_correct as (y & Hy & Hy_finite & Hy_val).
  solve_trivial.
  specialize (Hf (B2R _ _ x)).
  simpl round_mode in Hy_val.
  match type of Hy_val with
      _ = round ?beta (Fcore_FLT.FLT_exp ?emin ?prec) (Znearest ?choice) ?x =>
      generalize (error_N_FLT beta emin prec $( vm_compute; congruence )$ choice x)
  end.
  intros (d & e & Hd & He & _ & Hv_).
  rewrite Hv_ in Hy_val; clear Hv_.
  unfold fprec in Hy_val.
  simpl in Hy_val.
  simpl in Hd, He.
  assert (B2R _ _ y - f (B2R _ _ x) = f (B2R _ _ x) * d + e) as Hy_error_eq.
  {
    rewrite Hy_val.
    ring.
  }
  Require Import Interval.Interval_tactic.
  match type of Hy_error_eq with
      _ = ?z =>
      interval_intro (Rabs z) upper with (i_prec 64) as Hy_error
  end.
  rewrite <- Hy_error_eq in Hy_error; clear Hy_error_eq.
  eexact Hy_error.
Defined.

Definition f_unary_error' :=
 let (x, _) := f_unary_correct_generalize_ in 
 x.

Require Import FieldEq.

Definition f_unary_error'_eq := 
  $( field_eq f_unary_error' )$ .

Definition f_unary_error := 
  $( match type of f_unary_error'_eq with _ = ?z => exact z end )$ .

Lemma f_unary_correct_generalize: 
    forall f,
      (forall x, -1 <= f x <= 1) ->
      forall ge cef,
        f_unary_correct f ge cef ->
        f_unary_correct_gen_ f f_unary_error ge cef .
Proof.
  unfold f_unary_error.
  rewrite <- f_unary_error'_eq.
  unfold f_unary_error'.
  destruct f_unary_correct_generalize_.
  assumption.
Qed.

Definition f_unary_correct_gen f BOUND ge cef :=
  type_of_fundef cef =
  Ctypes.Tfunction (Ctypes.Tcons Clightdefs.tdouble
                                 Ctypes.Tnil)
                   Clightdefs.tdouble cc_default /\
  forall x m,
    is_finite _ _ x = true ->
    x_left <= B2R _ _ x <= x_right ->
    let s0 := (Callstate cef
                         (Vfloat x :: nil)
                         Kstop
                         m) in
    exists y,
      star Clight.step2 ge
           s0
           E0
           (Returnstate (Vfloat y)
                        Kstop
                        m)
      /\
      is_finite _ _ y = true 
      /\
      Rabs (B2R _ _ y - f (B2R _ _ x)) <= BOUND
      /\
      - (1 + BOUND) <= B2R _ _ y <= 1 + BOUND
.

Lemma f_unary_correct_gen_intro BOUND f:
  (forall x, -1 <= f x <= 1) ->
  forall ge cef,
    f_unary_correct_gen_ f BOUND ge cef ->
    f_unary_correct_gen f BOUND ge cef.
Proof.
  intros H ge cef H0.
  destruct H0 as (H0_type & H0_correct).
  split; auto.
  intros x m H0 H1 s0.
  specialize (H0_correct x m H0 H1).
  destruct H0_correct as (y & Hy & Hy_finite & Hy_val).
  solve_trivial.
  specialize (H (B2R _ _ x)).
  apply Fcore_Raux.Rabs_le_inv in Hy_val.
  lra.
Qed.

Lemma f_cos_correct:
  forall ge cef,
    f_unary_correct cos ge cef ->
    f_unary_correct_gen cos f_unary_error ge cef.
Proof.
  intros ge cef H.
  apply f_unary_correct_gen_intro; auto using COS_bound.
  apply f_unary_correct_generalize; auto using COS_bound.
Qed.

Lemma f_sin_correct:
  forall ge cef,
    f_unary_correct sin ge cef ->
    f_unary_correct_gen sin f_unary_error ge cef.
Proof.
  intros ge cef H.
  apply f_unary_correct_gen_intro; auto using SIN_bound.
  apply f_unary_correct_generalize; auto using SIN_bound.
Qed.
