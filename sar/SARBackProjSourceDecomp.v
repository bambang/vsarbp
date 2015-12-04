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

Decomposition of our implementation of SAR backprojection into more
elementary statement blocks to be verified individually.
*)

Require Export Reals.
Require Export Psatz.
Require Export List.
Require Export Values.
Require Export Events.
Require Export Smallstep.
Require Export Clight.
Require Export Clightdefs.
Require Export LibTac.
Require Export SARBackProjSource.
Require Export SARBounds.
Require Export SepLogic.
Require Export ClightTac.
Open Scope R_scope.

(** Split the code of SAR backprojection into smaller slices 
    to compute the bounds of the arguments
    to norm, bin_sample, and sin_cos. *)

Definition f_sar_backprojection_loop_y := 
  $(
      let s := (eval cbn in (fn_body (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES))))
      in
      let t := first_loop s in
      exact t
    )$ .

Lemma stmt_assoc_l2r_head u a b c:
  stmt_assoc u (Ssequence (Ssequence a b) c) -> 
  stmt_assoc u (Ssequence a (Ssequence b c)).
Proof.
  intros H.
  setoid_rewrite stmt_assoc_l2r in H.
  assumption.
Qed.

Lemma stmt_assoc_r2l_head u a b c:
  stmt_assoc u (Ssequence a (Ssequence b c)) ->
  stmt_assoc u (Ssequence (Ssequence a b) c).
Proof.
  intros H.
  setoid_rewrite stmt_assoc_r2l in H.
  assumption.
Qed.

Lemma f_sar_backprojection_loop_y_pre_exists_1:
    {s1 |
     stmt_assoc (fn_body (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES))) (Ssequence s1 f_sar_backprojection_loop_y)}.
Proof.
  esplit.
  destruct (rememb_gen stmt_assoc (fn_body (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES)))) as (u & uL & uR).
  setoid_rewrite uL.
  clear uL.
  let rec t :=
      (
        eassumption
          ||
          (
            apply stmt_assoc_r2l_head in uR;
            t
          )
      )
  in
  t.
Defined.

Definition f_sar_backprojection_loop_y_pre_1' :=
  let (s1, _) := f_sar_backprojection_loop_y_pre_exists_1 in s1.

Lemma f_sar_backprojection_loop_y_pre_1_eq' :
     stmt_assoc (fn_body (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES))) (Ssequence f_sar_backprojection_loop_y_pre_1'  f_sar_backprojection_loop_y).
Proof.
  unfold f_sar_backprojection_loop_y_pre_1'.
  destruct f_sar_backprojection_loop_y_pre_exists_1.
  assumption.
Qed.

Lemma f_sar_backprojection_loop_y_pre_exists_2:
    {s1 |
     stmt_assoc f_sar_backprojection_loop_y_pre_1' s1}.
Proof.
  esplit.
  cbn.
  repeat rewrite stmt_assoc_l2r.
  reflexivity.
Defined.

Definition f_sar_backprojection_loop_y_pre' :=
  let (s1, _) := f_sar_backprojection_loop_y_pre_exists_2 in s1.

Definition f_sar_backprojection_loop_y_pre := Eval cbn in f_sar_backprojection_loop_y_pre'.

Lemma f_sar_backprojection_loop_y_pre_2_eq' : 
     stmt_assoc f_sar_backprojection_loop_y_pre_1' f_sar_backprojection_loop_y_pre' .
Proof.
  unfold f_sar_backprojection_loop_y_pre' .
  destruct f_sar_backprojection_loop_y_pre_exists_2.
  assumption.
Qed.

Lemma f_sar_backprojection_loop_y_pre_2_eq : 
     stmt_assoc f_sar_backprojection_loop_y_pre_1' f_sar_backprojection_loop_y_pre .
Proof f_sar_backprojection_loop_y_pre_2_eq' .

Lemma f_sar_backprojection_loop_y_pre_eq:
     stmt_assoc (fn_body (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES))) (Ssequence f_sar_backprojection_loop_y_pre f_sar_backprojection_loop_y).
Proof.
  setoid_rewrite <- f_sar_backprojection_loop_y_pre_2_eq.
  apply f_sar_backprojection_loop_y_pre_1_eq' .
Qed.

Definition f_sar_backprojection_loop_y_body :=
  $(
      let s := (eval unfold f_sar_backprojection_loop_y in f_sar_backprojection_loop_y) in
      match s with
        | Sloop (Ssequence _ ?s1) _ => exact s1
      end
    )$.

Lemma f_sar_backprojection_loop_y_body_fold:
    $( 
        let s := (eval unfold f_sar_backprojection_loop_y_body in f_sar_backprojection_loop_y_body)
        in exact s
      )$ =
    f_sar_backprojection_loop_y_body.
Proof.
  reflexivity.
Qed.

Definition f_sar_backprojection_loop_x :=
  $(
      let s := (eval unfold f_sar_backprojection_loop_y_body in f_sar_backprojection_loop_y_body) in
      let t := first_loop s in
      exact t
    )$.

Lemma f_sar_backprojection_loop_x_pre_exists:
    {s1 |
     stmt_assoc f_sar_backprojection_loop_y_body (Ssequence s1 f_sar_backprojection_loop_x)}.
Proof.
  esplit.
  destruct (rememb_gen stmt_assoc f_sar_backprojection_loop_y_body) as (u & uL & uR).
  setoid_rewrite uL.
  clear uL.
  let rec t :=
      (
        eassumption
          ||
          (
            apply stmt_assoc_r2l_head in uR;
            t
          )
      )
  in
  t.
Defined.

Definition f_sar_backprojection_loop_x_pre' :=
  let (s1, _) := f_sar_backprojection_loop_x_pre_exists in s1.

Definition f_sar_backprojection_loop_x_pre := Eval cbn in f_sar_backprojection_loop_x_pre'.

Lemma f_sar_backprojection_loop_x_pre'_eq:
  f_sar_backprojection_loop_x_pre' = f_sar_backprojection_loop_x_pre.
Proof.
  reflexivity.
Qed.

Lemma f_sar_backprojection_loop_x_pre_eq:
     stmt_assoc f_sar_backprojection_loop_y_body (Ssequence f_sar_backprojection_loop_x_pre f_sar_backprojection_loop_x).
Proof.
  rewrite <- f_sar_backprojection_loop_x_pre'_eq.
  unfold f_sar_backprojection_loop_x_pre'.
  destruct f_sar_backprojection_loop_x_pre_exists.
  assumption.
Qed.

Definition f_sar_backprojection_loop_x_body :=
  $(
      let s := (eval unfold f_sar_backprojection_loop_x in f_sar_backprojection_loop_x) in
      match s with
        | Sloop (Ssequence _ ?s1) _ => exact s1
      end
    )$.

Lemma f_sar_backprojection_loop_x_body_fold:
    $( 
        let s := (eval unfold f_sar_backprojection_loop_x_body in f_sar_backprojection_loop_x_body)
        in exact s
      )$ =
    f_sar_backprojection_loop_x_body.
Proof.
  reflexivity.
Qed.

Definition f_sar_backprojection_loop_p :=
  $(
      let s := (eval unfold f_sar_backprojection_loop_x_body in f_sar_backprojection_loop_x_body) in
      let t := first_loop s in
      exact t
    )$.

Lemma f_sar_backprojection_loop_p_fold:
    $(
        let s := (eval unfold f_sar_backprojection_loop_p in f_sar_backprojection_loop_p) in
        exact s
      )$ = f_sar_backprojection_loop_p.
Proof.
  reflexivity.
Qed.

Lemma f_sar_backprojection_loop_p_pre_post_exists_1:
    {s1s2 |
     let '(s1, s2) := s1s2 in
     stmt_assoc f_sar_backprojection_loop_x_body (Ssequence s1 (Ssequence f_sar_backprojection_loop_p s2))}.
Proof.
  eexists (_, _).
  destruct (rememb_gen stmt_assoc f_sar_backprojection_loop_x_body) as (u & uL & uR).
  setoid_rewrite uL.
  clear uL.
  unfold f_sar_backprojection_loop_x_body in uR.
  fold f_sar_backprojection_loop_p in uR.
  repeat setoid_rewrite stmt_assoc_r2l in uR.
  let rec t :=
      (
        eassumption
          ||
          (
            apply stmt_assoc_l2r_head in uR;
            t
          )
      )
  in
  t.
Defined.

Definition f_sar_backprojection_loop_p_pre_1' :=
  let (s, _) := f_sar_backprojection_loop_p_pre_post_exists_1 in 
  let (s1, _) := s in
  s1.

Definition f_sar_backprojection_loop_p_pre_1 := Eval cbn in f_sar_backprojection_loop_p_pre_1'.

Definition f_sar_backprojection_loop_p_post' :=
  let (s, _) := f_sar_backprojection_loop_p_pre_post_exists_1 in 
  let (_, s2) := s in
  s2.

Definition f_sar_backprojection_loop_p_post := Eval cbn in f_sar_backprojection_loop_p_post'.

Lemma f_sar_backprojection_loop_p_pre_post_eq_1' :
     stmt_assoc f_sar_backprojection_loop_x_body (Ssequence f_sar_backprojection_loop_p_pre_1'  (Ssequence f_sar_backprojection_loop_p f_sar_backprojection_loop_p_post' )).
Proof.
  unfold f_sar_backprojection_loop_p_pre_1'.
  unfold f_sar_backprojection_loop_p_post'.
  destruct f_sar_backprojection_loop_p_pre_post_exists_1 as [[? ?] ?].
  assumption.
Qed.

Lemma f_sar_backprojection_loop_p_pre_post_eq_1:
     stmt_assoc f_sar_backprojection_loop_x_body (Ssequence f_sar_backprojection_loop_p_pre_1 (Ssequence f_sar_backprojection_loop_p f_sar_backprojection_loop_p_post)).
Proof f_sar_backprojection_loop_p_pre_post_eq_1' .

Lemma f_sar_backprojection_loop_p_pre_exists_2:
    {s1 |
     stmt_assoc f_sar_backprojection_loop_p_pre_1 s1}.
Proof.
  esplit.
  unfold f_sar_backprojection_loop_p_pre_1.
  repeat rewrite stmt_assoc_l2r.
  reflexivity.
Defined.

Definition f_sar_backprojection_loop_p_pre' :=
  let (s1, _) := f_sar_backprojection_loop_p_pre_exists_2 in s1.

Definition f_sar_backprojection_loop_p_pre := Eval cbn in f_sar_backprojection_loop_p_pre'.

Lemma f_sar_backprojection_loop_p_pre'_eq:
  f_sar_backprojection_loop_p_pre' = f_sar_backprojection_loop_p_pre.
Proof.
  reflexivity.
Qed.

Lemma f_sar_backprojection_loop_p_pre_2_eq:
     stmt_assoc f_sar_backprojection_loop_p_pre_1 f_sar_backprojection_loop_p_pre.
Proof.
  rewrite <- f_sar_backprojection_loop_p_pre'_eq.
  unfold f_sar_backprojection_loop_p_pre'.
  destruct f_sar_backprojection_loop_p_pre_exists_2.
  assumption.
Qed.

Lemma f_sar_backprojection_loop_p_pre_post_eq:
     stmt_assoc f_sar_backprojection_loop_x_body (Ssequence f_sar_backprojection_loop_p_pre (Ssequence f_sar_backprojection_loop_p f_sar_backprojection_loop_p_post)).
Proof.
  setoid_rewrite <- f_sar_backprojection_loop_p_pre_2_eq.
  apply f_sar_backprojection_loop_p_pre_post_eq_1.
Qed.

Definition f_sar_backprojection_loop_p_body :=
  $(
      let s := (eval unfold f_sar_backprojection_loop_p in f_sar_backprojection_loop_p) in
      match s with
        | Sloop (Ssequence _ ?s1) _ => exact s1
      end
    )$.

Lemma f_sar_backprojection_loop_p_body_fold:
    $( 
        let s := (eval unfold f_sar_backprojection_loop_p_body in f_sar_backprojection_loop_p_body)
        in exact s
      )$ =
    f_sar_backprojection_loop_p_body.
Proof.
  reflexivity.
Qed.

Lemma f_sar_backprojection_pulse_contrib_exists:
    {s1v1v2 |
     let '(s1, v1, v2) := s1v1v2 in
     stmt_assoc f_sar_backprojection_loop_p_body (Ssequence s1 (Ssequence (Sset _contrib_r v1) (Sset _contrib_i v2))) }.
Proof.
  eexists (_, _, _).
  destruct (rememb_gen stmt_assoc f_sar_backprojection_loop_p_body) as (u & uL & uR).
  unfold f_sar_backprojection_loop_p_body in uR.
  repeat setoid_rewrite stmt_assoc_r2l in uR.
  setoid_rewrite stmt_assoc_l2r in uR.
  rewrite uR in uL.
  eexact uL.
Defined.

Definition f_sar_backprojection_pulse_contrib' :=
  let (x, _) := f_sar_backprojection_pulse_contrib_exists in
  let '(s, _, _) := x in s.

Definition f_sar_backprojection_pulse_contrib_r' :=
  let (x, _) := f_sar_backprojection_pulse_contrib_exists in
  let '(_, s, _) := x in s.

Definition f_sar_backprojection_pulse_contrib_i' :=
  let (x, _) := f_sar_backprojection_pulse_contrib_exists in
  let '(_, _, s) := x in s.

Lemma f_sar_backprojection_pulse_contrib_eq' :
  stmt_assoc f_sar_backprojection_loop_p_body (Ssequence f_sar_backprojection_pulse_contrib' (Ssequence (Sset _contrib_r f_sar_backprojection_pulse_contrib_r') (Sset _contrib_i f_sar_backprojection_pulse_contrib_i' ))) .
Proof.
  unfold f_sar_backprojection_pulse_contrib' , f_sar_backprojection_pulse_contrib_i' , f_sar_backprojection_pulse_contrib_r' .
  destruct f_sar_backprojection_pulse_contrib_exists as (x, ?).
  destruct x as [ [ ? ? ] ? ].
  assumption.
Qed.

Definition f_sar_backprojection_pulse_contrib := Eval cbn in f_sar_backprojection_pulse_contrib'.

Definition f_sar_backprojection_pulse_contrib_r := Eval cbn in f_sar_backprojection_pulse_contrib_r' .

Definition f_sar_backprojection_pulse_contrib_i := Eval cbn in f_sar_backprojection_pulse_contrib_i' .

Lemma f_sar_backprojection_pulse_contrib_eq :
  stmt_assoc f_sar_backprojection_loop_p_body (Ssequence f_sar_backprojection_pulse_contrib (Ssequence (Sset _contrib_r f_sar_backprojection_pulse_contrib_r) (Sset _contrib_i f_sar_backprojection_pulse_contrib_i ))) .
Proof.
  exact f_sar_backprojection_pulse_contrib_eq' .
Qed.

Lemma f_sar_backprojection_norm_exists_1:
  {s1tyargss2 |
   let '(s1, ty, args, s2) := s1tyargss2 in
   stmt_assoc f_sar_backprojection_pulse_contrib
              (Ssequence s1 (Ssequence (Scall None (Evar _norm ty) args) s2)) }.
Proof.
  eexists (_, _, _, _).
  destruct (rememb_gen stmt_assoc f_sar_backprojection_pulse_contrib) as (u & uL & uR).
  setoid_rewrite uL.
  clear uL.
  unfold f_sar_backprojection_pulse_contrib in uR.
  repeat setoid_rewrite stmt_assoc_r2l in uR.
  let rec t :=
      (
        eassumption
          ||
          (
            apply stmt_assoc_l2r_head in uR;
            t
          )
      )
  in
  t.
Defined.

Definition f_sar_backprojection_norm_pre'_1 :=
  let (s, _) := f_sar_backprojection_norm_exists_1 in 
  let '(s1, _, _, _) := s in
  s1.

Definition f_sar_backprojection_norm_post' :=
  let (s, _) := f_sar_backprojection_norm_exists_1 in 
  let '(_, _, _, s2) := s in
  s2.

Definition f_sar_backprojection_norm_post := Eval cbn in f_sar_backprojection_norm_post'.

Definition f_sar_backprojection_norm_ty' :=
  let (s, _) := f_sar_backprojection_norm_exists_1 in 
  let '(_, s1, _, _) := s in
  s1.

Definition f_sar_backprojection_norm_ty := Eval cbn in f_sar_backprojection_norm_ty'.

Definition f_sar_backprojection_norm_args' :=
  let (s, _) := f_sar_backprojection_norm_exists_1 in 
  let '(_, _, args, _) := s in
  args.

Definition f_sar_backprojection_norm_args := Eval cbn in f_sar_backprojection_norm_args'.

Lemma f_sar_backprojection_norm_eq_1 :
   stmt_assoc f_sar_backprojection_pulse_contrib
              (Ssequence f_sar_backprojection_norm_pre'_1 (Ssequence (Scall None (Evar _norm f_sar_backprojection_norm_ty') f_sar_backprojection_norm_args') f_sar_backprojection_norm_post')).
Proof.
  unfold f_sar_backprojection_norm_pre'_1.
  unfold f_sar_backprojection_norm_post'.
  unfold f_sar_backprojection_norm_ty'.
  unfold f_sar_backprojection_norm_args'.
  destruct f_sar_backprojection_norm_exists_1 as [[[[? ?] ?] ?] ?].
  assumption.
Qed.

Lemma f_sar_backprojection_norm_pre_exists_2:
    {s1 |
     stmt_assoc f_sar_backprojection_norm_pre'_1 s1}.
Proof.
  esplit.
  cbn.
  repeat rewrite stmt_assoc_l2r.
  reflexivity.
Defined.

Definition f_sar_backprojection_norm_pre' :=
  let (s1, _) := f_sar_backprojection_norm_pre_exists_2 in s1.

Definition f_sar_backprojection_norm_pre := Eval cbn in f_sar_backprojection_norm_pre'.

Lemma f_sar_backprojection_norm_pre_eq:
     stmt_assoc f_sar_backprojection_norm_pre'_1 f_sar_backprojection_norm_pre' .
Proof.
  unfold f_sar_backprojection_norm_pre'.
  destruct f_sar_backprojection_norm_pre_exists_2.
  assumption.
Qed.

Lemma f_sar_backprojection_norm_eq_2:
   stmt_assoc f_sar_backprojection_pulse_contrib
              (Ssequence f_sar_backprojection_norm_pre' (Ssequence (Scall None (Evar _norm f_sar_backprojection_norm_ty') f_sar_backprojection_norm_args') f_sar_backprojection_norm_post')).
Proof.
  setoid_rewrite <- f_sar_backprojection_norm_pre_eq.
  apply f_sar_backprojection_norm_eq_1.
Qed.

Lemma f_sar_backprojection_norm_eq:
   stmt_assoc f_sar_backprojection_pulse_contrib
              (Ssequence f_sar_backprojection_norm_pre (Ssequence (Scall None (Evar _norm f_sar_backprojection_norm_ty) f_sar_backprojection_norm_args) f_sar_backprojection_norm_post)).
Proof f_sar_backprojection_norm_eq_2.

Lemma f_sar_backprojection_bin_sample_exists:
  {s1tyargss2 |
   let '(s1, ty, args, s2) := s1tyargss2 in
   stmt_assoc f_sar_backprojection_norm_post
              (Ssequence s1 (Ssequence (Scall None (Evar _bin_sample ty) args) s2)) }.
Proof.
  eexists (_, _, _, _).
  destruct (rememb_gen stmt_assoc f_sar_backprojection_norm_post) as (u & uL & uR).
  setoid_rewrite uL.
  reflexivity.
Defined.

Definition f_sar_backprojection_bin_sample_pre' :=
  let (s, _) := f_sar_backprojection_bin_sample_exists in 
  let '(s1, _, _, _) := s in
  s1.

Definition f_sar_backprojection_bin_sample_pre := Eval cbn in f_sar_backprojection_bin_sample_pre'.

Lemma f_sar_backprojection_bin_sample_pre'_eq:
  f_sar_backprojection_bin_sample_pre' = f_sar_backprojection_bin_sample_pre.
Proof.
  reflexivity.
Qed.

Definition f_sar_backprojection_bin_sample_post' :=
  let (s, _) := f_sar_backprojection_bin_sample_exists in 
  let '(_, _, _, s2) := s in
  s2.

Definition f_sar_backprojection_bin_sample_post := Eval cbn in f_sar_backprojection_bin_sample_post'.

Lemma f_sar_backprojection_bin_sample_post'_eq:
  f_sar_backprojection_bin_sample_post' = f_sar_backprojection_bin_sample_post.
Proof.
  reflexivity.
Qed.

Definition f_sar_backprojection_bin_sample_ty' :=
  let (s, _) := f_sar_backprojection_bin_sample_exists in 
  let '(_, s1, _, _) := s in
  s1.

Definition f_sar_backprojection_bin_sample_ty := Eval cbn in f_sar_backprojection_bin_sample_ty'.

Lemma f_sar_backprojection_bin_sample_ty'_eq:
  f_sar_backprojection_bin_sample_ty' = f_sar_backprojection_bin_sample_ty.
Proof.
  reflexivity.
Qed.

Definition f_sar_backprojection_bin_sample_args' :=
  let (s, _) := f_sar_backprojection_bin_sample_exists in 
  let '(_, _, args, _) := s in
  args.

Definition f_sar_backprojection_bin_sample_args := Eval cbn in f_sar_backprojection_bin_sample_args'.

Lemma f_sar_backprojection_bin_sample_args'_eq:
  f_sar_backprojection_bin_sample_args' = f_sar_backprojection_bin_sample_args.
Proof.
  reflexivity.
Qed.

Lemma f_sar_backprojection_bin_sample_eq:
   stmt_assoc f_sar_backprojection_norm_post
              (Ssequence f_sar_backprojection_bin_sample_pre (Ssequence (Scall None (Evar _bin_sample f_sar_backprojection_bin_sample_ty) f_sar_backprojection_bin_sample_args) f_sar_backprojection_bin_sample_post)).
Proof.
  rewrite <- f_sar_backprojection_bin_sample_pre'_eq.
  rewrite <- f_sar_backprojection_bin_sample_post'_eq.
  rewrite <- f_sar_backprojection_bin_sample_ty'_eq.
  rewrite <- f_sar_backprojection_bin_sample_args'_eq.
  unfold f_sar_backprojection_bin_sample_pre'.
  unfold f_sar_backprojection_bin_sample_post'.
  unfold f_sar_backprojection_bin_sample_ty'.
  unfold f_sar_backprojection_bin_sample_args'.
  destruct f_sar_backprojection_bin_sample_exists as [[[[? ?] ?] ?] ?].
  assumption.
Qed.

Lemma f_sar_backprojection_sin_cos_exists:
  {s1tyargss2 |
   let '(ty, args, s2) := s1tyargss2 in
   stmt_assoc f_sar_backprojection_bin_sample_post
              (Ssequence (Scall None (Evar _sin_cos ty) args) s2) }.
Proof.
  eexists (_, _, _).
  destruct (rememb_gen stmt_assoc f_sar_backprojection_bin_sample_post) as (u & uL & uR).
  setoid_rewrite uL.
  reflexivity.
Defined.

Definition f_sar_backprojection_sin_cos_post' :=
  let (s, _) := f_sar_backprojection_sin_cos_exists in 
  let '(_, _, s2) := s in
  s2.

Definition f_sar_backprojection_sin_cos_post := Eval cbn in f_sar_backprojection_sin_cos_post'.

Lemma f_sar_backprojection_sin_cos_post'_eq:
  f_sar_backprojection_sin_cos_post' = f_sar_backprojection_sin_cos_post.
Proof.
  reflexivity.
Qed.

Definition f_sar_backprojection_sin_cos_ty' :=
  let (s, _) := f_sar_backprojection_sin_cos_exists in 
  let '(s1, _, _) := s in
  s1.

Definition f_sar_backprojection_sin_cos_ty := Eval cbn in f_sar_backprojection_sin_cos_ty'.

Lemma f_sar_backprojection_sin_cos_ty'_eq:
  f_sar_backprojection_sin_cos_ty' = f_sar_backprojection_sin_cos_ty.
Proof.
  reflexivity.
Qed.

Definition f_sar_backprojection_sin_cos_args' :=
  let (s, _) := f_sar_backprojection_sin_cos_exists in 
  let '(_, args, _) := s in
  args.

Definition f_sar_backprojection_sin_cos_args := Eval cbn in f_sar_backprojection_sin_cos_args'.

Lemma f_sar_backprojection_sin_cos_args'_eq:
  f_sar_backprojection_sin_cos_args' = f_sar_backprojection_sin_cos_args.
Proof.
  reflexivity.
Qed.

Lemma f_sar_backprojection_sin_cos_eq:
   stmt_assoc f_sar_backprojection_bin_sample_post
              (Ssequence (Scall None (Evar _sin_cos f_sar_backprojection_sin_cos_ty) f_sar_backprojection_sin_cos_args) f_sar_backprojection_sin_cos_post).
Proof.
  rewrite <- f_sar_backprojection_sin_cos_post'_eq.
  rewrite <- f_sar_backprojection_sin_cos_ty'_eq.
  rewrite <- f_sar_backprojection_sin_cos_args'_eq.
  unfold f_sar_backprojection_sin_cos_post'.
  unfold f_sar_backprojection_sin_cos_ty'.
  unfold f_sar_backprojection_sin_cos_args'.
  destruct f_sar_backprojection_sin_cos_exists as [[[? ?] ?] ?].
  assumption.
Qed.
