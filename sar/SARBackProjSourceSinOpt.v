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

Verification of C implementation of sine.
*)

Require Import Flocq.Appli.Fappli_IEEE.
Require Import Integers.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Clight.
Require Import FPLang.
Require Import FPLangOpt.
Require Import ClightFacts.
Require Import Clight2FPOpt.
Require Import SARBackProjSource.
Require Import SARBackProjSourceSin.

Require Import RAux.
Require Import FieldEq.
Open Scope R_scope.

Transparent Integers.Int.repr.
Transparent Floats.Float32.of_bits.
Transparent Floats.Float.of_bits.
Set Printing Depth 1000000. 

Local Existing Instances
      Clight2FP.nans
      map_nat compcert_map
.

Require Import Interval.Interval_tactic.
Require Import ClightSep2.

Open Scope R_scope.

Definition f_sin_cos_correct f_sin_error f_cos_error ge cef_sin_cos :=
  type_of_fundef cef_sin_cos =
  Ctypes.Tfunction (Ctypes.Tcons (Clightdefs.tptr Clightdefs.tfloat)
                                 (Ctypes.Tcons (Clightdefs.tptr Clightdefs.tfloat)
                                               (Ctypes.Tcons Clightdefs.tdouble Ctypes.Tnil)))
                   Clightdefs.tvoid
                   cc_default
  /\
  forall
    os
    (Hos_align: (align_chunk Mfloat32 | Int.unsigned os)%Z )
    oc
    (Hoc_align: (align_chunk Mfloat32 | Int.unsigned oc)%Z )
    ps (Hps: perm_order ps Writable)
    pc (Hpc: perm_order pc Writable)
    bs bc
    m P
    (Hm:
       holds
         (P ++
            Pperm bs (Int.unsigned os) ps (size_chunk_nat Mfloat32)
            ++
            Pperm bc (Int.unsigned oc) pc (size_chunk_nat Mfloat32))
         m)
    x
    (Hx_finite: is_finite _ _ x = true)
    (Hx_range: x_left <= B2R _ _ x <= x_right )
  ,
    let st0 := (Callstate cef_sin_cos
                          (Vptr bs os :: Vptr bc oc :: Vfloat x :: nil)
                          Kstop
                          m) in
    exists m',
      star Clight.step2 ge
           st0
           E0
           (Returnstate Vundef Kstop m')
      /\
      exists si co,
        holds
          (P ++
             Pval Mfloat32 bs (Int.unsigned os) ps (Vsingle si)
             ++
             Pval Mfloat32 bc (Int.unsigned oc) pc (Vsingle co))
          m'
        /\
        (
          is_finite _ _ si = true
          /\
          is_finite _ _ co = true
        )
        /\
        (
          Rabs (B2R _ _ si - sin (B2R _ _ x)) <= f_sin_error
          /\
          Rabs (B2R _ _ co - cos (B2R _ _ x)) <= f_cos_error
        )
.

Lemma round_to_error u v d e:
  v = u * (1 + d) + e ->
  v - u = u * d + e.
Proof.
  intros H.
  subst.
  ring.
Qed.
  
Lemma f_sin_cos_body_correct' :
  { f_sin_error : _ &
                        { f_cos_error |
                          forall
 (ge: Clight.genv)
      b_sin fn_sin
      (Hb_sin: Globalenvs.Genv.find_symbol ge _sin = Some b_sin)
      (Hfn_sin: Globalenvs.Genv.find_funct_ptr ge b_sin = Some fn_sin)
      (Hfn_sin_correct: SARBackProjSourceSin.f_unary_correct sin ge fn_sin)
      b_cos fn_cos
      (Hb_cos: Globalenvs.Genv.find_symbol ge _cos = Some b_cos)
      (Hfn_cos: Globalenvs.Genv.find_funct_ptr ge b_cos = Some fn_cos)
      (Hfn_cos_correct: SARBackProjSourceSin.f_unary_correct cos ge fn_cos)
,
  f_sin_cos_correct f_sin_error f_cos_error ge (Clight.Internal (f_sin_cos))
}}.
Proof.
  esplit. esplit.

  split; auto.
  intros os Hos_align oc Hoc_align ps Hps pc Hpc bs bc m P Hm x Hx_finite Hx_range st0.
  unfold x_left, x_right in Hx_range.
  unfold st0.
  clear st0.

  apply f_sin_correct in Hfn_sin_correct.
  destruct Hfn_sin_correct as (sin_type & Hfn_sin_correct).
  apply f_cos_correct in Hfn_cos_correct.
  destruct Hfn_cos_correct as (cos_type & Hfn_cos_correct).

  unfold f_unary_error in Hfn_sin_correct, Hfn_cos_correct.

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
    intro H;  break H; subst; eauto 13.
  }
  apply star_exists_step.
  call_fn.
  simpl fn_body.

  repeat run.

  apply exec_call_exists.
  solve_trivial.
  eapply exists_modus_ponens.
  {
    eapply exists_double_elim.
    eapply Hfn_sin_correct; eauto.
  }
  intros s1 Hs1.
  simpl in Hs1.
  destruct Hs1 as (si & ? & Hsi_finite & Hsi_val & Hsi_range).
  subst s1.
  solve_trivial.
  repeat run.

  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  (* here comes the framework into play! *)
  C_to_float_as sif Hsif.
  compute_fval_as Hsif Hsif_finite Hsif_val.
  solve_trivial.

  repeat run.

  holds_storev_solve.
  intros m Hm.
  repeat run.

  apply exec_call_exists.
  solve_trivial.
  eapply exists_modus_ponens.
  {
    eapply exists_double_elim.
    eapply Hfn_cos_correct; eauto.
  }
  intros s1 Hs1.
  simpl in Hs1.
  destruct Hs1 as (co & ? & Hco_finite & Hco_val & Hco_range).
  subst s1.
  solve_trivial.
  repeat run.

  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  (* here comes the framework into play! *)
  C_to_float_as cof Hcof.
  compute_fval_as Hcof Hcof_finite Hcof_val.
  solve_trivial.

  repeat run.

  holds_storev_solve.
  intros m Hm.
  repeat run.

  apply star_exists_refl.
  solve_trivial.

  exists sif, cof.
  split.
  {
    revert Hm.
    apply holds_list_comm_aux.
    apply count_occ_list_comm.
    intros; repeat rewrite count_occ_app; omega.
  }

  split; auto.

  split.
  {
    symmetry in Hsif_val.
    rewrite Rmult_1_l in *.
    apply round_to_error in Hsif_val.
    match type of Hsif_val with
        _ = ?z =>
        interval_intro (Rabs z) upper with (i_prec 128) as Hsif_error
    end.
    rewrite <- Hsif_val in Hsif_error.
    eapply Rabs_triang2.
    {
      eassumption.
    }
    eassumption.
  }
  symmetry in Hcof_val.
  rewrite Rmult_1_l in *.
  apply round_to_error in Hcof_val.
  match type of Hcof_val with
      _ = ?z =>
      interval_intro (Rabs z) upper with (i_prec 128) as Hcof_error
  end.
  rewrite <- Hcof_val in Hcof_error.
  eapply Rabs_triang2.
  {
    eassumption.
  }
  eassumption.
Defined.

Definition f_sin_error' :=
  let (x, _) := f_sin_cos_body_correct' in x.

Definition f_sin_error'_eq :=
  $( field_eq f_sin_error' )$ .

Definition f_sin_error :=
  $(
      match type of f_sin_error'_eq with
        _ = ?z => exact z
      end
    )$ .

Definition f_cos_error' :=
  let (_, y) := f_sin_cos_body_correct' in
  let (x, _) := y in x.

Definition f_cos_error'_eq :=
  $( field_eq f_cos_error' )$ .

Definition f_cos_error :=
  $(
      match type of f_cos_error'_eq with
        _ = ?z => exact z
      end
    )$ .

Lemma f_sin_cos_error_correct:
                          forall
 (ge: Clight.genv)
      b_sin fn_sin
      (Hb_sin: Globalenvs.Genv.find_symbol ge _sin = Some b_sin)
      (Hfn_sin: Globalenvs.Genv.find_funct_ptr ge b_sin = Some fn_sin)
      (Hfn_sin_correct: SARBackProjSourceSin.f_unary_correct sin ge fn_sin)
      b_cos fn_cos
      (Hb_cos: Globalenvs.Genv.find_symbol ge _cos = Some b_cos)
      (Hfn_cos: Globalenvs.Genv.find_funct_ptr ge b_cos = Some fn_cos)
      (Hfn_cos_correct: SARBackProjSourceSin.f_unary_correct cos ge fn_cos)
,
  f_sin_cos_correct f_sin_error f_cos_error ge (Clight.Internal (f_sin_cos))
.
Proof.
  unfold f_sin_error.
  rewrite <- f_sin_error'_eq.
  unfold f_cos_error.
  rewrite <- f_cos_error'_eq.
  unfold f_sin_error', f_cos_error'.
  destruct f_sin_cos_body_correct'.
  destruct s.
  assumption.
Qed.
