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

Verification of SAR backprojection: everything before the computation
of the norm.
*)

Require Export SARBackProjSourceDecomp.
Require Export SARBackProjSourceSpec.
Require Export RAux.
Require Export FieldEq.
Require Export FPLang Clight2FP FPLangOpt Clight2FPOpt.
Open Scope R_scope.
Import List.
Open Scope list_scope.

Require SARBackProj.
Require ClightSep2.

Definition f_sar_backprojection_loop_y_pre_correct BOUNDS :=
  let '(dR_inv_error, dR_inv_left, dR_inv_right) := BOUNDS in
  forall 
    `(HYPS: SARHypotheses)
    (ge : genv)
    (b_norm : block)
    (f_norm : fundef)
    (Hb_norm : Globalenvs.Genv.find_symbol ge _norm = Some b_norm)
    (Hf_norm : Globalenvs.Genv.find_funct_ptr ge b_norm = Some f_norm)
    (b3 b4 b5 b6 b7 b8 : block)
    (m : Mem.mem')
    (Hm : holds
         (((((((P ++
                   Parray_opt Mfloat32 0 (fun _ : Z => None) bir
                     (Int.unsigned oir) pir
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)) ++
                   Parray_opt Mfloat32 0 (fun _ : Z => None) bii
                     (Int.unsigned oii) pii
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
               Pperm b3 0 Freeable (size_chunk_nat Mfloat32)) ++
              Pperm b4 0 Freeable (size_chunk_nat Mfloat32)) ++
             Pperm b5 0 Freeable (size_chunk_nat Mfloat32)) ++
            Pperm b6 0 Freeable (size_chunk_nat Mfloat32)) ++
           Pperm b7 0 Freeable (size_chunk_nat Mfloat64)) ++
          Pperm b8 0 Freeable (size_chunk_nat Mfloat64)) m)
  ,
    let le :=
       (Maps.PTree.set _z0 (Vptr bz0 oz0)
          (Maps.PTree.set _dxdy (Vptr bdxdy odxdy)
             (Maps.PTree.set _dR (Vptr bdR odR)
                (Maps.PTree.set _R0 (Vptr br0 or0)
                   (Maps.PTree.set _ku (Vptr bku oku)
                      (Maps.PTree.set _platpos_z (Vptr bpz opz)
                         (Maps.PTree.set _platpos_y 
                            (Vptr bpy opy)
                            (Maps.PTree.set _platpos_x 
                               (Vptr bpx opx)
                               (Maps.PTree.set _data_i 
                                  (Vptr bdi odi)
                                  (Maps.PTree.set _data_r 
                                     (Vptr bdr odr)
                                     (Maps.PTree.set _image_i 
                                        (Vptr bii oii)
                                        (Maps.PTree.set _image_r
                                           (Vptr bir oir)
                                           (create_undef_temps
                                              (fn_temps
                                                 (f_sar_backprojection2
                                                  N_RANGE_UPSAMPLED
                                                  (Z.of_nat BP_NPIX_X)
                                                  (Z.of_nat BP_NPIX_Y)
                                                  (Z.of_nat N_PULSES))))))))))))))))
    in
   exists (le1 : temp_env) (m1 : mem) (out1 : outcome),
     exec_stmt ge
       (Maps.PTree.set _bin (b8, tdouble)
          (Maps.PTree.set _R (b7, tdouble)
             (Maps.PTree.set _matched_filter_i (b6, tfloat)
                (Maps.PTree.set _matched_filter_r (b5, tfloat)
                   (Maps.PTree.set _sample_i (b4, tfloat)
                      (Maps.PTree.set _sample_r (b3, tfloat)
                          empty_env))))))
       le
       m f_sar_backprojection_loop_y_pre E0 le1 m1 out1 /\
     m1 = m /\
     out1 = Out_normal /\
     exists ku2 dxdy2 dR_inv,
       le1 = 
       Maps.PTree.set _iy (Vint (Int.repr 0))
                      (Maps.PTree.set _ku_2 (Vfloat ku2)
                                      (Maps.PTree.set _dxdy_2 (Vfloat dxdy2)
                                                      (Maps.PTree.set _dR_inv (Vfloat dR_inv)
                                                                      le))) /\
       is_finite _ _ ku2 = true /\
       B2R _ _ ku2 = 2 * B2R _ _ ku0 /\
       is_finite _ _ dxdy2 = true /\
       B2R _ _ dxdy2 = /2 * B2R _ _ dxdy0 /\
       is_finite _ _ dR_inv = true /\
       (Rabs (B2R _ _ dR_inv - / B2R _ _ dR0) <= dR_inv_error) /\
       (dR_inv_left <= B2R _ _ dR_inv <= dR_inv_right)
.

Lemma f_sar_backprojection_loop_y_pre_body_correct' : { BOUNDS |
  f_sar_backprojection_loop_y_pre_correct BOUNDS }.
Proof.
  eexists (_, _, _).
  unfold f_sar_backprojection_loop_y_pre_correct.
  intros data_r data_i P bdr odr  bdi odi bpx opx platpos_x bpy opy.
  intros platpos_y bpz opz platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0.
  intros r0 bz0 oz0 z0 bir oir pir bii oii pii HYPS ge b_norm f_norm Hb_norm Hf_norm.
  intros b3 b4 b5 b6 b7 b8 m Hm.
  unfold f_sar_backprojection_loop_y_pre.

  inversion HYPS.

  apply exec_Sseq_exists.
  unfold out_normal_b.
  apply exec_Sset_exists.

  apply deepest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  repeat ClightSep2.run.

  assert (holds P m) as HP
  by let rec t :=
        match constr:tt with
          | _ => assumption
          | _ => (apply holds_weak_left in Hm; t)
          | _ => (apply holds_weak_right in Hm; t)
        end
    in t.

  rewrite HdR by assumption.
  solve_trivial.

  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  (* here comes the framework into play! *)
  C_to_float_as dR_inv HdR_inv.
  unfold SARBounds.dR in HdR_val.
  Transparent Float.of_bits Int64.repr.
  let t _ :=
      rewrite HdR_val;
      interval_
  in
  compute_fval_as' t HdR_inv HdR_inv_finite HdR_inv_val.
  rewrite HdR_val in HdR_inv_val.

  Require Import Interval.Interval_tactic.
  match type of HdR_inv_val with
      ?u = _ =>
      interval_intro u with (i_prec 256) as HdR_inv_range;
        rewrite HdR_inv_val in HdR_inv_range
  end.
  generalize (f_equal (fun x => x - / B2R _ _ dR0) HdR_inv_val). intro HdR_inv_val' .
  rewrite HdR_val in HdR_inv_val' at 1.
  match type of HdR_inv_val' with
      ?u = _ =>
      interval_intro (Rabs u) upper with (i_prec 256) as HdR_inv_error;
        rewrite HdR_inv_val' in HdR_inv_error
  end.
  clear HdR_inv_val'.

  apply exec_Sseq_exists.
  unfold out_normal_b.
  apply exec_Sset_exists.

  apply deepest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  repeat ClightSep2.run.

  rewrite Hdxdy by assumption.
  solve_trivial.

  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  (* here comes the framework into play! *)
  C_to_float_as dxdy2 Hdxdy2.
  unfold SARBounds.dxdy in Hdxdy_val.
  Transparent Float.of_bits Int64.repr.
  let t _ :=
      rewrite Hdxdy_val;
      interval_
  in
  compute_fval_as' t Hdxdy2 Hdxdy2_finite Hdxdy2_val.

  assert (B2R _ _ dxdy2 = / 2 * B2R _ _ dxdy0) as Hdxdy2 by (rewrite <- Hdxdy2_val; field).

  apply exec_Sseq_exists.
  unfold out_normal_b.
  apply exec_Sset_exists.

  apply deepest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  repeat ClightSep2.run.

  rewrite Hku by assumption.
  solve_trivial.

  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  (* here comes the framework into play! *)
  C_to_float_as ku2 Hku2.
  unfold SARBounds.ku in Hku_val.
  Transparent Float.of_bits Int64.repr.
  let t _ :=
      rewrite Hku_val;
      interval_
  in
  compute_fval_as' t Hku2 Hku2_finite Hku2_val.

  assert (B2R _ _ ku2 = 2 * B2R _ _ ku0) as Hku2 by (rewrite <- Hku2_val; field).

  apply exec_Sset_exists.
  apply eval_exists_Econst_int.

  solve_trivial.
  eassumption.
Defined.

Definition dR_inv_error' :=
  let (x, _) := f_sar_backprojection_loop_y_pre_body_correct' in 
  let '(y, _, _) := x in y
.

Definition dR_inv_error'_eq := $( field_eq dR_inv_error' )$ .

Definition dR_inv_error := $( match type of dR_inv_error'_eq with _ = ?z => exact z end )$ .

Definition dR_inv_left' :=
  let (x, _) := f_sar_backprojection_loop_y_pre_body_correct' in 
  let '(_, y, _) := x in y
.

Definition dR_inv_left'_eq := $( field_eq dR_inv_left' )$ .

Definition dR_inv_left := $( match type of dR_inv_left'_eq with _ = ?z => exact z end )$ .

Definition dR_inv_right' :=
  let (x, _) := f_sar_backprojection_loop_y_pre_body_correct' in 
  let '(_, _, y) := x in y
.

Definition dR_inv_right'_eq := $( field_eq dR_inv_right' )$ .

Definition dR_inv_right := $( match type of dR_inv_right'_eq with _ = ?z => exact z end )$ .

Lemma f_sar_backprojection_loop_y_pre_body_correct:
  f_sar_backprojection_loop_y_pre_correct (dR_inv_error, dR_inv_left, dR_inv_right).
Proof.
  unfold dR_inv_error. rewrite <- dR_inv_error'_eq.
  unfold dR_inv_left. rewrite <- dR_inv_left'_eq.
  unfold dR_inv_right. rewrite <- dR_inv_right'_eq.
  unfold dR_inv_error', dR_inv_left', dR_inv_right'.
  destruct f_sar_backprojection_loop_y_pre_body_correct'.
  destruct x.
  destruct p.
  assumption.
Qed.

Require Import SepLogicVars.

Definition f_sar_backprojection_loop_x_pre_correct BOUNDS :=
  let '(py_error, py_left, py_right) := BOUNDS in
  forall
    `(HYPS: SARHypotheses)
    (ku2 dxdy2 dR_inv : float)
    (Hku2_val : B2R 53 1024 ku2 = 2 * B2R 53 1024 ku0)
    (Hdxdy2_val : B2R 53 1024 dxdy2 = / 2 * B2R 53 1024 dxdy0)
    (HdR_inv_error : Rabs (B2R 53 1024 dR_inv - / B2R 53 1024 dR0) <=
                  dR_inv_error)
    (HdR_inv_range : dR_inv_left <= B2R 53 1024 dR_inv <= dR_inv_right)
    (Hku2_finite : is_finite 53 1024 ku2 = true)
    (Hdxdy2_finite : is_finite 53 1024 dxdy2 = true)
    (HdR_inv_finite : is_finite 53 1024 dR_inv = true)
    (b3 b4 b5 b6 b7 b8 : block)
    (m : mem)
    (y : int)
    (image_r image_i : Z -> option (SepLogic.type_of_chunk Mfloat32))
    (Hm : holds
            (((((((P ++
                   Parray_opt Mfloat32 0 image_r bir 
                     (Int.unsigned oir) pir
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)) ++
                   Parray_opt Mfloat32 0 image_i bii 
                     (Int.unsigned oii) pii
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
               Pperm b3 0 Freeable (size_chunk_nat Mfloat32)) ++
              Pperm b4 0 Freeable (size_chunk_nat Mfloat32)) ++
             Pperm b5 0 Freeable (size_chunk_nat Mfloat32)) ++
            Pperm b6 0 Freeable (size_chunk_nat Mfloat32)) ++
           Pperm b7 0 Freeable (size_chunk_nat Mfloat64)) ++
          Pperm b8 0 Freeable (size_chunk_nat Mfloat64)) m)
  (Hy_int_range : (0 <= Int.signed y <= Z.of_nat BP_NPIX_Y - 1)%Z )
  (le0 : Maps.PTree.t val)
  (Hle0: env_le
     (create_map
        ((_iy, Vint y)
         :: ((((((((((((((((_iy, Vint (Int.repr 0)) :: Datatypes.nil) ++
                          (_ku_2, Vfloat ku2) :: Datatypes.nil) ++
                         (_dxdy_2, Vfloat dxdy2) :: Datatypes.nil) ++
                        (_dR_inv, Vfloat dR_inv) :: Datatypes.nil) ++
                       (_z0, Vptr bz0 oz0) :: Datatypes.nil) ++
                      (_dxdy, Vptr bdxdy odxdy) :: Datatypes.nil) ++
                     (_dR, Vptr bdR odR) :: Datatypes.nil) ++
                    (_R0, Vptr br0 or0) :: Datatypes.nil) ++
                   (_ku, Vptr bku oku) :: Datatypes.nil) ++
                  (_platpos_z, Vptr bpz opz) :: Datatypes.nil) ++
                 (_platpos_y, Vptr bpy opy) :: Datatypes.nil) ++
                (_platpos_x, Vptr bpx opx) :: Datatypes.nil) ++
               (_data_i, Vptr bdi odi) :: Datatypes.nil) ++
              (_data_r, Vptr bdr odr) :: Datatypes.nil) ++
             (_image_i, Vptr bii oii) :: Datatypes.nil) ++
            (_image_r, Vptr bir oir) :: Datatypes.nil) 
        (Maps.PTree.empty val)) le0)
  ge,
   exists (le1 : temp_env) (m1 : mem) (out1 : outcome),
     exec_stmt ge
       (Maps.PTree.set _bin (b8, tdouble)
          (Maps.PTree.set _R (b7, tdouble)
             (Maps.PTree.set _matched_filter_i (b6, tfloat)
                (Maps.PTree.set _matched_filter_r (b5, tfloat)
                   (Maps.PTree.set _sample_i (b4, tfloat)
                      (Maps.PTree.set _sample_r (b3, tfloat)
                          empty_env))))))
       le0 m f_sar_backprojection_loop_x_pre E0 le1 m1 out1 /\
     forall le2,
       env_le le1 le2 ->
       m1 = m /\ out1 = Out_normal /\
       exists py,
       env_le
     (Maps.PTree.set _ix (Vint (Int.repr 0))
        (Maps.PTree.set _py (Vfloat py)
           (create_map
              ((_iy, Vint y)
               :: ((((((((((((((((_iy, Vint (Int.repr 0)) :: Datatypes.nil) ++
                                (_ku_2, Vfloat ku2) :: Datatypes.nil) ++
                               (_dxdy_2, Vfloat dxdy2) :: Datatypes.nil) ++
                              (_dR_inv, Vfloat dR_inv) :: Datatypes.nil) ++
                             (_z0, Vptr bz0 oz0) :: Datatypes.nil) ++
                            (_dxdy, Vptr bdxdy odxdy) :: Datatypes.nil) ++
                           (_dR, Vptr bdR odR) :: Datatypes.nil) ++
                          (_R0, Vptr br0 or0) :: Datatypes.nil) ++
                         (_ku, Vptr bku oku) :: Datatypes.nil) ++
                        (_platpos_z, Vptr bpz opz) :: Datatypes.nil) ++
                       (_platpos_y, Vptr bpy opy) :: Datatypes.nil) ++
                      (_platpos_x, Vptr bpx opx) :: Datatypes.nil) ++
                     (_data_i, Vptr bdi odi) :: Datatypes.nil) ++
                    (_data_r, Vptr bdr odr) :: Datatypes.nil) ++
                   (_image_i, Vptr bii oii) :: Datatypes.nil) ++
                  (_image_r, Vptr bir oir) :: Datatypes.nil)
              (Maps.PTree.empty val)))) le2
     /\
     is_finite 53 1024 py = true
     /\
     Rabs
       (B2R 53 1024 py -
        (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_Y - 1) +
         2 * Fcore_Raux.Z2R (Int.signed y)) * 
                 B2R 53 1024 dxdy2) <= py_error
     /\
     py_left <= 
     B2R 53 1024 py <=
     py_right.

Lemma f_sar_backprojection_loop_x_pre_body_correct' : { BOUNDS |
  f_sar_backprojection_loop_x_pre_correct BOUNDS }.
Proof.
  eexists (_, _, _).
  unfold f_sar_backprojection_loop_x_pre_correct.
  intros data_r data_i P bdr odr bdi odi bpx opx platpos_x bpy opy.
  intros platpos_y bpz opz platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0.
  intros r0 bz0 oz0 z0 bir oir pir bii oii pii HYPS ku2 dxdy2 dR_inv Hku2_val.
  intros Hdxdy2_val HdR_inv_error HdR_inv_range Hku2_finite Hdxdy2_finite.
  intros HdR_inv_finite b3 b4 b5 b6 b7 b8 m y image_r image_i Hm Hy_int_range.
  intros le0 Hle0 ge.
  inversion HYPS.
  revert le0 Hle0.

  unfold f_sar_backprojection_loop_x_pre.
  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sset_exists_lifted.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply eval_exists_Ebinop.
  apply eval_exists_Ebinop.
  apply eval_exists_Eunop.
  apply eval_exists_Econst_int.
  solve_trivial.
  apply eval_exists_Econst_int.
  solve_trivial.
  apply eval_exists_Ebinop.
  apply eval_exists_Econst_int.
  repeat ClightSep2.run.
  apply eval_exists_Ecast.
  repeat ClightSep2.run.
  match goal with
      |- exists v,
           eval_expr _ _ (Maps.PTree.set ?i (Vfloat ?f) _)
                     _
                     (Ebinop _ (Etempvar ?i _) _ _) v
           /\ _ =>
      destruct (rememb f) as (f_ & Hf_)
  end.
  rewrite <- Hf_.
  Transparent Int.neg Int.repr.
  cbn in Hf_.
  match type of Hf_ with
      _ = Float.of_int ?j =>
      destruct (rememb_gen Int.eqm (Int.signed j)) as (u & Hu_l & Hu_r)
  end.
  match type of Hu_r with
      Int.eqm _ (Int.signed ?v) =>
      eqm_signed v Hw
  end.
  generalize (Int.eqm_trans _ _ _ Hu_r Hw).
  clear Hu_r Hw.
  intros Hu_r.
  generalize (Int.eqm_trans _ _ _ Hu_l Hu_r).
  clear Hu_l Hu_r.
  intro Hu_l.
  destruct (Float_of_int_exists_strong _ _ _ Hf_ Hu_l) as (Hf_finite & Hf_val).
  {
    let t := eval vm_compute in Int.min_signed in
                                 replace (Int.min_signed) with t by reflexivity.
    let t := eval vm_compute in Int.max_signed in
                                 replace (Int.max_signed) with t by reflexivity.
    cbn in Hy_int_range.
    omega.
  }
  clear Hf_ u Hu_l.
  rewrite Fcore_Raux.Z2R_IZR in Hf_val.
  rewrite plus_IZR in Hf_val.
  rewrite mult_IZR in Hf_val.
  repeat rewrite <- Fcore_Raux.Z2R_IZR in Hf_val.
  simpl Fcore_Raux.Z2R in Hf_val.
  inversion Hy_int_range as (Hy_l & Hy_r).
  apply IZR_le in Hy_l.
  apply IZR_le in Hy_r.
  repeat rewrite <- Fcore_Raux.Z2R_IZR in Hy_l, Hy_r.
  simpl Fcore_Raux.Z2R in Hy_l, Hy_r.
  generalize (conj Hy_l Hy_r).
  clear Hy_l Hy_r. intro Hy_range.
  destruct (rememb (Fcore_Raux.Z2R (Int.signed y))) as (ry & Hry).
  rewrite <- Hry in Hf_val, Hy_range.
  match type of Hf_val with
      B2R _ _ f_ = ?z =>
      interval_intro z as Hf_range
  end.
  rewrite <- Hf_val in Hf_range.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  (* here comes the framework into play! *)
  C_to_float_as py Hpy.
  unfold dxdy in Hdxdy_val.
  rewrite Hdxdy_val in Hdxdy2_val.
  let t _ :=
      (try rewrite Hdxdy2_val);
        interval_
  in
  compute_fval_as' t Hpy Hpy_finite Hpy_val.
  assert (B2R _ _ f_ = -(Fcore_Raux.Z2R (Z.of_nat BP_NPIX_Y - 1)) + 2 * ry) as Hf_' by assumption.
  generalize Hpy_val. intro Hpy_val' .
  rewrite Hdxdy2_val in Hpy_val' .
  match type of Hpy_val' with
      ?z = _ =>
      interval_intro z with (i_prec 128) as Hpy_range
  end.
  rewrite Hpy_val' in Hpy_range.
  destruct (rememb (B2R _ _ py - B2R _ _ f_ * B2R _ _ dxdy2)) as (py_err & Hpy_err).
  generalize Hpy_err. intro Hpy_err' .
  rewrite <- Hpy_val' in Hpy_err'.
  rewrite Hdxdy2_val in Hpy_err'.
  field_simplify in Hpy_err'.
  replace (py_err / 1) with py_err in Hpy_err' by field.
  match type of Hpy_err' with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hpy_error
  end.
  rewrite <- Hpy_err' in Hpy_error.
  clear Hpy_err'.
  subst py_err.
  subst ry.
  rewrite Hf_' in Hpy_error.
  clear Hf_'.

  apply exec_Sset_exists_lifted.
  apply eval_exists_Econst_int.

  intros.
  solve_trivial.
  eassumption.
Defined.

Definition py_error' :=
  let (x, _) := f_sar_backprojection_loop_x_pre_body_correct' in 
  let '(y, _, _) := x in y
.

Definition py_error'_eq := $( field_eq py_error' )$ .

Definition py_error := $( match type of py_error'_eq with _ = ?z => exact z end )$ .

Definition py_left' :=
  let (x, _) := f_sar_backprojection_loop_x_pre_body_correct' in 
  let '(_, y, _) := x in y
.

Definition py_left'_eq := $( field_eq (py_left') )$ .

Definition py_left := $( match type of py_left'_eq with _ = ?z => exact z end )$ .

Definition py_right' :=
  let (x, _) := f_sar_backprojection_loop_x_pre_body_correct' in 
  let '(_, _, y) := x in y
.

Definition py_right'_eq := $( field_eq py_right' )$ .

Definition py_right := $( match type of py_right'_eq with _ = ?z => exact z end )$ .

Lemma f_sar_backprojection_loop_x_pre_body_correct:
  f_sar_backprojection_loop_x_pre_correct (py_error, py_left, py_right).
Proof.
  unfold py_error. rewrite <- py_error'_eq.
  unfold py_left. rewrite <- py_left'_eq.
  unfold py_right. rewrite <- py_right'_eq.
  unfold py_error', py_left', py_right'.
  destruct f_sar_backprojection_loop_x_pre_body_correct'.
  destruct x.
  destruct p.
  assumption.
Qed.

Definition f_sar_backprojection_loop_p_pre_correct BOUNDS :=
  let '(px_error, px_left, px_right) := BOUNDS in
  forall
    `(HYPS: SARHypotheses)
    (b3 b4 b5 b6 b7 b8 : block)
    (ku2 dxdy2 dR_inv : float)
    (Hku2_val : B2R 53 1024 ku2 = 2 * B2R 53 1024 ku0)
    (Hdxdy2_val : B2R 53 1024 dxdy2 = / 2 * B2R 53 1024 dxdy0)
    (HdR_inv_error : Rabs (B2R 53 1024 dR_inv - / B2R 53 1024 dR0) <=
                  dR_inv_error)
    (HdR_inv_range : dR_inv_left <= B2R 53 1024 dR_inv <= dR_inv_right)
    y
    (Hy_int_range : (0 <= Int.signed y <= Z.of_nat BP_NPIX_Y - 1)%Z )
    (py : float)
    (Hpy_error : Rabs
                (B2R 53 1024 py -
                 (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_Y - 1) +
                  2 * Fcore_Raux.Z2R (Int.signed y)) * 
                 B2R 53 1024 dxdy2) <= py_error)
    (Hpy_range : py_left <= B2R 53 1024 py <= py_right)
    (x : int)
    (Hx_int_range : (0 <= Int.signed x <= Z.of_nat BP_NPIX_X - 1)%Z)
    (Hku2_finite : is_finite 53 1024 ku2 = true)
    (Hdxdy2_finite : is_finite 53 1024 dxdy2 = true)
    (HdR_inv_finite : is_finite 53 1024 dR_inv = true)
    (Hpy_finite : is_finite 53 1024 py = true)
    (m : mem)
    (image_r image_i : Z -> option (SepLogic.type_of_chunk Mfloat32))
    (Hm : holds
         (((((((P ++
                   Parray_opt Mfloat32 0 image_r bir 
                     (Int.unsigned oir) pir
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)) ++
                   Parray_opt Mfloat32 0 image_i bii 
                     (Int.unsigned oii) pii
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
               Pperm b3 0 Freeable (size_chunk_nat Mfloat32)) ++
              Pperm b4 0 Freeable (size_chunk_nat Mfloat32)) ++
             Pperm b5 0 Freeable (size_chunk_nat Mfloat32)) ++
            Pperm b6 0 Freeable (size_chunk_nat Mfloat32)) ++
           Pperm b7 0 Freeable (size_chunk_nat Mfloat64)) ++
          Pperm b8 0 Freeable (size_chunk_nat Mfloat64)) m)
    (le0 : Maps.PTree.t val)
    (Hle0: env_le
     (create_map
        ((_ix, Vint x)
         :: (((_ix, Vint (Int.repr 0)) :: Datatypes.nil) ++
             (_py, Vfloat py) :: Datatypes.nil) ++
            (_iy, Vint y)
            :: ((((((((((((((((_iy, Vint (Int.repr 0)) :: Datatypes.nil) ++
                             (_ku_2, Vfloat ku2) :: Datatypes.nil) ++
                            (_dxdy_2, Vfloat dxdy2) :: Datatypes.nil) ++
                           (_dR_inv, Vfloat dR_inv) :: Datatypes.nil) ++
                          (_z0, Vptr bz0 oz0) :: Datatypes.nil) ++
                         (_dxdy, Vptr bdxdy odxdy) :: Datatypes.nil) ++
                        (_dR, Vptr bdR odR) :: Datatypes.nil) ++
                       (_R0, Vptr br0 or0) :: Datatypes.nil) ++
                      (_ku, Vptr bku oku) :: Datatypes.nil) ++
                     (_platpos_z, Vptr bpz opz) :: Datatypes.nil) ++
                    (_platpos_y, Vptr bpy opy) :: Datatypes.nil) ++
                   (_platpos_x, Vptr bpx opx) :: Datatypes.nil) ++
                  (_data_i, Vptr bdi odi) :: Datatypes.nil) ++
                 (_data_r, Vptr bdr odr) :: Datatypes.nil) ++
                (_image_i, Vptr bii oii) :: Datatypes.nil) ++
               (_image_r, Vptr bir oir) :: Datatypes.nil)
        (Maps.PTree.empty val)) le0)
    ge
  ,
   exists (le1 : temp_env) (m1 : mem) (out1 : outcome),
     exec_stmt ge
       (Maps.PTree.set _bin (b8, tdouble)
          (Maps.PTree.set _R (b7, tdouble)
             (Maps.PTree.set _matched_filter_i (b6, tfloat)
                (Maps.PTree.set _matched_filter_r (b5, tfloat)
                   (Maps.PTree.set _sample_i (b4, tfloat)
                      (Maps.PTree.set _sample_r (b3, tfloat)
                         empty_env))))))
       le0 m f_sar_backprojection_loop_p_pre E0 le1 m1 out1 /\
     (forall le1_ : Maps.PTree.t val,
      env_le le1 le1_ ->
      out1 = Out_normal /\
      exists px,
        env_le
     (Maps.PTree.set _p (Vint (Int.repr 0))
        (Maps.PTree.set _contrib_i (Vfloat (B754_zero 53 1024 false))
           (Maps.PTree.set _contrib_r (Vfloat (B754_zero 53 1024 false))
              (Maps.PTree.set _px (Vfloat px)
                 (create_map
                    ((_ix, Vint x)
                     :: (((_ix, Vint (Int.repr 0)) :: Datatypes.nil) ++
                         (_py, Vfloat py) :: Datatypes.nil) ++
                        (_iy, Vint y)
                        :: ((((((((((((((((_iy, Vint (Int.repr 0))
                                          :: Datatypes.nil) ++
                                         (_ku_2, Vfloat ku2) :: Datatypes.nil) ++
                                        (_dxdy_2, Vfloat dxdy2)
                                        :: Datatypes.nil) ++
                                       (_dR_inv, Vfloat dR_inv)
                                       :: Datatypes.nil) ++
                                      (_z0, Vptr bz0 oz0) :: Datatypes.nil) ++
                                     (_dxdy, Vptr bdxdy odxdy)
                                     :: Datatypes.nil) ++
                                    (_dR, Vptr bdR odR) :: Datatypes.nil) ++
                                   (_R0, Vptr br0 or0) :: Datatypes.nil) ++
                                  (_ku, Vptr bku oku) :: Datatypes.nil) ++
                                 (_platpos_z, Vptr bpz opz) :: Datatypes.nil) ++
                                (_platpos_y, Vptr bpy opy) :: Datatypes.nil) ++
                               (_platpos_x, Vptr bpx opx) :: Datatypes.nil) ++
                              (_data_i, Vptr bdi odi) :: Datatypes.nil) ++
                             (_data_r, Vptr bdr odr) :: Datatypes.nil) ++
                            (_image_i, Vptr bii oii) :: Datatypes.nil) ++
                           (_image_r, Vptr bir oir) :: Datatypes.nil)
                    (Maps.PTree.empty val)))))) le1_
   /\
   px_left <= 
   B2R 53 1024 px <=
   px_right
   /\
   Rabs
     (B2R 53 1024 px -
      (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_X - 1) +
       2 * Fcore_Raux.Z2R (Int.signed x)) * 
      B2R 53 1024 dxdy2) <= px_error
   /\
   is_finite 53 1024 px = true
   /\
   holds
         ((((((((Pperm b3 (Int.unsigned Int.zero) Freeable
                      (size_chunk_nat Mfloat32) ++
                    Pperm b4 (Int.unsigned Int.zero) Freeable
                      (size_chunk_nat Mfloat32)) ++
                   Pperm b5 (Int.unsigned Int.zero) Freeable
                     (size_chunk_nat Mfloat32)) ++
                  Pperm b6 (Int.unsigned Int.zero) Freeable
                    (size_chunk_nat Mfloat32)) ++
                 Pperm b7 (Int.unsigned Int.zero) Freeable
                   (size_chunk_nat Mfloat64)) ++
                Pperm b8 (Int.unsigned Int.zero) Freeable
                  (size_chunk_nat Mfloat64)) ++ P) ++
              Parray_opt Mfloat32 (Int.unsigned Int.zero) image_r bir
                (Int.unsigned oir) pir
                (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
             Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
               (Int.unsigned oii) pii
               (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) m1
).

Lemma f_sar_backprojection_loop_p_pre_body_correct' : { BOUNDS |
  f_sar_backprojection_loop_p_pre_correct BOUNDS } .
Proof.
  eexists (_, _, _).
  unfold f_sar_backprojection_loop_p_pre_correct.
  intros data_r data_i P  bdr odr bdi odi bpx opx platpos_x bpy opy.
  intros platpos_y bpz opz platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0.
  intros r0 bz0 oz0 z0 bir oir pir bii oii pii HYPS b3 b4 b5 b6 b7 b8 ku2.
  intros dxdy2 dR_inv Hku2_val Hdxdy2_val HdR_inv_error HdR_inv_range y Hy_int_range.
  intros py Hpy_error Hpy_range x Hx_int_range Hku2_finite Hdxdy2_finite.
  intros HdR_inv_finite Hpy_finite m image_r image_i Hm le0 Hle0 ge.
  inversion HYPS.
  revert le0 Hle0.

  generalize Hx_int_range. intro Hx_int_range' . cbn in Hx_int_range.

  unfold f_sar_backprojection_loop_p_pre.
  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sset_exists_lifted.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply eval_exists_Ebinop.
  apply eval_exists_Ebinop.
  apply eval_exists_Eunop.
  apply eval_exists_Econst_int.
  solve_trivial.
  apply eval_exists_Econst_int.
  solve_trivial.
  apply eval_exists_Ebinop.
  apply eval_exists_Econst_int.
  repeat ClightSep2.run.
  apply eval_exists_Ecast.
  repeat ClightSep2.run.
  match goal with
      |- exists v,
           eval_expr _ _ (Maps.PTree.set ?i (Vfloat ?f) _)
                     _
                     (Ebinop _ (Etempvar ?i _) _ _) v
           /\ _ =>
      destruct (rememb f) as (fx_ & Hfx_)
  end.
  rewrite <- Hfx_.
  cbn in Hfx_.
  match type of Hfx_ with
      _ = Float.of_int ?j =>
      destruct (rememb_gen Int.eqm (Int.signed j)) as (u & Hu_l & Hu_r)
  end.
  match type of Hu_r with
      Int.eqm _ (Int.signed ?v) =>
      eqm_signed v Hw
  end.
  generalize (Int.eqm_trans _ _ _ Hu_r Hw).
  clear Hu_r Hw.
  intros Hu_r.
  generalize (Int.eqm_trans _ _ _ Hu_l Hu_r).
  clear Hu_l Hu_r.
  intro Hu_l.
  destruct (Float_of_int_exists_strong _ _ _ Hfx_ Hu_l) as (Hfx_finite & Hfx_val).
  {
    let t := eval vm_compute in Int.min_signed in
                                 replace (Int.min_signed) with t by reflexivity.
    let t := eval vm_compute in Int.max_signed in
                                 replace (Int.max_signed) with t by reflexivity.
    omega.
  }
  clear Hfx_ u Hu_l.
  rewrite Fcore_Raux.Z2R_IZR in Hfx_val.
  rewrite plus_IZR in Hfx_val.
  rewrite mult_IZR in Hfx_val.
  repeat rewrite <- Fcore_Raux.Z2R_IZR in Hfx_val.
  simpl Fcore_Raux.Z2R in Hfx_val.
  inversion Hx_int_range as (Hx_l & Hx_r).
  apply IZR_le in Hx_l.
  apply IZR_le in Hx_r.
  repeat rewrite <- Fcore_Raux.Z2R_IZR in Hx_l, Hx_r.
  simpl Fcore_Raux.Z2R in Hx_l, Hx_r.
  generalize (conj Hx_l Hx_r).
  clear Hx_l Hx_r. intro Hx_range.
  destruct (rememb (Fcore_Raux.Z2R (Int.signed x))) as (rx & Hrx).
  rewrite <- Hrx in Hfx_val, Hx_range.
  match type of Hfx_val with
      B2R _ _ _ = ?z =>
      interval_intro z as Hf_range
  end.
  rewrite <- Hfx_val in Hf_range.

  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  (* here comes the framework into play! *)
  unfold dxdy in Hdxdy_val.
  rewrite Hdxdy_val in Hdxdy2_val.
  C_to_float_as px Hpx.
  let t _ :=
      (try rewrite Hdxdy2_val);
        interval_
  in
  compute_fval_as' t Hpx Hpx_finite Hpx_val.
  rewrite Hdxdy2_val in Hpx_val.

  assert (B2R _ _ fx_ = -(Fcore_Raux.Z2R (Z.of_nat BP_NPIX_X - 1)) + 2 * rx) as Hf_' by assumption.
  generalize Hpx_val. intro Hpx_val' .
  rewrite <- Hdxdy2_val in Hpx_val .
  match type of Hpx_val' with
      ?z = _ =>
      interval_intro z with (i_prec 128) as Hpx_range
  end.
  rewrite Hpx_val' in Hpx_range.
  destruct (rememb (B2R _ _ px - B2R _ _ fx_ * B2R _ _ dxdy2)) as (px_err & Hpx_err).
  generalize Hpx_err. intro Hpx_err' .
  rewrite <- Hpx_val' in Hpx_err'.
  rewrite Hdxdy2_val in Hpx_err'.
  field_simplify in Hpx_err'.
  replace (px_err / 1) with px_err in Hpx_err' by field.
  match type of Hpx_err' with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hpx_error
  end.
  rewrite <- Hpx_err' in Hpx_error.
  clear Hpx_err'.
  subst px_err.
  subst rx.
  rewrite Hf_' in Hpx_error.
  clear Hf_'.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sset_exists_lifted.
  eval_exists_Econst_float.
  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sset_exists_lifted.
  eval_exists_Econst_float.
  apply exec_Sset_exists_lifted.
  apply eval_exists_Econst_int.

  intros le_ H.
  solve_trivial.

  revert Hm.
  apply holds_list_comm_aux.
  apply count_occ_list_comm.
  intro i.
  repeat rewrite count_occ_app.
  simpl Int.unsigned.
  omega.
Defined.

Definition px_error' :=
  let (x, _) := f_sar_backprojection_loop_p_pre_body_correct' in 
  let '(y, _, _) := x in y
.

Definition px_error'_eq := $( field_eq px_error' )$ .

Definition px_error := $( match type of px_error'_eq with _ = ?z => exact z end )$ .

Definition px_left' :=
  let (x, _) := f_sar_backprojection_loop_p_pre_body_correct' in 
  let '(_, y, _) := x in y
.

Definition px_left'_eq := $( field_eq (px_left') )$ .

Definition px_left := $( match type of px_left'_eq with _ = ?z => exact z end )$ .

Definition px_right' :=
  let (x, _) := f_sar_backprojection_loop_p_pre_body_correct' in 
  let '(_, _, y) := x in y
.

Definition px_right'_eq := $( field_eq px_right' )$ .

Definition px_right := $( match type of px_right'_eq with _ = ?z => exact z end )$ .

Lemma f_sar_backprojection_loop_p_pre_body_correct:
  f_sar_backprojection_loop_p_pre_correct (px_error, px_left, px_right).
Proof.
  unfold px_error. rewrite <- px_error'_eq.
  unfold px_left. rewrite <- px_left'_eq.
  unfold px_right. rewrite <- px_right'_eq.
  unfold px_error', px_left', px_right'.
  destruct f_sar_backprojection_loop_p_pre_body_correct'.
  destruct x.
  destruct p.
  assumption.
Qed.

Definition f_sar_backprojection_norm_pre_correct BOUNDS :=
  let '(xdiff_error, xdiff_left, xdiff_right,
        ydiff_error, ydiff_left, ydiff_right,
        zdiff_error, zdiff_left, zdiff_right) := BOUNDS in
  forall
    `(HYPS: SARHypotheses)
    (b3 b4 b5 b6 b7 b8 : block)
    (ku2 dxdy2 dR_inv : float)
    (Hku2_val : B2R 53 1024 ku2 = 2 * B2R 53 1024 ku0)
    (Hdxdy2_val : B2R 53 1024 dxdy2 = / 2 * B2R 53 1024 dxdy0)
    (HdR_inv_error : Rabs (B2R 53 1024 dR_inv - / B2R 53 1024 dR0) <=
                     dR_inv_error)
    (HdR_inv_range : dR_inv_left <= B2R 53 1024 dR_inv <= dR_inv_right)
        (Hku2_finite : is_finite 53 1024 ku2 = true)
    (Hdxdy2_finite : is_finite 53 1024 dxdy2 = true)
    (HdR_inv_finite : is_finite 53 1024 dR_inv = true)
    (y : int)
    (Hy_int_range : (0 <= Int.signed y <= Z.of_nat BP_NPIX_Y - 1)%Z )
    (py : float)
    (Hpy_error : Rabs
                (B2R 53 1024 py -
                 (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_Y - 1) +
                  2 * Fcore_Raux.Z2R (Int.signed y)) * 
                 B2R 53 1024 dxdy2) <= py_error)                                        
    (Hpy_range : py_left <= B2R 53 1024 py <= py_right)
    (Hpy_finite : is_finite 53 1024 py = true)
    (x : int)
    (Hx_int_range : (0 <= Int.signed x <= Z.of_nat BP_NPIX_X - 1)%Z )
    (px : float)
    (Hpx_range : px_left <= B2R 53 1024 px <= px_right)
    (Hpx_error : Rabs
                (B2R 53 1024 px -
                 (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_X - 1) +
                  2 * Fcore_Raux.Z2R (Int.signed x)) * 
                 B2R 53 1024 dxdy2) <= px_error)
    (Hpx_finite : is_finite 53 1024 px = true)
    (m : mem)
    (p : int)
    (contrib_r contrib_i : float)
    (image_r image_i : Z -> option (SepLogic.type_of_chunk Mfloat32))
    (Hm : holds
            ((((((((Pperm b3 (Int.unsigned Int.zero) Freeable
                      (size_chunk_nat Mfloat32) ++
                    Pperm b4 (Int.unsigned Int.zero) Freeable
                      (size_chunk_nat Mfloat32)) ++
                   Pperm b5 (Int.unsigned Int.zero) Freeable
                     (size_chunk_nat Mfloat32)) ++
                  Pperm b6 (Int.unsigned Int.zero) Freeable
                    (size_chunk_nat Mfloat32)) ++
                 Pperm b7 (Int.unsigned Int.zero) Freeable
                   (size_chunk_nat Mfloat64)) ++
                Pperm b8 (Int.unsigned Int.zero) Freeable
                  (size_chunk_nat Mfloat64)) ++ P) ++
              Parray_opt Mfloat32 (Int.unsigned Int.zero) image_r bir
                (Int.unsigned oir) pir
                (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
             Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
               (Int.unsigned oii) pii
               (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))
              ) m)
    (Hp_int_range : (0 <= Int.signed p <= Z.of_nat N_PULSES - 1)%Z)
    ( le0 : Maps.PTree.t val )
    (LE: env_le
     (create_map
        ((_p, Vint p)
         :: (_contrib_r, Vfloat contrib_r)
            :: (_contrib_i, Vfloat contrib_i)
               :: (((((_p, Vint (Int.repr 0)) :: Datatypes.nil) ++
                     (_contrib_i, Vfloat (B754_zero 53 1024 false))
                     :: Datatypes.nil) ++
                    (_contrib_r, Vfloat (B754_zero 53 1024 false))
                    :: Datatypes.nil) ++ (_px, Vfloat px) :: Datatypes.nil) ++
                  (_ix, Vint x)
                  :: (((_ix, Vint (Int.repr 0)) :: Datatypes.nil) ++
                      (_py, Vfloat py) :: Datatypes.nil) ++
                     (_iy, Vint y)
                     :: ((((((((((((((((_iy, Vint (Int.repr 0))
                                       :: Datatypes.nil) ++
                                      (_ku_2, Vfloat ku2) :: Datatypes.nil) ++
                                     (_dxdy_2, Vfloat dxdy2) :: Datatypes.nil) ++
                                    (_dR_inv, Vfloat dR_inv) :: Datatypes.nil) ++
                                   (_z0, Vptr bz0 oz0) :: Datatypes.nil) ++
                                  (_dxdy, Vptr bdxdy odxdy) :: Datatypes.nil) ++
                                 (_dR, Vptr bdR odR) :: Datatypes.nil) ++
                                (_R0, Vptr br0 or0) :: Datatypes.nil) ++
                               (_ku, Vptr bku oku) :: Datatypes.nil) ++
                              (_platpos_z, Vptr bpz opz) :: Datatypes.nil) ++
                             (_platpos_y, Vptr bpy opy) :: Datatypes.nil) ++
                            (_platpos_x, Vptr bpx opx) :: Datatypes.nil) ++
                           (_data_i, Vptr bdi odi) :: Datatypes.nil) ++
                          (_data_r, Vptr bdr odr) :: Datatypes.nil) ++
                         (_image_i, Vptr bii oii) :: Datatypes.nil) ++
                        (_image_r, Vptr bir oir) :: Datatypes.nil)
        (Maps.PTree.empty val)) le0)
    ge
  ,
   exists (le2 : temp_env) (m1 : mem) (out1 : outcome),
     exec_stmt ge
       (Maps.PTree.set _bin (b8, tdouble)
          (Maps.PTree.set _R (b7, tdouble)
             (Maps.PTree.set _matched_filter_i (b6, tfloat)
                (Maps.PTree.set _matched_filter_r (b5, tfloat)
                   (Maps.PTree.set _sample_i (b4, tfloat)
                      (Maps.PTree.set _sample_r (b3, tfloat)
                         empty_env))))))
       le0 m f_sar_backprojection_norm_pre E0 le2 m1 out1 /\
     (forall le1_ : Maps.PTree.t val,
      env_le le2 le1_ ->
  m1 = m /\
  out1 = Out_normal /\
  exists xdiff ydiff zdiff,
   env_le
     (Maps.PTree.set _zdiff (Vfloat zdiff)
        (Maps.PTree.set _ydiff (Vfloat ydiff)
           (Maps.PTree.set _xdiff (Vfloat xdiff)
              (create_map
                 ((_p, Vint p)
                  :: (_contrib_r, Vfloat contrib_r)
                     :: (_contrib_i, Vfloat contrib_i)
                        :: (((((_p, Vint (Int.repr 0)) :: Datatypes.nil) ++
                              (_contrib_i, Vfloat (B754_zero 53 1024 false))
                              :: Datatypes.nil) ++
                             (_contrib_r, Vfloat (B754_zero 53 1024 false))
                             :: Datatypes.nil) ++
                            (_px, Vfloat px) :: Datatypes.nil) ++
                           (_ix, Vint x)
                           :: (((_ix, Vint (Int.repr 0)) :: Datatypes.nil) ++
                               (_py, Vfloat py) :: Datatypes.nil) ++
                              (_iy, Vint y)
                              :: ((((((((((((((((_iy, Vint (Int.repr 0))
                                                :: Datatypes.nil) ++
                                               (_ku_2, Vfloat ku2)
                                               :: Datatypes.nil) ++
                                              (_dxdy_2, Vfloat dxdy2)
                                              :: Datatypes.nil) ++
                                             (_dR_inv, Vfloat dR_inv)
                                             :: Datatypes.nil) ++
                                            (_z0, Vptr bz0 oz0)
                                            :: Datatypes.nil) ++
                                           (_dxdy, Vptr bdxdy odxdy)
                                           :: Datatypes.nil) ++
                                          (_dR, Vptr bdR odR)
                                          :: Datatypes.nil) ++
                                         (_R0, Vptr br0 or0) :: Datatypes.nil) ++
                                        (_ku, Vptr bku oku) :: Datatypes.nil) ++
                                       (_platpos_z, Vptr bpz opz)
                                       :: Datatypes.nil) ++
                                      (_platpos_y, Vptr bpy opy)
                                      :: Datatypes.nil) ++
                                     (_platpos_x, Vptr bpx opx)
                                     :: Datatypes.nil) ++
                                    (_data_i, Vptr bdi odi)
                                    :: Datatypes.nil) ++
                                   (_data_r, Vptr bdr odr) :: Datatypes.nil) ++
                                  (_image_i, Vptr bii oii) :: Datatypes.nil) ++
                                 (_image_r, Vptr bir oir) :: Datatypes.nil)
                 (Maps.PTree.empty val))))) le1_ /\
   is_finite 53 1024 xdiff = true /\
   xdiff_left <=
   B2R 53 1024 xdiff <=
   xdiff_right
   /\
   Rabs
     (B2R 53 1024 xdiff -
      (B2R 53 1024 (platpos_x (Int.signed p)) - B2R 53 1024 px)) <=
   xdiff_error
   /\
   is_finite 53 1024 ydiff = true
   /\
   ydiff_left <=
   B2R 53 1024 ydiff <=
   ydiff_right
   /\
   Rabs
     (B2R 53 1024 ydiff -
      (B2R 53 1024 (platpos_y (Int.signed p)) - B2R 53 1024 py)) <=
   ydiff_error
   /\
   is_finite 53 1024 zdiff = true
   /\
   zdiff_left <= B2R 53 1024 zdiff <= zdiff_right
   /\
   Rabs
     (B2R 53 1024 zdiff -
      (B2R 53 1024 (platpos_z (Int.signed p)) - B2R 53 1024 z0)) <=
   zdiff_error).


Lemma f_sar_backprojection_norm_pre_body_correct' : {BOUNDS |
 f_sar_backprojection_norm_pre_correct BOUNDS }.
Proof.
  eexists (_, _, _, _, _, _, _, _, _).
  unfold f_sar_backprojection_norm_pre_correct.
  intros data_r data_i P bdr odr bdi odi bpx opx platpos_x bpy opy.
  intros platpos_y bpz opz platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0.
  intros r0 bz0 oz0 z0 bir oir pir bii oii pii HYPS b3 b4 b5 b6 b7 b8 ku2.
  intros dxdy2 dR_inv Hku2_val Hdxdy2_val HdR_inv_error HdR_inv_range Hku2_finite.
  intros Hdxdy2_finite HdR_inv_finite y Hy_int_range py Hpy_error Hpy_range Hpy_finite.
  intros x Hx_int_range px Hpx_range Hpx_error Hpx_finite m p contrib_r contrib_i.
  intros image_r image_i Hm Hp_int_range le0 LE ge.
  inversion HYPS.

  unfold f_sar_backprojection_norm_pre.
  revert le0 LE.

  assert (holds P m) as HP
  by let rec t :=
        match constr:tt with
          | _ => assumption
          | _ => (apply holds_weak_left in Hm; t)
          | _ => (apply holds_weak_right in Hm; t)
        end
    in t.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sset_exists_lifted.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  pattern p at 1.
  replace p with (Int.repr (Int.signed p)) at 1 by (rewrite Int.repr_signed; reflexivity).
  replace (sizeof ge tdouble) with (size_chunk Mfloat64) by reflexivity.
  rewrite Hplatpos_x_array by (assumption || omega).
  solve_trivial.
  specialize (platpos_x_finite (Int.signed p) $( omega )$ ).
  specialize (platpos_x_range (Int.signed p) $( omega )$ ).
  unfold platpos_x_min, platpos_x_max in platpos_x_range.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  C_to_float_as xdiff Hxdiff.
  unfold px_left, px_right in Hpx_range.
  Transparent Float.of_bits Int64.repr.
  let t _ :=
      interval_
  in
  compute_fval_as' t Hxdiff Hxdiff_finite Hxdiff_val.
  match type of Hxdiff_val with
      ?z = _ =>
      interval_intro z with (i_prec 256) as Hxdiff_range
  end.
  rewrite Hxdiff_val in Hxdiff_range.
  destruct (rememb (B2R _ _ xdiff - (B2R _ _ (platpos_x (Int.signed p)) - B2R _ _ px))) as (xdiff_err & Exdiff).
  generalize Exdiff. intro Exdiff' .
  rewrite <- Hxdiff_val in Exdiff' .
  ring_simplify in Exdiff' .
  match type of Exdiff' with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hxdiff_error
  end.
  rewrite <- Exdiff' in Hxdiff_error ; clear Exdiff' .
  subst xdiff_err.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sset_exists_lifted.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  pattern p at 1.
  replace p with (Int.repr (Int.signed p)) at 1 by (rewrite Int.repr_signed; reflexivity).
  replace (sizeof ge tdouble) with (size_chunk Mfloat64) by reflexivity.
  rewrite Hplatpos_y_array by (assumption || omega).
  solve_trivial.
  specialize (platpos_y_finite (Int.signed p) $( omega )$ ).
  specialize (platpos_y_range (Int.signed p) $( omega )$ ).
  unfold platpos_y_min, platpos_y_max in platpos_y_range.
  (* here comes the framework into play! *)
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  C_to_float_as ydiff Hydiff.
  unfold py_left, py_right in Hpy_range.
  let t _ :=
      interval_
  in
  compute_fval_as' t Hydiff Hydiff_finite Hydiff_val.
  match type of Hydiff_val with
      ?z = _ =>
      interval_intro z with (i_prec 256) as Hydiff_range
  end.
  rewrite Hydiff_val in Hydiff_range.
  destruct (rememb (B2R _ _ ydiff - (B2R _ _ (platpos_y (Int.signed p)) - B2R _ _ py))) as (ydiff_err & Eydiff).
  generalize Eydiff. intro Eydiff' .
  rewrite <- Hydiff_val in Eydiff' .
  ring_simplify in Eydiff' .
  match type of Eydiff' with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hydiff_error
  end.
  rewrite <- Eydiff' in Hydiff_error ; clear Eydiff' .
  subst ydiff_err.

  apply exec_Sset_exists_lifted.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  pattern p at 1.
  replace p with (Int.repr (Int.signed p)) at 1 by (rewrite Int.repr_signed; reflexivity).
  replace (sizeof ge tdouble) with (size_chunk Mfloat64) by reflexivity.
  rewrite Hplatpos_z_array by (assumption || omega).
  solve_trivial.
  specialize (platpos_z_finite (Int.signed p) $( omega )$ ).
  specialize (platpos_z_range (Int.signed p) $( omega )$ ).
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  repeat ClightSep2.run.
  rewrite Hz0 by assumption.
  solve_trivial.
  match goal with
      K: z0_low <= _ <= z0_high |- _ =>
      unfold z0_low, z0_high in K
  end.
  unfold platpos_z_min, platpos_z_max in platpos_z_range.
  (* here comes the framework into play! *)
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  C_to_float_as zdiff Hzdiff.
  let t _ :=
      interval_
  in
  compute_fval_as' t Hzdiff Hzdiff_finite Hzdiff_val.
  match type of Hzdiff_val with
      ?z = _ =>
      interval_intro z with (i_prec 256) as Hzdiff_range
  end.
  rewrite Hzdiff_val in Hzdiff_range.
  destruct (rememb (B2R _ _ zdiff - (B2R _ _ (platpos_z (Int.signed p)) - B2R _ _ z0))) as (zdiff_err & Ezdiff).
  generalize Ezdiff. intro Ezdiff' .
  rewrite <- Hzdiff_val in Ezdiff' .
  ring_simplify in Ezdiff' .
  match type of Ezdiff' with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hzdiff_error
  end.
  rewrite <- Ezdiff' in Hzdiff_error ; clear Ezdiff' .
  subst zdiff_err.

  Set Printing Depth 2097152.
  intros le_ H.
  solve_trivial.
  eassumption.
Defined.

Definition xdiff_error' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(y, _, _, _, _, _, _, _, _) := x in y
.

Definition xdiff_error'_eq := $( field_eq xdiff_error' )$ .

Definition xdiff_error := $( match type of xdiff_error'_eq with _ = ?z => exact z end )$ .

Definition xdiff_left' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, y, _, _, _, _, _, _, _) := x in y
.

Definition xdiff_left'_eq := $( field_eq xdiff_left' )$ .

Definition xdiff_left := $( match type of xdiff_left'_eq with _ = ?z => exact z end )$ .

Definition xdiff_right' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, _, y, _, _, _, _, _, _) := x in y
.

Definition xdiff_right'_eq := $( field_eq xdiff_right' )$ .

Definition xdiff_right := $( match type of xdiff_right'_eq with _ = ?z => exact z end )$ .

Definition ydiff_error' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, _, _, y, _, _, _, _, _) := x in y
.

Definition ydiff_error'_eq := $( field_eq ydiff_error' )$ .

Definition ydiff_error := $( match type of ydiff_error'_eq with _ = ?z => exact z end )$ .

Definition ydiff_left' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, _, _, _, y, _, _, _, _) := x in y
.

Definition ydiff_left'_eq := $( field_eq ydiff_left' )$ .

Definition ydiff_left := $( match type of ydiff_left'_eq with _ = ?z => exact z end )$ .

Definition ydiff_right' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, _, _, _, _, y, _, _, _) := x in y
.

Definition ydiff_right'_eq := $( field_eq ydiff_right' )$ .

Definition ydiff_right := $( match type of ydiff_right'_eq with _ = ?z => exact z end )$ .

Definition zdiff_error' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, _, _, _, _, _, y, _, _) := x in y
.

Definition zdiff_error'_eq := $( field_eq zdiff_error' )$ .

Definition zdiff_error := $( match type of zdiff_error'_eq with _ = ?z => exact z end )$ .

Definition zdiff_left' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, _, _, _, _, _, _, y, _) := x in y
.

Definition zdiff_left'_eq := $( field_eq zdiff_left' )$ .

Definition zdiff_left := $( match type of zdiff_left'_eq with _ = ?z => exact z end )$ .

Definition zdiff_right' :=
  let (x, _) := f_sar_backprojection_norm_pre_body_correct' in 
  let '(_, _, _, _, _, _, _, _, y) := x in y
.

Definition zdiff_right'_eq := $( field_eq zdiff_right' )$ .

Definition zdiff_right := $( match type of zdiff_right'_eq with _ = ?z => exact z end )$ .

Lemma f_sar_backprojection_norm_pre_body_correct:
  f_sar_backprojection_norm_pre_correct
    (xdiff_error, xdiff_left, xdiff_right,
     ydiff_error, ydiff_left, ydiff_right,
     zdiff_error, zdiff_left, zdiff_right).     
Proof.
  unfold xdiff_error. rewrite <- xdiff_error'_eq.
  unfold xdiff_left. rewrite <- xdiff_left'_eq.
  unfold xdiff_right. rewrite <- xdiff_right'_eq.
  unfold xdiff_error', xdiff_left', xdiff_right'.
  unfold ydiff_error. rewrite <- ydiff_error'_eq.
  unfold ydiff_left. rewrite <- ydiff_left'_eq.
  unfold ydiff_right. rewrite <- ydiff_right'_eq.
  unfold ydiff_error', ydiff_left', ydiff_right'.
  unfold zdiff_error. rewrite <- zdiff_error'_eq.
  unfold zdiff_left. rewrite <- zdiff_left'_eq.
  unfold zdiff_right. rewrite <- zdiff_right'_eq.
  unfold zdiff_error', zdiff_left', zdiff_right'.
  destruct f_sar_backprojection_norm_pre_body_correct'.
  destruct x.
  destruct p.
  destruct p.
  destruct p.
  destruct p.
  destruct p.
  destruct p.
  destruct p.
  assumption.
Qed.
