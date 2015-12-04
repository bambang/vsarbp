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

Verification of SAR backprojection: summation of all pulse
contributions for one pixel.
*)

Require Export SARBackProjSourceDecomp.
Require Export SARBackProjSourceLink.
Require Export FPLang Clight2FP FPLangOpt Clight2FPOpt.
Require Export SARBackProjSourceSinOpt.
Open Scope R_scope.
Import List.
Open Scope list_scope.

Require SARBackProj.
Require ClightSep2.

Require Export SepLogicVars SARBackProjSourcePulse.

Require Summation.

Set Printing Depth 2097152.

Lemma homography_resym a b c d:
  c <> d ->
  (a - b) / (c - d) = (b - a) / (d - c).
Proof.
  intros.
  field.
  lra.
Qed.

(* Let us first prove that the total rounded sum
   will not overflow when cast to single-precision.
(consequently, the sum will never overflow during its computation
  in double-precision either.) *)
 
Lemma pixel_range_exists: { BOUND |
  Summation.E
    (pulse_range * (1 + error_bound Tdouble Normal) +
     error_bound Tdouble Denormal) 0
    (1 + error_bound Tdouble Normal) N_PULSES
  <= BOUND } .
Proof.
  esplit.
    destruct (rememb (Summation.E
           (pulse_range * (1 + error_bound Tdouble Normal) +
            error_bound Tdouble Denormal) 0 (1 + error_bound Tdouble Normal)
           (N_PULSES)
           )) as (BOUND & HBOUND).
    generalize HBOUND. intro HBOUND_.
    unfold Summation.E in HBOUND_.
    destruct (rememb ((1 + error_bound Tdouble Normal) ^ N_PULSES)) as (q & Hq).
    rewrite <- Hq in HBOUND_.
    unfold error_bound, pulse_range, Summation.E in HBOUND_.
    simpl in HBOUND_.
    unfold Rdiv in HBOUND_.
    repeat rewrite Rmult_0_l in HBOUND_.
    repeat rewrite Rplus_0_r in HBOUND_.
    repeat rewrite Rminus_0_r in HBOUND_.
    (* here assume that N_PULSES is a power of 2 *)
    unfold error_bound in Hq.
    simpl error_bound in Hq.
    simpl Fcore_Raux.bpow in Hq.    
    repeat
    match type of Hq with
        _ = _ ^ ?n =>
        let n2 := (eval vm_compute in (n / 2)%nat) in
        replace n with (2 * n2)%nat in Hq by (vm_compute; reflexivity);
          rewrite pow_sqr in Hq;
          match type of Hq with
              _ = ?r ^ _ =>
              let q1 := fresh "q1_" in
              let Hq1 := fresh "Hq1_" in
              destruct (rememb r) as (q1 & Hq1);
                let Hq1_ := fresh "Hq1t" in
                interval_intro r with (i_prec 128) as Hq1_;
                  rewrite <- Hq1 in Hq, Hq1_;
                  clear Hq1
          end
    end.
    simpl in Hq.
    subst q.
    field_simplify in HBOUND_.
    replace (BOUND / 1) with BOUND in HBOUND_ by field. 
    match type of HBOUND_ with
        _ = ?z =>
        interval_intro z upper with (i_prec 256) as HBOUND_BOUND;
          rewrite <- HBOUND_ in HBOUND_BOUND
    end.
    clear HBOUND_.

    rewrite HBOUND in HBOUND_BOUND.
    eexact HBOUND_BOUND.
Defined.

Definition pixel_range' :=
  let (x, _) := pixel_range_exists in x.

Definition pixel_range'_eq := $( field_eq pixel_range' )$ .

Definition pixel_range := $( match type of pixel_range'_eq with _ = ?z => exact z end )$ .

Lemma pixel_range_correct:
  Summation.E
    (pulse_range * (1 + error_bound Tdouble Normal) +
     error_bound Tdouble Denormal) 0
    (1 + error_bound Tdouble Normal) N_PULSES
  <= pixel_range.
Proof.
  unfold pixel_range. rewrite <- pixel_range'_eq.
  unfold pixel_range'.
  destruct pixel_range_exists.
  assumption.
Qed.

Lemma signed_eqm u v:
    Int.eqm (Int.signed u) v ->
    (Int.min_signed <= v <= Int.max_signed)%Z ->
    Int.signed u = v.
Proof.
  intros.
  apply Int.signed_repr in H0.
  rewrite <- H0.
  f_equal.
  rewrite <- (Int.repr_signed u).
  apply Int.eqm_samerepr.
  assumption.
Qed.


  Lemma env_le_elements_strong {A} l2 l1:
    (forall i, In i (Maps.PTree.elements l1) -> In i (Maps.PTree.elements l2)) ->
    forall t: Maps.PTree.t A,
      env_le l2 t ->
      env_le l1 t.
  Proof.
    unfold env_le.
    intros H t H0 i v H1.
    apply H0.
    apply Maps.PTree.elements_complete.
    apply H.
    apply Maps.PTree.elements_correct.
    assumption.
  Qed.

Lemma sar_backprojection'_S_gen N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku p n u:
  SARBackProjFacts.sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku u p (S n) =
  SARBackProj.Mplus
   (SARBackProjFacts.pulse_ N_RANGE_UPSAMPLED (platpos_x p) (platpos_y p) (platpos_z p) (data_r p) (data_i p) z0 R0 dR_inv px py ku)
   (SARBackProjFacts.sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku u (S p) n).
Proof.
  rewrite SARBackProjFacts.sar_backprojection'_charac.
  rewrite SARBackProjFacts.sar_backprojection'_S.
  symmetry.
  rewrite SARBackProjFacts.sar_backprojection'_charac.
  rewrite SARBackProjFacts.Mplus_comm.
  rewrite <- SARBackProjFacts.Mplus_assoc.
  f_equal.
  apply SARBackProjFacts.Mplus_comm.
Qed.

Lemma sar_backprojection_S_aux BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv dxdy y x ku c p n:
  SARBackProj.sar_backprojection  BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x c p (S n) =
  SARBackProj.Mplus
   (SARBackProj.pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED (platpos_x (p)%nat) (platpos_y (p)%nat) (platpos_z (p)%nat) (data_r (p)%nat) (data_i (p)%nat) z0 R0 dR_inv ku dxdy x y)
   (SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x c (S p) n).
Proof.
  repeat rewrite SARBackProjFacts.sar_backprojection_eq.
  rewrite SARBackProjFacts.pulse'_eq.
  apply sar_backprojection'_S_gen.
Qed.

Lemma sar_backprojection_S BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv dxdy y x ku p:
  forall c u,
  SARBackProj.sar_backprojection  BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x c u (S p) =
  SARBackProj.Mplus
   (SARBackProj.pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED (platpos_x (u + p)%nat) (platpos_y (u + p)%nat) (platpos_z (u + p)%nat) (data_r (u + p)%nat) (data_i (u + p)%nat) z0 R0 dR_inv ku dxdy x y)
   (SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x c u p).
Proof.
  induction p.
  {
    simpl.
    intros c u.
    rewrite SARBackProjFacts.Mplus_comm.
    f_equal.
    f_equal; f_equal; omega.
  }
  intros c u.
  rewrite sar_backprojection_S_aux.
  rewrite IHp.
  rewrite sar_backprojection_S_aux.
  rewrite SARBackProjFacts.Mplus_comm.
  rewrite <- SARBackProjFacts.Mplus_assoc.
  f_equal.
  {
    f_equal; f_equal; omega.
  }
  apply SARBackProjFacts.Mplus_comm.
Qed.

Corollary sar_backprojection_S_0 BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv dxdy y x ku p:
  SARBackProj.sar_backprojection  BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x (0,0) 0 (S p) =
  SARBackProj.Mplus
   (SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x (0,0) 0 p)
   (SARBackProj.pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED (platpos_x (p)%nat) (platpos_y (p)%nat) (platpos_z (p)%nat) (data_r (p)%nat) (data_i (p)%nat) z0 R0 dR_inv ku dxdy x y).
Proof.
  rewrite sar_backprojection_S.
  apply SARBackProjFacts.Mplus_comm.
Qed.

Lemma f_sar_backprojection_loop_p_body_correct :
  forall
    `(HYPS: SARHypotheses)
    ge
    `(MHYPS: ModuleHypotheses ge)
    (b3 b4 b5 b6 b7 b8 : block)
    (ku2 dxdy2 dR_inv : float)
    (Hku2_finite : is_finite 53 1024 ku2 = true)
    (Hku2_val : B2R 53 1024 ku2 = 2 * B2R 53 1024 ku0)
    (Hdxdy2_finite : is_finite 53 1024 dxdy2 = true)
    (Hdxdy2_val : B2R 53 1024 dxdy2 = / 2 * B2R 53 1024 dxdy0)
    (HdR_inv_finite : is_finite 53 1024 dR_inv = true)
    (HdR_inv_error : Rabs (B2R 53 1024 dR_inv - / B2R 53 1024 dR0) <=
                  dR_inv_error)
    (HdR_inv_range : dR_inv_left <= B2R 53 1024 dR_inv <= dR_inv_right)
    (y : int)
    (Hy_int_range : (0 <= Int.signed y <= Z.of_nat BP_NPIX_Y - 1)%Z )
    (py : float)
    (Hpy_finite : is_finite 53 1024 py = true)
    (Hpy_error : Rabs
                (B2R 53 1024 py -
                 (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_Y - 1) +
                  2 * Fcore_Raux.Z2R (Int.signed y)) * 
                 B2R 53 1024 dxdy2) <= py_error)
    (Hpy_range : py_left <= B2R 53 1024 py <= py_right)
    (x : int)
    (image_r image_i : Z -> option (SepLogic.type_of_chunk Mfloat32))
    (Hx_int_range : (0 <= Int.signed x <= Z.of_nat BP_NPIX_X - 1)%Z )
    (m : mem)
    (px : float)
    (Hpx_range : px_left <= B2R 53 1024 px <= px_right)
    (Hpx_error : Rabs
                (B2R 53 1024 px -
                 (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_X - 1) +
                  2 * Fcore_Raux.Z2R (Int.signed x)) * 
                 B2R 53 1024 dxdy2) <= px_error)
    (Hpx_finite : is_finite 53 1024 px = true)
    (Hm: holds
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
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)))
               m)
    (le0 : Maps.PTree.t val)
    (LE: env_le
     (create_map
        ((((((_p, Vint (Int.repr 0)) :: Datatypes.nil) ++
            (_contrib_i, Vfloat (B754_zero 53 1024 false)) :: Datatypes.nil) ++
           (_contrib_r, Vfloat (B754_zero 53 1024 false)) :: Datatypes.nil) ++
          (_px, Vfloat px) :: Datatypes.nil) ++
         (_ix, Vint x)
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
       le0 m f_sar_backprojection_loop_p E0 le1 m1 out1 /\
     (forall le1_ : Maps.PTree.t val,
      env_le le1 le1_ ->
      out1 = Out_normal /\
      exists (p : int) (contrib_r' contrib_i' : float),
          env_le
            (create_map
               ((_p, Vint p)
                :: (_contrib_r, Vfloat contrib_r')
                   :: (_contrib_i, Vfloat contrib_i')
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
                                        (_dR, Vptr bdR odR) :: Datatypes.nil) ++
                                       (_R0, Vptr br0 or0) :: Datatypes.nil) ++
                                      (_ku, Vptr bku oku) :: Datatypes.nil) ++
                                     (_platpos_z, Vptr bpz opz)
                                     :: Datatypes.nil) ++
                                    (_platpos_y, Vptr bpy opy)
                                    :: Datatypes.nil) ++
                                   (_platpos_x, Vptr bpx opx)
                                   :: Datatypes.nil) ++
                                  (_data_i, Vptr bdi odi) :: Datatypes.nil) ++
                                 (_data_r, Vptr bdr odr) :: Datatypes.nil) ++
                                (_image_i, Vptr bii oii) :: Datatypes.nil) ++
                               (_image_r, Vptr bir oir) :: Datatypes.nil)
               (Maps.PTree.empty val)) le1_ /\
          (Int.signed p = Z.of_nat N_PULSES)%Z /\
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
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)))                  
               m1
             /\
             is_finite _ _ contrib_r' = true /\
             is_finite _ _ contrib_i' = true /\
             let '(cr, ci) :=
             SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED 
                                         (fun i => B2R _ _ (platpos_x (Z.of_nat i)))
                                         (fun i => B2R _ _ (platpos_y (Z.of_nat i)))
                                         (fun i => B2R _ _ (platpos_z (Z.of_nat i)))
                                         (fun i j => B2R _ _ (data_r (Z.of_nat i) j))
                                         (fun i j => B2R _ _ (data_i (Z.of_nat i) j))
                                         (B2R _ _ z0)
                                         SARBounds.R0
                                         (/ SARBounds.dR)
                                         SARBounds.ku
                                         SARBounds.dxdy
                                         (Z.to_nat (Int.signed y))
                                         (Z.to_nat (Int.signed x))
                                         (0, 0)
                                         O (Z.to_nat (Int.signed p))
             in
             let Md := FPLang.error_bound Tdouble Normal in
             let Me := FPLang.error_bound Tdouble Denormal in
             let Mq := pulse_range + pulse_error in
             let Mdq := pulse_error in
             let M := 1 + Md in
             let L := Mq * Md in
             let K := (Mq * Md + Mdq * (1 + Md) + Me) in
             Rabs (B2R _ _ contrib_r' - cr) <= Summation.D K L M (Z.to_nat (Int.signed p))   /\
             Rabs (B2R _ _ contrib_i' - ci) <= Summation.D K L M (Z.to_nat (Int.signed p))   /\
             let Mq' := pulse_range in
             let K' := (Mq' * (1 + Md) + Me) in
             Rabs (B2R _ _ contrib_r') <= Summation.D K' 0 M (Z.to_nat (Int.signed p)) /\
             Rabs (B2R _ _ contrib_i') <= Summation.D K' 0 M (Z.to_nat (Int.signed p))
     ).
Proof.
  intros data_r data_i P bdr odr bdi odi bpx opx platpos_x bpy opy platpos_y bpz opz.
  intros platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0 r0 bz0 oz0 z0 bir.
  intros oir pir bii oii pii HYPS ge b_norm f_norm0 b_bin_sample f_bin_sample0.
  intros b_sin_cos f_sin_cos0 MHYPS b3 b4 b5 b6 b7 b8 ku2 dxdy2.
  intros dR_inv Hku2_finite Hku2_val Hdxdy2_finite Hdxdy2_val HdR_inv_finite.
  intros HdR_inv_error HdR_inv_range y Hy_int_range py Hpy_finite Hpy_error Hpy_range.
  intros x image_r image_i Hx_int_range m px Hpx_range Hpx_error Hpx_finite.
  intros Hm.
  inversion HYPS.
  inversion MHYPS.

  match goal with
      |-
      forall te2,
        env_le ?e te2 -> _
      =>
      destruct (rememb e) as (en & Hen);
        rewrite <- Hen
  end.
  repeat rewrite set_create_map in Hen.
  repeat rewrite create_map_app in Hen.
  subst en.

  match goal with
      |-
      forall _,
        env_le (create_map ?l _) _ -> _ 
      =>
  pose (Ip := fun te (m: Memory.Mem.mem) =>
                exists p contrib_r' contrib_i',
                  env_le (create_map ((_p, Vint p) ::
                                                   (_contrib_r, Vfloat contrib_r') ::
                                                   (_contrib_i, Vfloat contrib_i') ::
                                                   l) (Maps.PTree.empty _)) te
                  /\
                  (0 <= Integers.Int.signed p <= Z.of_nat SARBounds.N_PULSES)%Z /\
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
                                                                                                                                                                                    (Int.unsigned oir) pir (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                                                                                                                                                                                                                                                                 Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
                                                                                                                                                                                                                                                                 (Int.unsigned oii) pii (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) m
                    /\
             is_finite _ _ contrib_r' = true /\
             is_finite _ _ contrib_i' = true /\
             let '(cr, ci) :=
             SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED 
                                         (fun i => B2R _ _ (platpos_x (Z.of_nat i)))
                                         (fun i => B2R _ _ (platpos_y (Z.of_nat i)))
                                         (fun i => B2R _ _ (platpos_z (Z.of_nat i)))
                                         (fun i j => B2R _ _ (data_r (Z.of_nat i) j))
                                         (fun i j => B2R _ _ (data_i (Z.of_nat i) j))
                                         (B2R _ _ z0)
                                         SARBounds.R0
                                         (/ SARBounds.dR)
                                         SARBounds.ku
                                         SARBounds.dxdy
                                         (Z.to_nat (Int.signed y))
                                         (Z.to_nat (Int.signed x))
                                         (0, 0)
                                         O (Z.to_nat (Int.signed p))
             in
             let Md := FPLang.error_bound Tdouble Normal in
             let Me := FPLang.error_bound Tdouble Denormal in
             let Mq := pulse_range + pulse_error in
             let Mdq := pulse_error in
             let M := 1 + Md in
             let L := Mq * Md in
             let K := (Mq * Md + Mdq * (1 + Md) + Me) in
             Rabs (B2R _ _ contrib_r' - cr) <= Summation.D K L M (Z.to_nat (Int.signed p))   /\
             Rabs (B2R _ _ contrib_i' - ci) <= Summation.D K L M (Z.to_nat (Int.signed p))   /\
             let Mq' := pulse_range in
             let K' := (Mq' * (1 + Md) + Me) in
             Rabs (B2R _ _ contrib_r') <= Summation.D K' 0 M (Z.to_nat (Int.signed p)) /\
             Rabs (B2R _ _ contrib_i') <= Summation.D K' 0 M (Z.to_nat (Int.signed p)) /\
             Rabs cr <= Fcore_Raux.Z2R (Int.signed p) * Mq /\
             Rabs ci <= Fcore_Raux.Z2R (Int.signed p) * Mq
       );
    pose (Wp := fun te (m: Memory.Mem.mem) =>
                  match Maps.PTree.get _p te with
                    | Some (Vint p) =>
                      (SARBounds.N_PULSES - Z.to_nat (Integers.Int.signed p))%nat
                    | _ => O
                  end)                      
  end.

  apply (loop_exists_lifted Ip Wp).

  split.
  {
    unfold Ip.
    do 3 esplit.
    split.
    {
      apply env_le_set_l; [ reflexivity | ].
      apply env_le_set_l; [ reflexivity | ].
      apply env_le_set_l; [ reflexivity | ].
      reflexivity.
    }
    split.
    {
      vm_compute; intuition congruence.
    }
    solve_trivial.
    Transparent Int.repr.
    simpl SARBackProj.sar_backprojection.
    cbn iota.
    cbn beta.
    simpl B2R.
    replace (0 - 0) with 0 by ring.
    rewrite Rabs_R0.
    simpl Summation.D.
    cbn.
    lra.
  }

  clear m Hm.
  rewrite f_sar_backprojection_loop_p_body_fold.
  intros te0_ m H4 te0 H5.
  destruct H4 as (p & contrib_r & contrib_i  & LE & Hp & Hm & Hcontrib_r_finite & Hcontrib_i_finite & IP).
  destruct (
SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED
          (fun i : nat => B2R 53 1024 (platpos_x (Z.of_nat i)))
          (fun i : nat => B2R 53 1024 (platpos_y (Z.of_nat i)))
          (fun i : nat => B2R 53 1024 (platpos_z (Z.of_nat i)))
          (fun (i : nat) (j : Z) => B2R 24 128 (data_r (Z.of_nat i) j))
          (fun (i : nat) (j : Z) => B2R 24 128 (data_i (Z.of_nat i) j))
          (B2R 53 1024 z0) SARBounds.R0 (/ dR) ku dxdy
          (Z.to_nat (Int.signed y)) (Z.to_nat (Int.signed x)) 
          (0, 0) 0 (Z.to_nat (Int.signed p)) 
    ) as (cr & ci) eqn:CRCI.
  destruct IP as (Hcontrib_r_error & Hcontrib_i_error & Hcontrib_r_range & Hcontrib_i_range & Hcr_range & Hci_range).

  assert (Wp te0_ m = (N_PULSES - Z.to_nat (Int.signed p))%nat ) as WEQ.
  {
    unfold Wp.
    rewrite (LE _p _ (eq_refl _)).
    reflexivity.
  }
  rewrite WEQ; clear WEQ.

  generalize (env_le_trans _ _ _ LE H5).
  clear te0_ H5 LE.
  revert te0.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sifthenelse_exists_lifted.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  apply eval_exists_Econst_int.
  solve_trivial.
  rewrite bool_val_int_of_bool.
  solve_trivial.
  unfold Int.cmp.
  unfold Int.lt.
  simpl Z.of_nat in Hp.

    destruct (rememb (Summation.E
           (pulse_range * (1 + error_bound Tdouble Normal) +
            error_bound Tdouble Denormal) 0 (1 + error_bound Tdouble Normal)
           (N_PULSES)
           )) as (BOUND & HBOUND).
    generalize pixel_range_correct.
    intro Hsum_no_overflow.
    unfold pixel_range in Hsum_no_overflow.

  match goal with
      |- 
      forall _, _ ->
                exists _ _ _,
                  exec_stmt _ _ _ _ (if if ?b then true else false then _ else _) _ _ _ _ /\ _ =>
      destruct b as [CONDp | CONDp ]
  end.
  {
    cbn in CONDp.
    assert (0 <= Int.signed p <= Z.of_nat N_PULSES - 1)%Z as Hp_int_range by (cbn; omega).
    clear Hp.
    apply exec_Sskip_exists_lifted.
    Set Printing Depth 2097152.
    idtac.

    intros te2 H.
    generalize f_sar_backprojection_pulse_contrib_eq.
    apply exec_stmt_assoc_exists.
    revert te2 H.

    apply exec_Sseq_exists_lifted.
    unfold out_normal_b at 1.

    intros le0 H.

    edestruct
      f_sar_backprojection_pulse_contrib_body_correct
    with
      (ku2 := ku2)
      (dxdy2 := dxdy2)
      (dR_inv := dR_inv)
      (y := y)
      (py := py)
      (x := x)
      (px := px)
      (m := m)
      (p := p)
      (contrib_r := contrib_r) (contrib_i := contrib_i)
      (image_r := image_r) (image_i := image_i)
      (le0 := le0)
      as (le1 & m1 & out1 & Hexec & Hpost)
    ;
      try eassumption.
    solve_trivial.
    clear Hexec m Hm le0 H.
    intros le1_ H.
    specialize (Hpost _ H).
    rename m1 into m.
    destruct Hpost as (? & Hm & xdiff & ydiff & zdiff & prod_r & prod_i & LE & Hpulse_r_error & Hpulse_i_error & Hpulse_r_finite & Hpulse_i_finite & Hpulse_r_range & Hpulse_i_range).
    subst out1.
    clear le1 H.
    revert le1_ LE.
    
    match type of Hcontrib_r_range with
        _ <= ?z =>
        destruct (rememb z) as (rg & Hrg)
    end;
      rewrite <- Hrg in Hcontrib_r_range, Hcontrib_i_range.
    generalize Hrg. intro Hrg_.
    rewrite Summation.D_eq in Hrg_
    by (unfold error_bound; simpl; lra).
    
    assert (rg <= BOUND)
             as Hrg_le.
    {
      rewrite HBOUND; clear BOUND HBOUND.
      rewrite Hrg_; clear Hrg_.
      unfold Summation.E.
      destruct (rememb ((1 + error_bound Tdouble Normal) ^ Z.to_nat (Int.signed p))) as (u & Hu).
      rewrite <- Hu.
      destruct (rememb ((1 + error_bound Tdouble Normal) ^ N_PULSES)) as (t & Ht).
      rewrite <- Ht.
      unfold Rdiv.
      repeat rewrite Rmult_0_l.
      repeat rewrite Rplus_0_r.
      rewrite Rminus_0_r.
      unfold pulse_range, error_bound.
      simpl.
      assert (u <= t).
      {
        rewrite Hu.
        rewrite Ht.
        apply Rle_pow.
        {
          unfold error_bound; simpl; lra.
        }
        apply Nat2Z.inj_le.
        rewrite Z2Nat.id by tauto.
        omega.
      }
      lra.
    }
    clear Hrg_.

    match type of Hsum_no_overflow with
        _ <= ?z =>
        (assert (Rabs (B2R _ _ contrib_r) <= z) as Hcontrib_r_no_overflow by lra);
        (assert (Rabs (B2R _ _ contrib_i) <= z) as Hcontrib_i_no_overflow by lra)
    end.
    unfold pulse_range in Hpulse_r_range, Hpulse_i_range.

    apply exec_Sseq_exists_lifted.
    unfold out_normal_b at 1.

    destruct 
                (SARBackProj.pulse BP_NPIX_X BP_NPIX_Y
                           N_RANGE_UPSAMPLED
                           (B2R 53 1024 (platpos_x (Int.signed p)))
                           (B2R 53 1024 (platpos_y (Int.signed p)))
                           (B2R 53 1024 (platpos_z (Int.signed p)))
                           (fun i : Z => B2R 24 128 (data_r (Int.signed p) i))
                           (fun i : Z => B2R 24 128 (data_i (Int.signed p) i))
                           (B2R 53 1024 z0) SARBounds.R0 
                           (/ dR) ku dxdy (Z.to_nat (Int.signed x))
                           (Z.to_nat (Int.signed y)))
      as (pulse_r & pulse_i) eqn:Hpulse.
    simpl in Hpulse_r_error, Hpulse_i_error.

    (* add the real pulse contribution *)
    apply exec_Sset_exists_lifted.
    unfold f_sar_backprojection_pulse_contrib_r.
    apply eval_expr_exists_filter_domain.
    apply eval_expr_exists_filter_float.
    apply Vfloat_exists.
    (* here comes the framework into play! *)
    C_to_float_as contrib_r' Hcontrib_r'.
    Transparent Float.of_bits Int64.repr.
    compute_fval_as Hcontrib_r' Hcontrib_r'_finite Hcontrib_r'_val.
    rewrite Rmult_1_l in Hcontrib_r'_val.
    match type of Hcontrib_r'_val with
        _ * (_ + ?d) + ?e = _ =>
        generalize (Summation.error_rounded_sum_with_approx cr pulse_r (B2R _ _ contrib_r) (B2R _ _ prod_r) d e (pulse_range + pulse_error) pulse_error (error_bound Tdouble Normal) (error_bound Tdouble Denormal) (Z.to_nat (Int.signed p)));
        generalize (Summation.next_rounded_sum_range (B2R _ _ contrib_r) (Z.to_nat (Int.signed p)) (B2R _ _ prod_r) d e pulse_range (error_bound Tdouble Normal) (error_bound Tdouble Denormal))
    end.
    intros Hcontrib_r'_range Hcontrib_r'_error.
    specialize_assert Hcontrib_r'_error.
    {
      apply Rabs_le.
      apply Fcore_Raux.Rabs_le_inv in Hpulse_r_range.
      apply Fcore_Raux.Rabs_le_inv in Hpulse_r_error.
      unfold pulse_range, pulse_error in * |- *.
      lra.
    }
    specialize_assert Hcontrib_r'_error.
    { assumption. }
    specialize_assert Hcontrib_r'_error.
    { assumption. }
    specialize_assert Hcontrib_r'_error.
    { assumption. }
    specialize_assert Hcontrib_r'_error.
    { 
      rewrite INR_IZR_INZ.
      rewrite Z2Nat.id by omega.
      rewrite <- Fcore_Raux.Z2R_IZR.
      assumption.
    }
    cbv zeta in Hcontrib_r'_error.
    specialize_assert Hcontrib_r'_error.
    {
      assumption.
    }
    specialize_assert Hcontrib_r'_range.
    { assumption. }
    specialize_assert Hcontrib_r'_range.
    { assumption. }
    specialize_assert Hcontrib_r'_range.
    { assumption. }
    cbv zeta in Hcontrib_r'_range.
    specialize_assert Hcontrib_r'_range.
    { congruence. }
    rewrite Hcontrib_r'_val in Hcontrib_r'_error, Hcontrib_r'_range.

    (* add the imag pulse contribution *)
    apply exec_Sset_exists_lifted.
    unfold f_sar_backprojection_pulse_contrib_i.
    apply eval_expr_exists_filter_domain.
    apply eval_expr_exists_filter_float.
    apply Vfloat_exists.
    (* here comes the framework into play! *)
    C_to_float_as contrib_i' Hcontrib_i'.
    Transparent Float.of_bits Int64.repr.
    compute_fval_as Hcontrib_i' Hcontrib_i'_finite Hcontrib_i'_val.
    rewrite Rmult_1_l in Hcontrib_i'_val.
    match type of Hcontrib_i'_val with
        _ * (_ + ?d) + ?e = _ =>
        generalize (Summation.error_rounded_sum_with_approx ci pulse_i (B2R _ _ contrib_i) (B2R _ _ prod_i) d e (pulse_range + pulse_error) pulse_error (error_bound Tdouble Normal) (error_bound Tdouble Denormal) (Z.to_nat (Int.signed p)));
        generalize (Summation.next_rounded_sum_range (B2R _ _ contrib_i) (Z.to_nat (Int.signed p)) (B2R _ _ prod_i) d e pulse_range (error_bound Tdouble Normal) (error_bound Tdouble Denormal))
    end.
    intros Hcontrib_i'_range Hcontrib_i'_error.
    specialize_assert Hcontrib_i'_error.
    {
      apply Rabs_le.
      apply Fcore_Raux.Rabs_le_inv in Hpulse_i_range.
      apply Fcore_Raux.Rabs_le_inv in Hpulse_i_error.
      unfold pulse_range, pulse_error in * |- *.
      lra.
    }
    specialize_assert Hcontrib_i'_error.
    { assumption. }
    specialize_assert Hcontrib_i'_error.
    { assumption. }
    specialize_assert Hcontrib_i'_error.
    { assumption. }
    specialize_assert Hcontrib_i'_error.
    { 
      rewrite INR_IZR_INZ.
      rewrite Z2Nat.id by omega.
      rewrite <- Fcore_Raux.Z2R_IZR.
      assumption.
    }
    cbv zeta in Hcontrib_i'_error.
    specialize_assert Hcontrib_i'_error.
    {
      assumption.
    }
    specialize_assert Hcontrib_i'_range.
    { assumption. }
    specialize_assert Hcontrib_i'_range.
    { assumption. }
    specialize_assert Hcontrib_i'_range.
    { assumption. }
    cbv zeta in Hcontrib_i'_range.
    specialize_assert Hcontrib_i'_range.
    { congruence. }
    rewrite Hcontrib_i'_val in Hcontrib_i'_error, Hcontrib_i'_range.

    (* finalize the current iteration: increment p *)
    unfold out_normal_b at 1.
    unfold orb at 1.
    apply exec_Sset_exists_lifted.
    apply eval_exists_Ebinop.
    repeat ClightSep2.run.
    apply eval_exists_Econst_int.
    solve_trivial.
    unfold out_normal_b at 1.
    unfold orb at 1.

    intros le_ H.
    solve_trivial.

    assert (Int.signed (Int.add p (Int.repr 1)) = Int.signed p + 1)%Z as Hincr.
    {
      apply signed_eqm.
      {
        clear.
        rewrite signed_add.
        reflexivity.
      }
      cbn. omega.
    }

    assert (Z.to_nat (Int.signed (Int.add p (Int.repr 1))) = S (Z.to_nat (Int.signed p))) as HincrN.
    {
      rewrite Hincr.
      rewrite Z2Nat.inj_add by omega.
      replace (Z.to_nat 1) with 1%nat by reflexivity.
      omega.
    }      

    (* invariant *)
    split.
    {
      unfold Ip.
      exists (Int.add p (Int.repr 1)), contrib_r', contrib_i'.
      split.
      {
        (* local variables *)
        revert H.
        apply env_le_elements_strong.
        simpl.
        tauto.
      }
      split.
      {
        rewrite Hincr.
        omega.
      }
      split.
      {
        revert Hm.
        apply holds_list_comm_aux.
        apply count_occ_list_comm.
        intro.
        repeat rewrite count_occ_app.
        omega.
      }
      solve_trivial.
      rewrite HincrN.
      rewrite sar_backprojection_S_0.
      rewrite CRCI.
      rewrite Z2Nat.id by omega.
      rewrite Hpulse.
      unfold SARBackProj.Mplus.
      simpl fst.
      simpl snd.
      solve_trivial.
      rewrite Hincr.
      rewrite Fcore_Raux.Z2R_IZR.
      rewrite plus_IZR.
      replace (IZR 1) with 1 by reflexivity.
      rewrite <- Fcore_Raux.Z2R_IZR.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      split.
      {
        eapply Rle_trans.
        {
          apply Rabs_triang.
        }
        apply Rplus_le_compat; auto.
        apply Fcore_Raux.Rabs_le_inv in Hpulse_r_error.
        apply Fcore_Raux.Rabs_le_inv in Hpulse_r_range.
        apply Fcore_Raux.Rabs_le.
        unfold pulse_range in * |- *.
        lra.
      }
        eapply Rle_trans.
        {
          apply Rabs_triang.
        }
        apply Rplus_le_compat; auto.
        apply Fcore_Raux.Rabs_le_inv in Hpulse_i_error.
        apply Fcore_Raux.Rabs_le_inv in Hpulse_i_range.
        apply Fcore_Raux.Rabs_le.
        unfold pulse_range in * |- *.
        lra.
    }
    (* weight *)
    unfold Wp.
    rewrite (H _p _ (eq_refl _)).
    rewrite HincrN.
    assert (Z.to_nat (Int.signed p) < N_PULSES)%nat.
    {
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by omega.
      omega.
    }
    omega.
  }

  (* after all N_PULSES iterations *)
  apply exec_Sbreak_exists_lifted.
  unfold orb at 1.
  unfold out_normal_b at 1.
  unfold out_continue_b at 1.
  intros le_ H.
  assert (Int.signed p = Z.of_nat N_PULSES) as Hp_end.
  {
    cbn.
    cbn in CONDp.
    omega.
  }
  solve_trivial.
  rewrite CRCI.
  solve_trivial.
  assumption.
Qed.

(* We will do the same trick as before to compute a bound on the sum of the contributions of all pulses
   for one pixel BEFORE casting from double to single-precision. *)

Lemma pixel_error_before_cast_exists: { BOUND |
             let Md := FPLang.error_bound Tdouble Normal in
             let Me := FPLang.error_bound Tdouble Denormal in
             let Mq := pulse_range + pulse_error in
             let Mdq := pulse_error in
             let M := 1 + Md in
             let L := Mq * Md in
             let K := (Mq * Md + Mdq * (1 + Md) + Me) in
             Summation.D K L M N_PULSES <= BOUND }.
Proof.
  esplit.
  cbv zeta.
  rewrite Summation.D_eq by (vm_compute; lra).
    destruct (rememb (Summation.E
           ((pulse_range + pulse_error) * error_bound Tdouble Normal + pulse_error * (1 + error_bound Tdouble Normal) +
            error_bound Tdouble Denormal)
           ((pulse_range + pulse_error) * error_bound Tdouble Normal)
           (1 + error_bound Tdouble Normal)
           (N_PULSES)
           )) as (BOUND & HBOUND).
    generalize HBOUND. intro HBOUND_.
    unfold Summation.E in HBOUND_.
    rewrite INR_IZR_INZ in HBOUND_.
    rewrite <- Fcore_Raux.Z2R_IZR in HBOUND_.
    destruct (rememb ((1 + error_bound Tdouble Normal) ^ N_PULSES)) as (q & Hq).
    rewrite <- Hq in HBOUND_.
    unfold error_bound, pulse_range, pulse_error, Summation.E in HBOUND_.
    simpl in HBOUND_.
    (* here assume that N_PULSES is a power of 2 *)
    unfold error_bound in Hq.
    simpl error_bound in Hq.
    simpl Fcore_Raux.bpow in Hq.    
    repeat
    match type of Hq with
        _ = _ ^ ?n =>
        let n2 := (eval vm_compute in (n / 2)%nat) in
        replace n with (2 * n2)%nat in Hq by (vm_compute; reflexivity);
          rewrite pow_sqr in Hq;
          match type of Hq with
              _ = ?r ^ _ =>
              let q1 := fresh "q1_" in
              let Hq1 := fresh "Hq1_" in
              destruct (rememb r) as (q1 & Hq1);
                let Hq1_ := fresh "Hq1t" in
                interval_intro r with (i_prec 128) as Hq1_;
                  rewrite <- Hq1 in Hq, Hq1_;
                  clear Hq1
          end
    end.
    simpl in Hq.
    subst q.
    field_simplify in HBOUND_.
    replace (BOUND / 1) with BOUND in HBOUND_ by field. 
    match type of HBOUND_ with
        _ = ?z =>
        interval_intro z upper with (i_prec 256) as HBOUND_BOUND;
          rewrite <- HBOUND_ in HBOUND_BOUND
    end.
    clear HBOUND_.

    rewrite HBOUND in HBOUND_BOUND.
    eexact HBOUND_BOUND.
Defined.

Definition pixel_error_before_cast' :=
  let (x, _) := pixel_error_before_cast_exists in x.

Definition pixel_error_before_cast'_eq := $( field_eq pixel_error_before_cast' )$ .

Definition pixel_error_before_cast := $( match type of pixel_error_before_cast'_eq with _ = ?z => exact z end )$ .

Lemma pixel_error_before_cast_correct:
let Md := FPLang.error_bound Tdouble Normal in
             let Me := FPLang.error_bound Tdouble Denormal in
             let Mq := pulse_range + pulse_error in
             let Mdq := pulse_error in
             let M := 1 + Md in
             let L := Mq * Md in
             let K := (Mq * Md + Mdq * (1 + Md) + Me) in
             Summation.D K L M N_PULSES
  <= pixel_error_before_cast.
Proof.
  unfold pixel_error_before_cast. rewrite <- pixel_error_before_cast'_eq.
  unfold pixel_error_before_cast'.
  destruct pixel_error_before_cast_exists.
  assumption.
Qed.

(* Now we investigate the effect of casting the sum to single precision,
   thus computing the final error bound on all pulse contributions
   for one pixel. *)

Definition f_sar_backprojection_loop_x_correct BOUND :=
  forall
    `(HYPS: SARHypotheses)
    ge
    `(MHYPS: ModuleHypotheses ge)
    (b3 b4 b5 b6 b7 b8 : block)
    (ku2 dxdy2 dR_inv : float)
    (Hku2_finite : is_finite 53 1024 ku2 = true)
    (Hku2_val : B2R 53 1024 ku2 = 2 * B2R 53 1024 ku0)
    (Hdxdy2_finite : is_finite 53 1024 dxdy2 = true)
    (Hdxdy2_val : B2R 53 1024 dxdy2 = / 2 * B2R 53 1024 dxdy0)
    (HdR_inv_finite : is_finite 53 1024 dR_inv = true)
    (HdR_inv_error : Rabs (B2R 53 1024 dR_inv - / B2R 53 1024 dR0) <=
                     dR_inv_error)
    (HdR_inv_range : dR_inv_left <= B2R 53 1024 dR_inv <= dR_inv_right)
    (y : int)
    (Hy_int_range : (0 <= Int.signed y <= Z.of_nat BP_NPIX_Y - 1)%Z )
    (py : float)
    (Hpy_finite : is_finite 53 1024 py = true)
    (Hpy_error : Rabs
                (B2R 53 1024 py -
                 (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_Y - 1) +
                  2 * Fcore_Raux.Z2R (Int.signed y)) * 
                 B2R 53 1024 dxdy2) <= py_error)
    (Hpy_range : py_left <= B2R 53 1024 py <= py_right)
    (m : mem)
    (x : int)
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
    (Hx_int_range : (0 <= Int.signed x <= Z.of_nat BP_NPIX_X - 1)%Z )
    (te2 : Maps.PTree.t val)
    (LE: env_le
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
        (Maps.PTree.empty val)) te2)
  ,
   exists (le2 : temp_env) (m2 : mem) (out2 : outcome),
     exec_stmt ge
       (Maps.PTree.set _bin (b8, tdouble)
          (Maps.PTree.set _R (b7, tdouble)
             (Maps.PTree.set _matched_filter_i (b6, tfloat)
                (Maps.PTree.set _matched_filter_r (b5, tfloat)
                   (Maps.PTree.set _sample_i (b4, tfloat)
                      (Maps.PTree.set _sample_r (b3, tfloat)
                         empty_env))))))
       te2 m f_sar_backprojection_loop_x_body E0 le2 m2 out2 /\
     (forall le2_ : Maps.PTree.t val,
        env_le le2 le2_ ->
        out2 = Out_normal /\
        exists p contrib_r' contrib_i' px,
   env_le
     (create_map
        ((_p, Vint p)
         :: (_contrib_r, Vfloat contrib_r')
            :: (_contrib_i, Vfloat contrib_i')
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
        (Maps.PTree.empty val)) le2_ /\
        exists ir ii,
          let image_r' :=
              fun k =>
                if Z.eq_dec k (Z.of_nat BP_NPIX_X * Int.signed y + Int.signed x)
                then Some ir  
                else image_r k
          in
          let image_i' :=
              fun k =>
                if Z.eq_dec k (Z.of_nat BP_NPIX_X * Int.signed y + Int.signed x)
                then Some ii
                else image_i k
          in
          holds
         (((((((P ++
                   Parray_opt Mfloat32 0 image_r' bir 
                     (Int.unsigned oir) pir
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)) ++
                   Parray_opt Mfloat32 0 image_i' bii 
                     (Int.unsigned oii) pii
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
               Pperm b3 0 Freeable (size_chunk_nat Mfloat32)) ++
              Pperm b4 0 Freeable (size_chunk_nat Mfloat32)) ++
             Pperm b5 0 Freeable (size_chunk_nat Mfloat32)) ++
            Pperm b6 0 Freeable (size_chunk_nat Mfloat32)) ++
           Pperm b7 0 Freeable (size_chunk_nat Mfloat64)) ++
          Pperm b8 0 Freeable (size_chunk_nat Mfloat64)) m2 /\
          is_finite _ _ ir = true /\
          is_finite _ _ ii = true /\
     let '(cr, ci) :=
         SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED 
                                        (fun i => B2R _ _ (platpos_x (Z.of_nat i)))
                                        (fun i => B2R _ _ (platpos_y (Z.of_nat i)))
                                        (fun i => B2R _ _ (platpos_z (Z.of_nat i)))
                                        (fun i j => B2R _ _ (data_r (Z.of_nat i) j))
                                        (fun i j => B2R _ _ (data_i (Z.of_nat i) j))
                                        (B2R _ _ z0)
                                        SARBounds.R0
                                        (/ SARBounds.dR)
                                        SARBounds.ku
                                        SARBounds.dxdy
                                        (Z.to_nat (Int.signed y))
                                        (Z.to_nat (Int.signed x))
                                        (0, 0)
                                        O N_PULSES
     in
     (Rabs (B2R _ _ ir - cr) <= BOUND /\
      Rabs (B2R _ _ ii - ci) <= BOUND)).

Lemma f_sar_backprojection_loop_x_body_correct' : { BOUND |
        f_sar_backprojection_loop_x_correct BOUND }.
Proof.
  esplit.
  unfold f_sar_backprojection_loop_x_correct.
  intros data_r data_i P bdr odr bdi odi bpx opx platpos_x bpy opy platpos_y bpz opz.
  intros platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0 r0 bz0 oz0 z0 bir.
  intros oir pir bii oii pii HYPS ge b_norm f_norm0 b_bin_sample f_bin_sample0.
  intros b_sin_cos f_sin_cos0 MHYPS b3 b4 b5 b6 b7 b8 ku2 dxdy2.
  intros dR_inv Hku2_finite Hku2_val Hdxdy2_finite Hdxdy2_val HdR_inv_finite.
  intros HdR_inv_error HdR_inv_range y Hy_int_range py Hpy_finite Hpy_error Hpy_range.
  intros m x image_r image_i Hm Hx_int_range te2 LE.
  inversion HYPS.
  inversion MHYPS.

  generalize f_sar_backprojection_loop_p_pre_post_eq.
  apply exec_stmt_assoc_exists.
  revert te2 LE.
  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.

  intros le0 H.
  edestruct f_sar_backprojection_loop_p_pre_body_correct with (y := y) (x := x) as (le1 & m1 & out1 & Hexec & Hpost) ; try eassumption.
  solve_trivial.
  clear m Hm Hexec le0 H.
  rename m1 into m.

  intros le1_ H.
  specialize (Hpost _ H). clear le1 H.
  destruct Hpost as (? & px & LE & Hpx_range & Hpx_error & Hpx_finite & Hm).
  revert le1_ LE.
  subst.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.

  (* loop p *)
  intros le0 H.
  edestruct
    @f_sar_backprojection_loop_p_body_correct  
  with
  (ku2 := ku2) (dxdy2 := dxdy2) (dR_inv := dR_inv)
  (y := y) (py := py) (x := x)
  (image_r := image_r) (image_i := image_i)
  as (le1 & m1 & out1 & Hexec & Hpost)
  ; try eassumption.
  solve_trivial.
  clear le0 H m Hm Hexec.
  intros le1_ H.
  specialize (Hpost _ H); clear le1 H.
  rename m1 into m.
  destruct Hpost as
      (? & p & contrib_r' & contrib_i' & LE & Hp & Hm & Hcontrib_r'_finite & Hcontrib_i'_finite & Hpost).
  subst out1.
  rewrite Hp in Hpost.
  rewrite Nat2Z.id in Hpost.
  destruct (
SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y
              N_RANGE_UPSAMPLED
              (fun i : nat => B2R 53 1024 (platpos_x (Z.of_nat i)))
              (fun i : nat => B2R 53 1024 (platpos_y (Z.of_nat i)))
              (fun i : nat => B2R 53 1024 (platpos_z (Z.of_nat i)))
              (fun (i : nat) (j : Z) => B2R 24 128 (data_r (Z.of_nat i) j))
              (fun (i : nat) (j : Z) => B2R 24 128 (data_i (Z.of_nat i) j))
              (B2R 53 1024 z0) SARBounds.R0 (/ dR) ku dxdy
              (Z.to_nat (Int.signed y)) (Z.to_nat (Int.signed x)) 
              (0, 0) 0 N_PULSES) as (cr & ci).
  destruct Hpost as (Hcr_error & Hci_error & Hcr_range & Hci_range).
  generalize (Rle_trans _ _ _ Hcr_error pixel_error_before_cast_correct);
  generalize (Rle_trans _ _ _ Hci_error pixel_error_before_cast_correct);
  clear Hcr_error Hci_error;
  intros Hci_error Hcr_error.
  rewrite Summation.D_eq
    in Hcr_range, Hci_range
    by (vm_compute; lra).
  generalize (Rle_trans _ _ _ Hcr_range pixel_range_correct);
  generalize (Rle_trans _ _ _ Hci_range pixel_range_correct);
  clear Hcr_range Hci_range;
  intros Hci_range Hcr_range.

  unfold f_sar_backprojection_loop_p_post.
  revert le1_ LE.
  apply exec_Sseq_exists_lifted.
  apply exec_Sassign_exists_lifted.
  repeat ClightSep2.run.
  apply eval_exists_Ebinop.
  eval_Elvalue_exists.
  repeat ClightSep2.run.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.

  unfold pixel_range, pixel_error_before_cast in *.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  (* here comes the framework into play! *)
  C_to_float_as ir Hir.
  Transparent Float.of_bits Int64.repr Int.repr.
  compute_fval_as Hir Hir'_finite Hir_val.
  destruct (rememb (B2R _ _ ir - B2R _ _ contrib_r')) as (er & Her).
  generalize Her. intro Her_.
  rewrite <- Hir_val in Her_.
  ring_simplify in Her_.
  match type of Her_ with
      _ = ?z =>
      interval_intro (Rabs z) upper as Her_bound
  end.
  rewrite <- Her_ in Her_bound.
  clear Her_.
  subst er.
  generalize (Rabs_triang2 _ _ _ _ _ Her_bound Hcr_error).
  clear Her_bound Hcr_error.
  intro Hcr_error.
  solve_trivial.
  repeat ClightSep2.run.
  unfold Mem.storev.
  simpl sizeof.
  match goal with
      |- exists _,
           Mem.store _ _ _ ?i _ = _ /\ _
      =>
  assert ( i
      =
      (Int.unsigned oir +
      size_chunk Mfloat32 * Z.of_nat (Z.to_nat (Z.of_nat BP_NPIX_X * Int.signed y +
                                Int.signed x)))%Z
    ) as INDEX
  end.
  {
    apply unsigned_eqm.
    {
      repeat rewrite unsigned_add.
      repeat rewrite unsigned_mul.
      repeat rewrite <- Int.eqm_unsigned_repr.
      rewrite Z2Nat.id by (simpl Z.of_nat; omega).
      simpl size_chunk.
      simpl Z.of_nat.
      match goal with
          |- Int.eqm ?a ?b =>
          assert (a = b) as EQ
      end.
      {
        replace (Int.signed y) with (Int.unsigned y).
        {
          replace (Int.signed x) with (Int.unsigned x).
          {
            omega.
          }
          apply unsigned_eqm.
          {
            symmetry.
            apply Int.eqm_signed_unsigned.
          }
          cbn. cbn in Hx_int_range. omega.
        }
        apply unsigned_eqm.
        {
          symmetry.
          apply Int.eqm_signed_unsigned.
        }
        cbn. cbn in Hy_int_range. omega.
      }
      rewrite EQ.
      reflexivity.
    }
    rewrite Z2Nat.id by (simpl Z.of_nat; omega).
    revert Hoir_bound Hx_int_range Hy_int_range.
    simpl size_chunk.
    simpl Z.of_nat.
    split.
    {
      generalize (Int.unsigned_range oir). omega.
    }
    omega.
  }
  rewrite INDEX.
  let t Q :=
      match Q with
          Parray_opt _ _ _ bir (Int.unsigned oir) _ _ =>
          idtac
      end
  in
  revolve Hm t.
  generalize (
      fun H => 
        holds_Parray_opt_modify _ _ Hoir_align _ Hpir _ _ _ _ _ Hm
                                (Z.to_nat (Z.of_nat BP_NPIX_X * Int.signed y + Int.signed x)%Z) H
                                (ir)
    ).
  intro STORE.
  specialize_assert STORE.
  {
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by (simpl Z.of_nat; omega).
    rewrite Z2Nat.id by (simpl Z.of_nat; omega).
    revert Hx_int_range Hy_int_range.
    simpl Z.of_nat. clear. intros. omega.
  }
  clear Hm.
  destruct STORE as (m1 & Hm1_store & Hm).
  solve_trivial.
  clear m Hm1_store.
  rename m1 into m.

  (* store imag *)
  unfold out_normal_b at 1.
  apply exec_Sassign_exists_lifted.
  repeat ClightSep2.run.
  apply eval_exists_Ebinop.
  eval_Elvalue_exists.
  repeat ClightSep2.run.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.

  unfold pixel_range, pixel_error_before_cast in *.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  (* here comes the framework into play! *)
  C_to_float_as ii Hii.
  Transparent Float.of_bits Int64.repr Int.repr.
  compute_fval_as Hii Hii'_finite Hii_val.
  destruct (rememb (B2R _ _ ii - B2R _ _ contrib_i')) as (ei & Hei).
  generalize Hei. intro Hei_.
  rewrite <- Hii_val in Hei_.
  ring_simplify in Hei_.
  match type of Hei_ with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hei_bound
  end.
  rewrite <- Hei_ in Hei_bound.
  clear Hei_.
  subst ei.
  generalize (Rabs_triang2 _ _ _ _ _ Hei_bound Hci_error).
  clear Hei_bound Hci_error.
  intro Hci_error.
  solve_trivial.
  repeat ClightSep2.run.
  unfold Mem.storev.
  simpl sizeof.
  clear INDEX.
    match goal with
      |- exists _,
           Mem.store _ _ _ ?i _ = _ /\ _
      =>
  assert ( i
      =
      (Int.unsigned oii +
      size_chunk Mfloat32 * Z.of_nat (Z.to_nat (Z.of_nat BP_NPIX_X * Int.signed y +
                                Int.signed x)))%Z
    ) as INDEX
  end.
  {
    apply unsigned_eqm.
    {
      repeat rewrite unsigned_add.
      repeat rewrite unsigned_mul.
      repeat rewrite <- Int.eqm_unsigned_repr.
      rewrite Z2Nat.id by (simpl Z.of_nat; omega).
      simpl size_chunk.
      simpl Z.of_nat.
      match goal with
          |- Int.eqm ?a ?b =>
          assert (a = b) as EQ
      end.
      {
        replace (Int.signed y) with (Int.unsigned y).
        {
          replace (Int.signed x) with (Int.unsigned x).
          {
            omega.
          }
          apply unsigned_eqm.
          {
            symmetry.
            apply Int.eqm_signed_unsigned.
          }
          cbn. cbn in Hx_int_range. omega.
        }
        apply unsigned_eqm.
        {
          symmetry.
          apply Int.eqm_signed_unsigned.
        }
        cbn. cbn in Hy_int_range. omega.
      }
      rewrite EQ.
      reflexivity.
    }
    rewrite Z2Nat.id by (simpl Z.of_nat; omega).
    revert Hoii_bound Hx_int_range Hy_int_range.
    simpl size_chunk.
    simpl Z.of_nat.
    split.
    {
      generalize (Int.unsigned_range oii). omega.
    }
    omega.
  }
  rewrite INDEX.
  clear INDEX.
  let t Q :=
      match Q with
          Parray_opt _ _ _ bii (Int.unsigned oii) _ _ =>
          idtac
      end
  in
  revolve Hm t.
  generalize (
      fun H => 
        holds_Parray_opt_modify _ _ Hoii_align _ Hpii _ _ _ _ _ Hm
                                (Z.to_nat (Z.of_nat BP_NPIX_X * Int.signed y + Int.signed x)%Z) H
                                (ii)
    ).
  intro STORE.
  specialize_assert STORE.
  {
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by (simpl Z.of_nat; omega).
    rewrite Z2Nat.id by (simpl Z.of_nat; omega).
    revert Hx_int_range Hy_int_range.
    simpl Z.of_nat. clear. intros. omega.
  }
  clear Hm.
  destruct STORE as (m1 & Hm1_store & Hm).
  solve_trivial.
  clear m Hm1_store.
  rename m1 into m.
  
  (* finalize *)
  intros le1 H.
  split; [ reflexivity | ].
  do 4 esplit.
  split; [ eassumption | ].
  exists ir, ii.
  split.
  {
    revert Hm.
    apply holds_list_comm_aux.
    apply count_occ_list_comm.
    intro.
    repeat rewrite count_occ_app.
    rewrite Z2Nat.id by (simpl Z.of_nat; omega).
    repeat
    match goal with
        |- context [ SepLogic.count_occ (Parray_opt ?a ?b ?c ?d ?e ?e1 ?e2) ?f ] =>
        generalize (SepLogic.count_occ (Parray_opt a b c d e e1 e2) f)
    end.
    simpl Int.unsigned.
    intros.
    omega.
  }    
  solve_trivial.
  assumption.
Defined.

(* Here we actually compute the value of the final bound for all pulses of one pixel.
   The bound turns out to be better than the one in the paper,
   probably thanks to the optimized error terms computed by our VCFloat framework. *)

Definition pixel_error' :=
  let (x, _) := f_sar_backprojection_loop_x_body_correct' in x.

Definition pixel_error'_eq := $( field_eq pixel_error' )$ .

Definition pixel_error := $( match type of pixel_error'_eq with _ = ?z => exact z end )$ .

Lemma f_sar_backprojection_loop_x_body_correct :
        f_sar_backprojection_loop_x_correct pixel_error.
Proof.
  unfold pixel_error.
  rewrite <- pixel_error'_eq.
  unfold pixel_error'.
  destruct f_sar_backprojection_loop_x_body_correct'.
  assumption.
Qed.

Fixpoint free_list_exists (P: mem -> Prop) (l : list (block * Z * Z)) (m: mem): Prop :=
  match l with
    | nil => P m
    | (b, lo, hi)  :: l' =>
      exists m', Mem.free m b lo hi = Some m' /\
                 free_list_exists P l' m'
  end.

Lemma free_list_exists_correct l:
  forall (P: _ -> Prop) m,
    free_list_exists P l m ->
    exists m',
      Mem.free_list m l = Some m' /\ P m'.
Proof.
  induction l; simpl; eauto.
  intros P m H.
  destruct a.
  destruct p.
  destruct H as (m' & Hm' & FREE).
  rewrite Hm'.
  auto.
Qed.

Lemma holds_free_exists P (Q: _ -> Prop):
  (
    forall m,
      holds P m ->
      Q m
  ) ->
  forall b lo hi m,
    holds (P ++ Pperm b lo Freeable (Z.to_nat (hi - lo))) m ->
    exists m',
      Mem.free m b lo hi = Some m' /\
      Q m'.
Proof.
  intros H b lo hi m H0.
  apply holds_free in H0.
  destruct H0 as (m' & FREE & HOLDS).
  eauto.
Qed.

Ltac holds_free_solve :=
  match goal with
      K: holds _ ?m
      |- exists m',
           Mem.free ?m ?b ?lo ?hi = Some m' /\ _ =>
      (
        let t Q :=
            match Q with
                Pperm b lo Freeable (Z.to_nat (hi - lo)) =>
                idtac
        end
        in
          revolve K t;
        revert m K;
        apply holds_free_exists;
        intros m K
      )
  end.

Lemma f_sar_backprojection_body_correct' :
   forall ge `(MHYPS: ModuleHypotheses ge),
    SARBackProjSourceSpec.sar_backprojection_spec ge (Clight.Internal (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES))) pixel_error.
Proof.
  intros ge b_norm f_norm b_bin_sample f_bin_sample b_sin_cos f_sin_cos.
  intros MHYPS.
  inversion MHYPS.
  split; auto.
  intros data_r data_i P bdr odr bdi odi bpx opx platpos_x bpy opy.
  intros platpos_y bpz opz platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0.
  intros r0 bz0 oz0 z0 bir oir pir bii oii pii HYPS m Hm.
  intros st0.
  inversion HYPS.
  unfold st0.
  clear st0.
  apply star_call_eval_funcall_exists.
  apply eval_funcall_exists_internal.
  solve_trivial.
  simpl fn_vars.
  unfold alloc_variables_prop.
  intros b3 m3 H2 b4 m4 H3 b5 m5 H4 b6 m6 H5 b7 m7 H6 b8 m8.
  intros H7.
  repeat
    match goal with
        HOLDS: holds ?P ?m1,
               ALLOC: Mem.alloc ?m1 ?lo ?hi = (?m2, ?b)
        |- _ =>
        generalize (holds_alloc _ _ _ _ _ ALLOC _ HOLDS);
          clear m1 HOLDS ALLOC;
          intros HOLDS;
          rename m2 into m1
    end.
  solve_trivial.
  repeat rewrite <- (Parray_opt_none _ (fun _ => None) _ _ _ 0 (fun _ _ => eq_refl)) in Hm.
  replace (Z.to_nat (sizeof ge tfloat - 0))%nat
  with (size_chunk_nat Mfloat32)
    in Hm by reflexivity.
  replace (Z.to_nat (sizeof ge tdouble - 0))%nat
  with (size_chunk_nat Mfloat64)
    in Hm by reflexivity.

  generalize f_sar_backprojection_loop_y_pre_eq.
  apply exec_stmt_assoc_exists.

  apply exec_Sseq_exists.
  unfold out_normal_b at 1.
  edestruct (f_sar_backprojection_loop_y_pre_body_correct) as (? & ? & ? & exec_Y_PRE & H_Y_PRE ); try eassumption.
  destruct H_Y_PRE as (? & ? & ku2 & dxdy2 & dR_inv & ? & Hku2_finite & Hku2_val & Hdxdy2_finite & Hdxdy2_val & HdR_inv_finite & HdR_inv_error & HdR_inv_range).
  subst.
  solve_trivial.
  cbv iota.
  clear exec_Y_PRE.

  apply exec_stmt_exists_lift.

  (* loop y *)

  match goal with
      |-
      forall te2,
        env_le ?e te2 -> _
      =>
      destruct (rememb e) as (en & Hen);
        rewrite <- Hen
  end.
  repeat rewrite set_create_map in Hen.
  repeat rewrite create_map_app in Hen.
  subst en.
  match goal with
      |-
      forall te2,
        env_le (create_map ?l _) te2 -> _
      =>
      (* invariant for y loop *)
      pose (Iy := fun te (m: Memory.Mem.mem) =>
                    exists y,
                      env_le (create_map ((_iy, Vint y) :: l) (Maps.PTree.empty _)) te
                      /\
                      (0 <= Integers.Int.signed y <= Z.of_nat SARBounds.BP_NPIX_Y)%Z 
                      /\
                      exists image_r image_i,
                        holds
         (((((((P ++
                   Parray_opt Mfloat32 0 image_r bir
                     (Int.unsigned oir) pir (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)) ++
                   Parray_opt Mfloat32 0 image_i bii
                     (Int.unsigned oii) pii (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
               Pperm b3 0 Freeable (size_chunk_nat Mfloat32)) ++
              Pperm b4 0 Freeable (size_chunk_nat Mfloat32)) ++
             Pperm b5 0 Freeable (size_chunk_nat Mfloat32)) ++
            Pperm b6 0 Freeable (size_chunk_nat Mfloat32)) ++
           Pperm b7 0 Freeable (size_chunk_nat Mfloat64)) ++
          Pperm b8 0 Freeable (size_chunk_nat Mfloat64)) m
                        /\
                        forall y',
                          (0 <= y' < Int.signed y)%Z ->
                          forall x,
                            (0 <= x < Z.of_nat BP_NPIX_X)%Z ->
                            exists ir,
                              image_r (Z.of_nat BP_NPIX_X * y' + x)%Z = Some ir /\
                              exists ii,
                                image_i (Z.of_nat BP_NPIX_X * y' + x)%Z = Some ii /\
                                is_finite _ _ ir = true /\
                                is_finite _ _ ii = true /\
                                let '(cr, ci) :=
                                    SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED 
                                        (fun i => B2R _ _ (platpos_x (Z.of_nat i)))
                                        (fun i => B2R _ _ (platpos_y (Z.of_nat i)))
                                        (fun i => B2R _ _ (platpos_z (Z.of_nat i)))
                                        (fun i j => B2R _ _ (data_r (Z.of_nat i) j))
                                        (fun i j => B2R _ _ (data_i (Z.of_nat i) j))
                                        (B2R _ _ z0)
                                        SARBounds.R0
                                        (/ SARBounds.dR)
                                        SARBounds.ku
                                        SARBounds.dxdy
                                        (Z.to_nat y')
                                        (Z.to_nat x)
                                        (0, 0)
                                        O N_PULSES
                                in
                                (Rabs (B2R _ _ ir - cr) <= pixel_error /\
                                 Rabs (B2R _ _ ii - ci) <= pixel_error))
      ;
        pose (Wy := fun te (m: Memory.Mem.mem) =>
                     match Maps.PTree.get _iy te with
                       | Some (Vint y) =>
                         (SARBounds.BP_NPIX_Y - Z.to_nat (Integers.Int.signed y))%nat
                       | _ => O
                     end)                      
  end.
  apply (loop_exists_lifted Iy Wy).

  split.
  {
    exists (Int.repr 0).
    split.
    {
      apply env_le_set_l; [ reflexivity | ].
      apply create_map_le; auto.
      apply env_le_empty.
    }
    split.
    {
      vm_compute; intuition congruence.
    }
    esplit. esplit.
    split.
    {
      eexact Hm.
    }
    intros y' H.
    cbn in H.
    exfalso. omega.
  }

  clear m Hm.
  intros te0_ m H2 te0 H3.
  destruct H2 as (y & LE & Hy & image_r & image_i & Hm & Himages).

  assert (Wy te0_ m = (BP_NPIX_Y - Z.to_nat (Int.signed y))%nat) as WEQ.
  {
    unfold Wy.
    rewrite (LE _iy _ (eq_refl _)).
    reflexivity.
  }
  rewrite WEQ; clear WEQ.
  
  generalize (env_le_trans _ _ _ LE H3).
  clear te0_ H3 LE.
  revert te0.

  rewrite f_sar_backprojection_loop_y_body_fold.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Sifthenelse_exists_lifted.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  apply eval_exists_Econst_int.
  solve_trivial.
  rewrite bool_val_int_of_bool.
  solve_trivial.
  unfold Int.cmp.
  unfold Int.lt.
  simpl Z.of_nat in Hy.
  match goal with
      |- 
      forall _, _ ->
                exists _ _ _,
                  exec_stmt _ _ _ _ (if if ?b then true else false then _ else _) _ _ _ _ /\ _ =>
      destruct b as [COND | COND ]
  end.
  {
    Transparent Int.signed Int.repr.
    cbn in COND.
    assert (0 <= Int.signed y <= Z.of_nat BP_NPIX_Y - 1)%Z as Hy_int_range by (cbn; omega).
    clear Hy.
    apply exec_Sskip_exists_lifted.
    intros te2 Hte2.
    generalize f_sar_backprojection_loop_x_pre_eq.
    apply exec_stmt_assoc_exists.
    revert te2 Hte2.
    apply exec_Sseq_exists_lifted.
    unfold out_normal_b at 1.

    intros le0 H.
    edestruct f_sar_backprojection_loop_x_pre_body_correct as (le1 & m1 & out1 & Hexec & Hpost); try eassumption.
    solve_trivial.
    clear le0 H Hexec.
    intros le1_ H.
    specialize (Hpost _ H). clear le1 H.
    destruct Hpost as (? & ? & py & LE & Hpy_finite & Hpy_error & Hpy_range).
    subst.
    revert le1_ LE.

    (* loop x *)

    match goal with
        |-
        forall te2,
          env_le ?e te2 -> _
        =>
        destruct (rememb e) as (en & Hen);
          rewrite <- Hen
    end.
    repeat rewrite set_create_map in Hen.
    repeat rewrite create_map_app in Hen.
    subst en.
    match goal with
        |-
        forall te2,
          env_le (create_map ?l _) te2 -> _
        =>
        pose (Ix := fun te (m: Memory.Mem.mem) =>
                      exists x,
                        env_le (create_map ((_ix, Vint x) :: l) (Maps.PTree.empty _)) te
                        /\
                        (0 <= Integers.Int.signed x <= Z.of_nat SARBounds.BP_NPIX_X)%Z /\
             exists image_r image_i,
               holds
         (((((((P ++
                   Parray_opt Mfloat32 0 image_r bir 
                     (Int.unsigned oir) pir (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)) ++
                   Parray_opt Mfloat32 0 image_i bii 
                     (Int.unsigned oii) pii (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
               Pperm b3 0 Freeable (size_chunk_nat Mfloat32)) ++
              Pperm b4 0 Freeable (size_chunk_nat Mfloat32)) ++
             Pperm b5 0 Freeable (size_chunk_nat Mfloat32)) ++
            Pperm b6 0 Freeable (size_chunk_nat Mfloat32)) ++
           Pperm b7 0 Freeable (size_chunk_nat Mfloat64)) ++
          Pperm b8 0 Freeable (size_chunk_nat Mfloat64)) m
               /\
                        forall y' x',
                          ( 
                            (0 <= y' < Int.signed y)%Z /\ (0 <= x' < Z.of_nat BP_NPIX_X)%Z )
                            \/
                            (y' = Int.signed y /\ (0 <= x' < Int.signed x)%Z
                          ) ->
                            exists ir,
                              image_r (Z.of_nat BP_NPIX_X * y' + x')%Z = Some ir /\
                              exists ii,
                                image_i (Z.of_nat BP_NPIX_X * y' + x')%Z = Some ii /\
                                is_finite _ _ ir = true /\
                                is_finite _ _ ii = true /\
                                let '(cr, ci) :=
                                    SARBackProj.sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED 
                                        (fun i => B2R _ _ (platpos_x (Z.of_nat i)))
                                        (fun i => B2R _ _ (platpos_y (Z.of_nat i)))
                                        (fun i => B2R _ _ (platpos_z (Z.of_nat i)))
                                        (fun i j => B2R _ _ (data_r (Z.of_nat i) j))
                                        (fun i j => B2R _ _ (data_i (Z.of_nat i) j))
                                        (B2R _ _ z0)
                                        SARBounds.R0
                                        (/ SARBounds.dR)
                                        SARBounds.ku
                                        SARBounds.dxdy
                                        (Z.to_nat y')
                                        (Z.to_nat x')
                                        (0, 0)
                                        O N_PULSES
                                in
                                (Rabs (B2R _ _ ir - cr) <= pixel_error /\
                                 Rabs (B2R _ _ ii - ci) <= pixel_error))
;
          pose (Wx := fun te (m: Memory.Mem.mem) =>
                        match Maps.PTree.get _ix te with
                          | Some (Vint x) =>
                            (SARBounds.BP_NPIX_X - Z.to_nat (Integers.Int.signed x))%nat
                          | _ => O
                        end)                      
    end.
    apply (loop_exists_lifted Ix Wx).

    split.
    {
      exists (Int.repr 0).
      split.
      {
        apply env_le_set_l; [ reflexivity | ] .
        reflexivity.
      }
      split.
      {
        vm_compute; intuition congruence.
      }
      do 2 esplit.
      split.
      {
        eexact Hm.
      }
      intros y' x' H.
      destruct H.
      {
        destruct H.
        auto.
      }
      exfalso.
      destruct H as [_ H0].
      cbn in H0.
      omega.
    }

    clear image_r image_i m Hm Himages.
    intros te0_0 m H3 te0 H4.
    destruct H3 as (x & LE & Hx & image_r & image_i & Hm & Himages).

    assert (Wx te0_0 m = (BP_NPIX_X - Z.to_nat (Int.signed x))%nat) as WEQ.
    {
      unfold Wx.
      rewrite (LE _ix _ (eq_refl _)).
      reflexivity.
    }
    rewrite WEQ; clear WEQ.

    generalize (env_le_trans _ _ _ LE H4).
    clear te0_0 H4 LE.
    revert te0.

    rewrite f_sar_backprojection_loop_x_body_fold.

    apply exec_Sseq_exists_lifted.
    unfold out_normal_b at 1.
    apply exec_Sifthenelse_exists_lifted.
    apply eval_exists_Ebinop.
    repeat ClightSep2.run.
    apply eval_exists_Econst_int.
    solve_trivial.
    rewrite bool_val_int_of_bool.
    solve_trivial.
    unfold Int.cmp.
    unfold Int.lt.
    simpl Z.of_nat in Hx.
    match goal with
        |-
        forall _,
          _ ->
        exists _ _ _,
             exec_stmt _ _ _ _ (if if ?b then true else false then _ else _) _ _ _ _ /\ _ =>
        destruct b as [CONDx | CONDx ]
    end.
    {
      cbn in CONDx.
      assert (0 <= Int.signed x <= Z.of_nat BP_NPIX_X - 1)%Z as Hx_int_range by (cbn; omega).
      clear Hx.
      apply exec_Sskip_exists_lifted.
      intros te2 H.
      edestruct
        f_sar_backprojection_loop_x_body_correct
      with
      (ku2 := ku2) (dxdy2 := dxdy2) (dR_inv := dR_inv)
                   (y := y)
                   (py := py)
                   (m := m)
                   (x := x)
                   (image_r := image_r)
                   (image_i := image_i)
                   (te2 := te2)
        as
          (le2 & m2 & out2 & Hexec & 
               Hpost);
        try eassumption.
      solve_trivial.
      clear te2 H m Hm Hexec.
      intros le2_ H.
      specialize (Hpost _ H); clear le2 H.
      destruct Hpost as (? & p & contrib_r' & contrib_i' & px & LE & ir & ii & Hm & Hir_finite & Hii_finite & Herrors).
      subst out2.
      unfold out_normal_b.
      unfold orb.
      revert le2_ LE.
      
      apply exec_Sset_exists_lifted.
      apply eval_exists_Ebinop.
      repeat ClightSep2.run.
      apply eval_exists_Econst_int.
      solve_trivial.
      intros le_ H.
      solve_trivial.

      assert (Int.signed (Int.add x (Int.repr 1)) = Int.signed x + 1)%Z as Hincr.
      {
        apply signed_eqm.
        {
          clear.
          rewrite signed_add.
          reflexivity.
        }
        cbn. omega.
      }
      assert (Z.to_nat (Int.signed (Int.add x (Int.repr 1))) = S (Z.to_nat (Int.signed x))) as HincrN.
      {
        rewrite Hincr.
        rewrite Z2Nat.inj_add by omega.
        replace (Z.to_nat 1) with 1%nat by reflexivity.
        omega.
      }      

      (* invariant *)
      split.
      {
        unfold Ix.
        exists (Int.add x (Int.repr 1)).
        split.
        {
          (* local variables *)
          revert H.
          apply env_le_elements_strong.
          simpl.
          tauto.
        }
        split.
        {
          rewrite Hincr.
          omega.
        }
        solve_trivial.
        intros y' x' H0.
        cbv beta.
        match goal with
            |- exists _, (if ?b then _ else _) = _ /\ _ 
            => destruct b as [ EQ | NE ]
        end.
        {
          assert (y' = Int.signed y /\ x' = Int.signed x) as EQS.
          {
            simpl Z.of_nat in H0, EQ.
            omega.
          }
          destruct EQS; subst y' x'.
          solve_trivial.
          assumption.
        }
        apply Himages.
        simpl Z.of_nat in H0, NE |- * .
        omega.
      }
      (* weight *)
      unfold Wx.
      rewrite (H _ix _ (eq_refl _)).
      rewrite HincrN.
      assert (Z.to_nat (Int.signed x) < BP_NPIX_X)%nat.
      {
        apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by omega.
        omega.
      }
      omega.
    }
    
  (* after all BP_NPIX_X pixels of column y *)
  apply exec_Sbreak_exists_lifted.
  intros le_ H.
  unfold orb at 1.
  unfold out_normal_b at 1.
  unfold out_continue_b at 1.
  unfold orb at 1.
  unfold out_normal_b at 1.
  unfold out_continue_b at 1.
  unfold out_break_or_return_f.
  unfold out_return_o.
  revert le_ H.

  assert (Int.signed x = Z.of_nat BP_NPIX_X) as Hx_end.
  {
    cbn.
    cbn in CONDx.
    omega.
  }

  apply exec_Sset_exists_lifted.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  apply eval_exists_Econst_int.
  solve_trivial.
  intros le_ H.
  unfold orb at 1.
  unfold out_normal_b at 1.
  solve_trivial.

  assert (Int.signed (Int.add y (Int.repr 1)) = Int.signed y + 1)%Z as Hincr.
  {
    apply signed_eqm.
    {
      clear.
      rewrite signed_add.
      reflexivity.
    }
    cbn. omega.
  }
  assert (Z.to_nat (Int.signed (Int.add y (Int.repr 1))) = S (Z.to_nat (Int.signed y))) as HincrN.
  {
    rewrite Hincr.
    rewrite Z2Nat.inj_add by omega.
    replace (Z.to_nat 1) with 1%nat by reflexivity.
    omega.
  }      

  (* invariant *)
  split.
  {
    unfold Iy.
    exists (Int.add y (Int.repr 1)).
    split.
    {
      (* local variables *)
      revert H.
      apply env_le_elements_strong.
      simpl.
      tauto.
    }
    split.
    {
      rewrite Hincr.
      omega.
    }
    solve_trivial.
    rewrite Hincr.
    intros y' Hy' x' Hx'.
    apply Himages.
    destruct (Z.eq_dec y' (Int.signed y)) as [ EQ | NE ].
    {
      subst y'.
      rewrite Hx_end.
      omega.
    }
    omega.
  }
  (* weight *)
  unfold Wy.
  rewrite (H _iy _ (eq_refl _)).
  rewrite HincrN.
  assert (Z.to_nat (Int.signed y) < BP_NPIX_Y)%nat.
  {
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by omega.
    omega.
  }
  omega.
  }

   (* after all y columns, all pixels are done. *)
  apply exec_Sbreak_exists_lifted.
  intros le_ H.
  unfold orb at 1.
  unfold out_normal_b at 1.
  unfold out_continue_b at 1.

  apply free_list_exists_correct.
  match goal with
      |- free_list_exists _ ?l _ =>
      destruct (rememb l) as (u & Hu)
  end.
  rewrite <- Hu.
  cbn -[sizeof] in Hu.
  replace (size_chunk_nat Mfloat64) with (Z.to_nat (sizeof ge tdouble - 0)) in Hm by reflexivity.
  replace (size_chunk_nat Mfloat32) with (Z.to_nat (sizeof ge tfloat - 0)) in Hm by reflexivity.
  subst u.
  unfold free_list_exists.
  repeat holds_free_solve.
  unfold outcome_result_value_exists.
  unfold out_break_or_return_f.
  unfold out_return_o.
  simpl fn_return.
  unfold tvoid.
  solve_trivial.
  exists (fun i => match image_r i with  | Some j => j | None =>  (* dummy *) B754_zero _ _ true end).
  exists (fun i => match image_i i with  | Some j => j | None =>  (* dummy *) B754_zero _ _ true end).
  repeat rewrite Parray_int_eq.
  assert (Int.signed (Int.mul (Int.repr (Z.of_nat BP_NPIX_X)) (Int.repr (Z.of_nat BP_NPIX_Y)))
        = (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)%Z )
    as DIMS
               by reflexivity.
  rewrite DIMS.

  assert (Int.signed y = Z.of_nat BP_NPIX_Y) as Hy_end.
  {
    cbn.
    cbn in COND.
    omega.
  }
  rewrite Hy_end in Himages. 
  split.
  {
    rewrite <- Parray_opt_some with (bd := bir) (data1 := image_r).
    {
      rewrite <- Parray_opt_some with (bd := bii) (data1 := image_i).
      {
        rewrite <- app_ass.
        assumption.
      }
      intros j H0.
      destruct (image_i (Z.of_nat j)) eqn:EQ; auto.
      exfalso.
      apply Nat2Z.inj_lt in H0.
      rewrite Z2Nat.id in H0 by (vm_compute; congruence).
      generalize (Z_div_mod (Z.of_nat j) (Z.of_nat BP_NPIX_X) $( vm_compute; congruence )$ ).
      destruct (Z.div_eucl (Z.of_nat j) (Z.of_nat BP_NPIX_X)) as [quo rem] .
      destruct 1 as (Hquo & Hrem).
      assert (0 <= quo < Z.of_nat BP_NPIX_Y)%Z as H1 .
      {
        simpl in H0. simpl in Hrem. simpl Z.of_nat in Hquo. simpl. omega.
      }
      destruct (Himages _ H1 _ Hrem) as (_ & _ & ? & ? & _).
      congruence.
    }
    intros j H0.
    destruct (image_r (Z.of_nat j)) eqn:EQ; auto.
    exfalso.
    apply Nat2Z.inj_lt in H0.
    rewrite Z2Nat.id in H0 by (vm_compute; congruence).
    generalize (Z_div_mod (Z.of_nat j) (Z.of_nat BP_NPIX_X) $( vm_compute; congruence )$ ).
    destruct (Z.div_eucl (Z.of_nat j) (Z.of_nat BP_NPIX_X)) as [quo rem] .
    destruct 1 as (Hquo & Hrem).
    assert (0 <= quo < Z.of_nat BP_NPIX_Y)%Z as H1 .
    {
      simpl in H0. simpl in Hrem. simpl Z.of_nat in Hquo. simpl. omega.
    }
    destruct (Himages _ H1 _ Hrem) as (? & ? & _).
    congruence.
  }
  intros y0 H0 x H1.
  apply Nat2Z.inj_lt in H0.
  apply Nat2Z.inj_lt in H1.
  generalize (Nat2Z.is_nonneg y0). intro Hy0_pos.
  generalize (Nat2Z.is_nonneg x). intro Hx_pos.
  rewrite Nat2Z.inj_add.
  rewrite Nat2Z.inj_mul.
  destruct (Himages _ (conj Hy0_pos H0) _ (conj Hx_pos H1))
  as (ir & Hir & ii & Hii & Himg).
  rewrite Z.mul_comm.
  rewrite Hir.
  rewrite Hii.
  repeat rewrite Nat2Z.id in Himg.
  assumption.
Qed.


(* Finally, let us prove that our C compilation unit described in SARBackProjSource
    makes the ModuleHypotheses hold, when linked with suitable implementations
    for fabsf, sqrt and copysignf. *)

Require SARBackProjSourceSqrt.

Lemma prog_module_correct :
  forall (ge: Clight.genv) `(LINK: LinkingHypotheses ge),
     exists b_norm f_norm b_bin_sample f_bin_sample b_sin_cos f_sin_cos,
       ModuleHypotheses
         ge
         b_norm
         f_norm
         b_bin_sample
         f_bin_sample
         b_sin_cos
         f_sin_cos.
Proof.
  intros ge bf_sqrt cef_sqrt b_sin fn_sin b_cos fn_cos LINK.
  inversion LINK.

  generalize (Hp_extends _norm _ $( vm_compute_with_meta )$ ).
  destruct 1 as (bn & Hbn & Hfn).
  specialize (Hfn _ $( vm_compute_with_meta )$ ).

  generalize (Hp_extends _bin_sample _ $( vm_compute_with_meta )$ ).
  destruct 1 as (bbs & Hbbs & Hfbs).
  specialize (Hfbs _ $( vm_compute_with_meta )$ ).

  generalize (Hp_extends _sin_cos _ $( vm_compute_with_meta )$ ).
  destruct 1 as (bsc & Hbsc & Hfsc).
  specialize (Hfsc _ $( vm_compute_with_meta )$ ).

  do 6 esplit.
  constructor; eauto.
  {
    eapply f_norm_body_correct; eauto.
  }
  {
    apply f_bin_sample_body_correct.
  }
  eapply SARBackProjSourceSinOpt.f_sin_cos_error_correct; eauto.
Qed.

Theorem sar_backprojection_correct: 
  forall (ge: Clight.genv) `(LINK: LinkingHypotheses ge),
    sar_backprojection_spec ge (Clight.Internal (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES))) pixel_error.
                                         
Proof.
  intros ge bf_sqrt cef_sqrt b_sin fn_sin b_cos fn_cos LINK.
  apply prog_module_correct in LINK.
  break LINK.
  eapply f_sar_backprojection_body_correct'; eauto.
Qed.
