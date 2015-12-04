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

Verification of SAR backprojection: one pulse
contribution for one pixel.
*)

Require Export SARBackProjSourceDecomp.
Require Export SARBackProjSourceSpec.
Require Export FPLang Clight2FP FPLangOpt Clight2FPOpt.
Require Export SARBackProjSourceSinOpt.
Require Export RAux.
Open Scope R_scope.
Import List.
Open Scope list_scope.

Require SARBackProjFacts.
Require ClightSep2.

Require Export SepLogicVars SARBackProjSourceOpt2.


Inductive ModuleHypotheses
          (ge: Clight.genv)
          (b_norm: _)
          (f_norm: _)
          (b_bin_sample: _)
          (f_bin_sample: _)
          (b_sin_cos: _)
          (f_sin_cos: _)
: Prop :=
  ModuleHypothesesIntro
      (Hb_norm: Globalenvs.Genv.find_symbol ge _norm = Some b_norm)
      (Hf_norm: Globalenvs.Genv.find_funct_ptr ge b_norm = Some f_norm)      
      (Hf_norm_correct: f_norm_correct
                          (f_norm_error, f_norm_left, f_norm_right)
                          ge f_norm)
      (Hb_bin_sample: Globalenvs.Genv.find_symbol ge _bin_sample = Some b_bin_sample)
      (Hf_bin_sample: Globalenvs.Genv.find_funct_ptr ge b_bin_sample = Some f_bin_sample)
      (Hf_bin_sample_correct:
         f_bin_sample_correct (f_bin_sample_error, f_bin_sample_left, f_bin_sample_right) ge f_bin_sample)
      (Hb_sin_cos: Globalenvs.Genv.find_symbol ge _sin_cos = Some b_sin_cos)
      (Hf_sin_cos: Globalenvs.Genv.find_funct_ptr ge b_sin_cos = Some f_sin_cos)
      (Hf_sin_cos_correct:
         f_sin_cos_correct f_sin_error f_cos_error ge f_sin_cos)
.

Existing Class ModuleHypotheses.         


Lemma norm_error_propagate
      x x0 dx
      y y0 dy
      z z0 dz:
  Rabs (x - x0) <= dx ->
  Rabs (y - y0) <= dy ->
  Rabs (z - z0) <= dz ->
  exists ex ey ez,
    Rabs ex <= dx /\
    Rabs ey <= dy /\
    Rabs ez <= dz /\
    Rabs (sqrt (x * x + y * y + z * z) - sqrt (x0 * x0 + y0 * y0 + z0 * z0))
    = Rabs (ex * (x + x + ex) + ey * (y + y + ey) + ez * (z + z + ez))
        / (sqrt (x * x + y * y + z * z) + sqrt ((x + ex) * (x + ex) + (y + ey) * (y + ey) + (z + ez) * (z + ez)))
.
Proof.
  intros H H0 H1.
  pose (ex := x0 - x).
  pose (ey := y0 - y).
  pose (ez := z0 - z).
  rewrite Rabs_minus_sym in *.
  fold ex in H.
  fold ey in H0.
  fold ez in H1.
  replace x0 with (x + ex) by (unfold ex; ring).
  replace y0 with (y + ey) by (unfold ey; ring).
  replace z0 with (z + ez) by (unfold ez; ring).
  revert H H0 H1.
  generalize ex. clear ex. intro ex.
  generalize ey. clear ey. intro ey.
  generalize ez. clear ez. intro ez.
  intros H H0 H1.
  solve_trivial.
  rewrite sqrt_abs_error'.
  {
    f_equal.
    {
      f_equal. ring.
    }
    ring.
  }
  {
    generalize (Rle_0_sqr x).
    generalize (Rle_0_sqr y).
    generalize (Rle_0_sqr z).
    unfold Rsqr.
    lra.
  }
  generalize (Rle_0_sqr (x+ex)).
  generalize (Rle_0_sqr (y+ey)).
  generalize (Rle_0_sqr (z+ez)).
  unfold Rsqr.
  lra.
Qed.


Definition f_sar_backprojection_pulse_contrib_correct BOUNDS :=
  let '(pulse_error, pulse_range) := BOUNDS in
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
    (Hx_int_range : (0 <= Int.signed x <= Z.of_nat BP_NPIX_X - 1)%Z)
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
               (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) m)
    (Hp_int_range : (0 <= Int.signed p <= Z.of_nat N_PULSES - 1)%Z)
    (le0 : Maps.PTree.t val)
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
       le0 m f_sar_backprojection_pulse_contrib E0 le1 m1 out1 /\
     forall le',
       env_le le1 le' ->
       out1 = Out_normal /\
holds
         (((((((((
                  Pperm b8 (Int.unsigned Int.zero) Freeable
                    (size_chunk_nat Mfloat64)) ++
                 Pperm b3 (Int.unsigned Int.zero) Freeable
                   (size_chunk_nat Mfloat32)) ++
                Pperm b4 (Int.unsigned Int.zero) Freeable
                  (size_chunk_nat Mfloat32)) ++
               Pperm b6 (Int.unsigned Int.zero) Freeable
                 (size_chunk_nat Mfloat32)) ++
              Pperm b5 (Int.unsigned Int.zero) Freeable
                (size_chunk_nat Mfloat32)) ++ P) ++
            Parray_opt Mfloat32 (Int.unsigned Int.zero) image_r bir
              (Int.unsigned oir) pir
              (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
           Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
             (Int.unsigned oii) pii
             (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
          Pperm b7 (Int.unsigned Int.zero) Freeable (size_chunk_nat Mfloat64))
         m1
  /\ exists xdiff ydiff zdiff prod_r prod_i,
   env_le
     (Maps.PTree.set _prod_i (Vsingle prod_i)
        (Maps.PTree.set _prod_r (Vsingle prod_r)
           (Maps.PTree.set _zdiff (Vfloat zdiff)
              (Maps.PTree.set _ydiff (Vfloat ydiff)
                 (Maps.PTree.set _xdiff (Vfloat xdiff)
                    (create_map
                       ((_p, Vint p)
                        :: (_contrib_r, Vfloat contrib_r)
                           :: (_contrib_i, Vfloat contrib_i)
                              :: (((((_p, Vint (Int.repr 0)) :: Datatypes.nil) ++
                                    (_contrib_i,
                                    Vfloat (B754_zero 53 1024 false))
                                    :: Datatypes.nil) ++
                                   (_contrib_r,
                                   Vfloat (B754_zero 53 1024 false))
                                   :: Datatypes.nil) ++
                                  (_px, Vfloat px) :: Datatypes.nil) ++
                                 (_ix, Vint x)
                                 :: (((_ix, Vint (Int.repr 0))
                                      :: Datatypes.nil) ++
                                     (_py, Vfloat py) :: Datatypes.nil) ++
                                    (_iy, Vint y)
                                    :: ((((((((((((((((_iy,
                                                  Vint (Int.repr 0))
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
                                               (_R0, Vptr br0 or0)
                                               :: Datatypes.nil) ++
                                              (_ku, Vptr bku oku)
                                              :: Datatypes.nil) ++
                                             (_platpos_z, Vptr bpz opz)
                                             :: Datatypes.nil) ++
                                            (_platpos_y, Vptr bpy opy)
                                            :: Datatypes.nil) ++
                                           (_platpos_x, Vptr bpx opx)
                                           :: Datatypes.nil) ++
                                          (_data_i, Vptr bdi odi)
                                          :: Datatypes.nil) ++
                                         (_data_r, Vptr bdr odr)
                                         :: Datatypes.nil) ++
                                        (_image_i, Vptr bii oii)
                                        :: Datatypes.nil) ++
                                       (_image_r, Vptr bir oir)
                                       :: Datatypes.nil)
                       (Maps.PTree.empty val))))))) le'
/\
  Rabs
          (B2R 24 128 prod_r -
           fst
             (SARBackProj.pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED
                (B2R 53 1024 (platpos_x (Int.signed p)))
                (B2R 53 1024 (platpos_y (Int.signed p)))
                (B2R 53 1024 (platpos_z (Int.signed p)))
                (fun i : Z => B2R 24 128 (data_r (Int.signed p) i))
                (fun i : Z => B2R 24 128 (data_i (Int.signed p) i))
                (B2R 53 1024 z0) SARBounds.R0 (/ dR) ku dxdy
                (Z.to_nat (Int.signed x)) (Z.to_nat (Int.signed y)))) <=
        pulse_error /\
  Rabs
          (B2R 24 128 prod_i -
           snd
             (SARBackProj.pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED
                (B2R 53 1024 (platpos_x (Int.signed p)))
                (B2R 53 1024 (platpos_y (Int.signed p)))
                (B2R 53 1024 (platpos_z (Int.signed p)))
                (fun i : Z => B2R 24 128 (data_r (Int.signed p) i))
                (fun i : Z => B2R 24 128 (data_i (Int.signed p) i))
                (B2R 53 1024 z0) SARBounds.R0 (/ dR) ku dxdy
                (Z.to_nat (Int.signed x)) (Z.to_nat (Int.signed y)))) <=
        pulse_error /\
                      is_finite _ _ prod_r = true /\
                      is_finite _ _ prod_i = true /\
Rabs (B2R 24 128 prod_r) <=
                  pulse_range
/\
Rabs (B2R 24 128 prod_i) <=
                  pulse_range
.


Lemma f_sar_backprojection_pulse_contrib_body_correct': { BOUNDS |
  f_sar_backprojection_pulse_contrib_correct BOUNDS }.
Proof.
  eexists (_, _).
  unfold f_sar_backprojection_pulse_contrib_correct.
  intros data_r data_i P bdr odr bdi odi bpx opx platpos_x bpy opy platpos_y bpz opz.
  intros platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0 r0 bz0 oz0 z0 bir.
  intros oir pir bii oii pii HYPS ge b_norm f_norm0 b_bin_sample f_bin_sample.
  intros b_sin_cos f_sin_cos MHYPS b3 b4 b5 b6 b7 b8 ku2 dxdy2.
  intros dR_inv Hku2_finite Hku2_val Hdxdy2_finite Hdxdy2_val HdR_inv_finite.
  intros HdR_inv_error HdR_inv_range y Hy_int_range py Hpy_finite Hpy_error Hpy_range.
  intros x Hx_int_range px Hpx_range Hpx_error Hpx_finite m p contrib_r contrib_i.
  intros image_r image_i Hm Hp_int_range le0 H.
  inversion MHYPS.
  inversion HYPS.

  generalize f_sar_backprojection_norm_eq.
  apply exec_stmt_assoc_exists.
  revert le0 H.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.

  Set Printing Depth 2097152.
  idtac.

  intros le0 H.
  edestruct f_sar_backprojection_norm_pre_body_correct with (px := px) (py := py) (p := p) (x := x) (y := y) (ge := ge) as (le1 & m1 & out1 & Hexec & Hpost);  try eassumption.
  solve_trivial.
  clear le0 H Hexec.
  intros le1_ H.
  specialize (Hpost _ H); clear le1 H.
  destruct Hpost as (? & ? & xdiff & ydiff & zdiff & LE & Hxdiff_finite & Hxdiff_range & Hxdiff_error & Hydiff_finite & Hydiff_range & Hydiff_error & Hzdiff_finite & Hzdiff_range & Hzdiff_error).
  subst.
  revert le1_ LE.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Scall_exists_lifted.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  apply eval_exprlist_exists_correct.
  unfold eval_exprlist_exists.
  apply eval_exists_Eaddrof.
  eval_lvalue_exists_Evar.
  repeat ClightSep2.run.
  inversion Hf_norm_correct as (Hf_norm_type_ & Hf_norm_correct_).
  solve_trivial.
  clear Hf_norm_type_.
  apply eval_funcall_exists_star_call.
  assert (align_chunk Mfloat64 | Int.unsigned Int.zero)%Z as align_zero_64.
  {
    exists 0%Z.
    cbn.
    reflexivity.
  }
  assert (align_chunk Mfloat32 | Int.unsigned Int.zero)%Z as align_zero_32.
  {
    exists 0%Z.
    cbn.
    reflexivity.
  }
  destruct Hf_norm_correct_ with (os := Int.zero) (ps := Freeable) (m := m) (bs := b7) (P := ((((((((Pperm b3 (Int.unsigned Int.zero) Freeable
                                                                                                                                                                                                                                                                                                   (size_chunk_nat Mfloat32) ++
                                                                                                                                                                                                                                                                                                   Pperm b4 (Int.unsigned Int.zero) Freeable
                                                                                                                                                                                                                                                                                                   (size_chunk_nat Mfloat32)) ++
                                                                                                                                                                                                                                                                                                                              Pperm b5 (Int.unsigned Int.zero) Freeable
                                                                                                                                                                                                                                                                                                                              (size_chunk_nat Mfloat32)) ++
                                                                                                                                                                                                                                                                                                                                                         Pperm b6 (Int.unsigned Int.zero) Freeable
                                                                                                                                                                                                                                                                                                                                                         (size_chunk_nat Mfloat32)) ++
                                                                                                                                                                                                                                                                                                                                                                                    Pperm b8 (Int.unsigned Int.zero) Freeable
                                                                                                                                                                                                                                                                                                                                                                                    (size_chunk_nat Mfloat64)) ++ P) ++
                                                                                                                                                                                                                                                                                                                                                                                                                     Parray_opt Mfloat32 (Int.unsigned Int.zero) image_r bir
                                                                                                                                                                                                                                                                                                                                                                                                                     (Int.unsigned oir) pir
                                                                                                                                                                                                                                                                                                                                                                                                                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (Int.unsigned oii) pii
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))))) (x' := xdiff) (y' := ydiff) (z' := zdiff)
    as (m_ & Hexec & norm & Hnorm_finite & Hnorm_error & Hnorm_range & Hm_)
  ; try (assumption || now constructor); clear Hf_norm_correct_.
  {
    revert Hm.
    clear.
    apply holds_list_comm_aux.
    apply count_occ_list_comm.
    intro; repeat rewrite count_occ_app; omega.
  }
  solve_trivial.
  clear Hexec m Hm.
  rename m_ into m. rename Hm_ into Hm.

  intros le_ H.
  generalize f_sar_backprojection_bin_sample_eq.
  apply exec_stmt_assoc_exists.
  revert le_ H.
  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.

  intros le0 H.
  edestruct
    f_sar_backprojection_bin_sample_pre_body_correct
  with
  (ku2 := ku2) (dxdy2 := dxdy2) (dR_inv := dR_inv)
               (y := y)
               (py := py)
               (x := x)
               (px := px)
               (xdiff := xdiff)
               (ydiff := ydiff)
               (zdiff := zdiff)
               (norm := norm)
               (ge := ge)
    as (le1 & m1 & out1 & Hexec & Hpost) ;
    try eassumption.
  solve_trivial.
  clear m Hm Hexec le0 H.
  intros le1_ H.
  specialize (Hpost _ H). clear le1 H.
  rename m1 into m.
  destruct Hpost as (? & LE & bin & Hm & Hbin_finite & Hbin_range & Hbin_error).
  subst.
  revert le1_ LE.

  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Scall_exists_lifted.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  apply eval_exprlist_exists_correct.
  unfold eval_exprlist_exists.
  apply eval_exists_Eaddrof.
  eval_lvalue_exists_Evar.
  repeat ClightSep2.run.
  apply eval_exists_Eaddrof.
  eval_lvalue_exists_Evar.
  repeat ClightSep2.run.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  apply eval_Elvalue_exists.
  intros am Ham.
  vm_compute in Ham.
  subst am.
  apply eval_lvalue_exists_Ederef.
  repeat ClightSep2.run.
  unfold deref_loc_exists.
  solve_trivial.
  apply shallowest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  apply eval_exists_Ebinop.
  repeat ClightSep2.run.
  apply eval_Elvalue_exists.
  intros am Ham.
  vm_compute in Ham.
  subst am.
  apply eval_lvalue_exists_Ederef.
  repeat ClightSep2.run.
  unfold deref_loc_exists.
  solve_trivial.
  apply eval_exists_Eaddrof.
  eval_lvalue_exists_Evar.
  inversion Hf_bin_sample_correct as (Hf_bin_sample_type_ & Hf_bin_sample_correct_).
  solve_trivial.
  clear Hf_bin_sample_type_.
  apply eval_funcall_exists_star_call.
  destruct Hf_bin_sample_correct_
  with
  (bin := bin)
    (data_r := (data_r (Int.signed p)))
    (data_i := (data_i (Int.signed p)))
    (P :=
       ((((((P ++
                  Parray_opt Mfloat32 (Int.unsigned Int.zero) image_r bir
                  (Int.unsigned oir) pir
                  (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                                                                        Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
                                                                        (Int.unsigned oii) pii
                                                                        (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                                                                                                                              Pval Mfloat64 b7 (Int.unsigned Int.zero) Freeable
                                                                                                                              (Vfloat norm)) ++
                                             Pperm b5 (Int.unsigned Int.zero) Freeable
                                                                                                                                                                                                                                         (size_chunk_nat Mfloat32)) ++
                                                                                                                                                                                                                                                                    Pperm b6 (Int.unsigned Int.zero) Freeable
                                                                                                                                                                                                                                                                    (size_chunk_nat Mfloat32)) ++
                                                                                                                                                                                                                                                                                               Pval Mfloat64 b8 (Int.unsigned Int.zero) Freeable (Vfloat bin))
    )
    (bbi := b8) (obi := Int.zero)
    (bdr := (bdr))
    (odr := (Int.add odr (Int.mul (Int.repr (size_chunk Mfloat32 * N_RANGE_UPSAMPLED)) p)))
    (bdi := (bdi))
    (odi := (Int.add odi (Int.mul (Int.repr (size_chunk Mfloat32 * N_RANGE_UPSAMPLED)) p)))
    (psr := Freeable)
    (psi := Freeable)
    (bsr := b3) (osr := Int.zero)
    (bsi := b4) (osi := Int.zero)
    (m := m)
    as (? & Hexec & m' & ? & sample_r & sample_i & (Hsample_r_finite & Hsample_i_finite) & (Hsample_r_error & Hsample_i_error) & (Hsample_r_range & Hsample_i_range) & Hm'); clear Hf_bin_sample_correct_; (try assumption); (try now constructor).
  { apply Hdata_r_invariant; omega. }
  { apply Hdata_i_invariant; omega. }
  {
    intros m0 H.
    match goal with
        |- ?u = Some ?v =>
        cut (exists w, u = Some w /\ w = v); [ clear; intro H; break H; subst; assumption | ]
    end.
    Pval_solve.
    reflexivity.
  }
  {
    intros i H m0 H0.
    rewrite <- (Int.repr_signed p) at 1.
    apply Hdata_r; try omega.
    let rec t :=
        match constr:tt with
          | _ => assumption
          | _ => (apply holds_weak_left in H0; t)
          | _ => (apply holds_weak_right in H0; t)
        end
    in t.          
  }
  {
    intros i H m0 H0.
    rewrite <- (Int.repr_signed p) at 1.
    apply Hdata_i; try omega.
    let rec t :=
        match constr:tt with
          | _ => assumption
          | _ => (apply holds_weak_left in H0; t)
          | _ => (apply holds_weak_right in H0; t)
        end
    in t.          
  }
  {          
    revert Hm.
    apply holds_list_comm_aux.
    apply count_occ_list_comm.
    intros. repeat rewrite SepLogic.count_occ_app. omega.
  }
  subst.
  solve_trivial.
  clear m Hexec Hm.
  rename m' into m.
  rename Hm' into Hm.
  unfold set_opttemp.

  intros le_ H.
  generalize f_sar_backprojection_sin_cos_eq.
  apply exec_stmt_assoc_exists.
  revert le_ H.
  
  apply exec_Sseq_exists_lifted.
  unfold out_normal_b at 1.
  apply exec_Scall_exists_lifted.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  apply eval_exprlist_exists_correct.
  unfold f_sar_backprojection_sin_cos_args.
  unfold eval_exprlist_exists.
  apply eval_exists_Eaddrof.
  eval_lvalue_exists_Evar.
  apply eval_exists_Eaddrof.
  eval_lvalue_exists_Evar.
  apply deepest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  generalize Hku2_val. intro Hku2_val_.
  rewrite Hku_val in Hku2_val.
  unfold ku in Hku2_val.
  unfold f_norm_left, f_norm_right in Hnorm_range.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  C_to_float_as phi_ Hphi.
  let t _ :=
      try rewrite Hku2_val;
        interval_
  in
  compute_fval_as' t Hphi Hphi_finite Hphi_val.
  rewrite Hku2_val in Hphi_val.
  match type of Hphi_val with
      ?z = _ =>
      interval_intro z as Hphi_range
  end.
  rewrite Hphi_val in Hphi_range.
  destruct (rememb (B2R _ _ phi_ - (B2R _ _ ku2 * B2R _ _ norm))) as (d & Hd).
  generalize Hd. intro Hd_.
  rewrite Hku2_val in Hd_.
  rewrite <- Hphi_val in Hd_.
  ring_simplify in Hd_.
  match type of Hd_ with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hphi_error
  end.
  rewrite <- Hd_ in Hphi_error.
  clear Hd_.
  subst d.
  clear Hphi_val.
  solve_trivial.
  inversion Hf_sin_cos_correct as (Hf_sin_cos_type_ & Hf_sin_cos_correct_).
  solve_trivial.
  clear Hf_sin_cos_type_.
  apply eval_funcall_exists_star_call.
  destruct Hf_sin_cos_correct_
  with
  (os := Int.zero)
    (oc := Int.zero) (ps := Freeable) (pc := Freeable)
    (bs := b6) (bc := b5) (m := m)
    (P :=
         (((((P ++
                   Parray_opt Mfloat32 (Int.unsigned Int.zero) image_r bir
                     (Int.unsigned oir) pir
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                  Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
                    (Int.unsigned oii) pii
                    (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                 Pval Mfloat64 b7 (Int.unsigned Int.zero) Freeable
                   (Vfloat norm)) ++
           Pval Mfloat64 b8 (Int.unsigned Int.zero) Freeable (Vfloat bin)) ++
          Pval Mfloat32 b3 (Int.unsigned Int.zero) Freeable
            (Vsingle sample_r) ++
          Pval Mfloat32 b4 (Int.unsigned Int.zero) Freeable
            (Vsingle sample_i)))
    (x := phi_)
  as (m' & Hexec & si & co & Hm' & (Hsi_finite & Hco_finite) & (Hsi_error & Hco_error))
  ;
    clear Hf_sin_cos_correct_
  ;
    try (assumption || now constructor).
  {
    revert Hm.
    apply  holds_list_comm_aux.
    apply count_occ_list_comm.
    intros.
    repeat rewrite count_occ_app; omega.
  }
  {
    unfold SARBackProjSourceSin.x_left, SARBackProjSourceSin.x_right.
    lra.
  }
  solve_trivial.
  clear m Hm Hexec.
  rename m' into m.
  rename Hm' into Hm.
  unfold set_opttemp.
  unfold f_sar_backprojection_sin_cos_post.
  unfold f_sin_error, f_cos_error in Hsi_error, Hco_error.
  destruct (rememb (B2R _ _ si - sin (B2R _ _ phi_))) as (ds & Hds).
  rewrite <- Hds in Hsi_error.
  assert (B2R _ _ si = sin (B2R _ _ phi_) + ds) as Hs_eq by (subst ds; ring).
  interval_intro (sin (B2R _ _ phi_) + ds) as Hsi_range. 
  rewrite <- Hs_eq in Hsi_range.
  clear Hs_eq.
  subst ds.
  destruct (rememb (B2R _ _ co - cos (B2R _ _ phi_))) as (dc & Hdc).
  rewrite <- Hdc in Hco_error.
  assert (B2R _ _ co = cos (B2R _ _ phi_) + dc) as Hc_eq by (subst dc; ring).
  interval_intro (cos (B2R _ _ phi_) + dc) as Hci_range. 
  rewrite <- Hc_eq in Hci_range.
  clear Hc_eq.
  subst dc.
  apply exec_Sseq_exists_lifted.
  unfold out_normal_b.

  (* pulse contribution, real part *)
  apply exec_Sset_exists_lifted.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  unfold f_bin_sample_left, f_bin_sample_right in *.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  C_to_float_as prod_r Hprod_r.
  let t _ :=
        interval_
  in
  compute_fval_as' t Hprod_r Hprod_r_finite Hprod_r_val.
  match type of Hprod_r_val with
      ?z = _ => interval_intro (Rabs z) upper as Hprod_r_range
  end.
  rewrite Hprod_r_val in Hprod_r_range.
  destruct (rememb (B2R _ _ prod_r - (B2R _ _ sample_r * B2R _ _ co - B2R _ _ sample_i * B2R _ _ si)))
    as (er & Her).
  generalize Her. intro Her'.
  rewrite <- Hprod_r_val in Her'.
  ring_simplify in Her'.
  match type of Her' with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hprod_r_error
  end.
  rewrite <- Her' in Hprod_r_error.
  clear Her'.
  subst er.
  clear Hprod_r_val.

  (* pulse contribution, imag part *)
  apply exec_Sset_exists_lifted.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  match goal with
      |- exists v2,
           eval_expr _ _ ?te _ ?e v2 /\ _ =>
      match e with
          context [Evar ?u ?v] =>
          let i := (eval vm_compute in (next_index xH (Maps.PTree.elements te))) in
          let e1 := constr:(Evar u v) in
          let e2 := pattern_expr i e1 e in
          apply (subst_expr_exists e1 e2 i)
      end
  end.
  simpl typeof.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
  Pval_solve.
  unfold f_bin_sample_left, f_bin_sample_right in *.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  C_to_float_as prod_i Hprod_i.
  let t _ :=
        interval_
  in
  compute_fval_as' t Hprod_i Hprod_i_finite Hprod_i_val.
  match type of Hprod_i_val with
      ?z = _ => interval_intro (Rabs z) upper as Hprod_i_range
  end.
  rewrite Hprod_i_val in Hprod_i_range.
  destruct (rememb (B2R _ _ prod_i - (B2R _ _ sample_r * B2R _ _ si + B2R _ _ sample_i * B2R _ _ co)))
    as (ei & Hei).
  generalize Hei. intro Hei'.
  rewrite <- Hprod_i_val in Hei'.
  ring_simplify in Hei'.
  match type of Hei' with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hprod_i_error
  end.
  rewrite <- Hei' in Hprod_i_error.
  clear Hei'.
  subst ei.
  clear Hprod_i_val.

  (* Summary of all errors *)
  assert (B2R _ _ sample_r * B2R _ _ si + B2R _ _ sample_i * B2R _ _ co -
                                          (B2R _ _ sample_r * sin (B2R _ _ phi_) + B2R _ _ sample_i * cos (B2R _ _ phi_)) =
          B2R _ _ sample_r * (B2R _ _ si - sin (B2R _ _ phi_)) + B2R _ _ sample_i * (B2R _ _ co - cos (B2R _ _ phi_)))
    as Hprod_i_error_sincos_eq
         by ring.
  destruct (rememb (B2R _ _ si - sin (B2R _ _ phi_))) as (es & Hes).
  rewrite <- Hes in Hsi_error, Hprod_i_error_sincos_eq.
  destruct (rememb (B2R _ _ co - cos (B2R _ _ phi_))) as (ec & Hec).
  rewrite <- Hec in Hco_error, Hprod_i_error_sincos_eq.
  match type of Hprod_i_error_sincos_eq with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hprod_i_error_sincos
  end.
  rewrite <- Hprod_i_error_sincos_eq in Hprod_i_error_sincos; clear Hprod_i_error_sincos_eq.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_i_error Hprod_i_error_sincos).
  clear Hprod_i_error Hprod_i_error_sincos.
  intro Hprod_i_error.

  assert (B2R _ _ sample_r * B2R _ _ co - B2R _ _ sample_i * B2R _ _ si -
                                          (B2R _ _ sample_r * cos (B2R _ _ phi_) - B2R _ _ sample_i * sin (B2R _ _ phi_)) =
          B2R _ _ sample_r * (B2R _ _ co - cos (B2R _ _ phi_)) - B2R _ _ sample_i * (B2R _ _ si - sin (B2R _ _ phi_)))
    as Hprod_r_error_sincos_eq
         by ring.
  rewrite <- Hes in Hprod_r_error_sincos_eq.
  rewrite <- Hec in Hprod_r_error_sincos_eq.
  match type of Hprod_r_error_sincos_eq with
      _ = ?z =>
      interval_intro (Rabs z) upper as Hprod_r_error_sincos
  end.
  rewrite <- Hprod_r_error_sincos_eq in Hprod_r_error_sincos; clear Hprod_r_error_sincos_eq.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_r_error Hprod_r_error_sincos).
  clear Hprod_r_error Hprod_r_error_sincos Hco_error Hsi_error Hci_range Hsi_range Hsi_finite Hco_finite.
  clear es ec Hes Hec.
  intro Hprod_r_error.

  destruct (rememb (SARBackProj.bin_sample_component N_RANGE_UPSAMPLED
                         (fun i : Z => B2R 24 128 (data_r (Int.signed p) i))))
    as (bsc_r & Hbsc_r).
  rewrite <- Hbsc_r in Hsample_r_error.
  destruct (rememb (SARBackProj.bin_sample_component N_RANGE_UPSAMPLED
                         (fun i : Z => B2R 24 128 (data_i (Int.signed p) i))))
    as (bsc_i & Hbsc_i).
  rewrite <- Hbsc_i in Hsample_i_error.
  destruct (rememb (B2R _ _ sample_r - bsc_r (B2R _ _ bin))) as (er & Her).
  rewrite <- Her in Hsample_r_error.
  destruct (rememb (B2R _ _ sample_i - bsc_i (B2R _ _ bin))) as (ei & Hei).
  rewrite <- Hei in Hsample_i_error.

  assert (B2R _ _ sample_r * sin (B2R _ _ phi_)
          + B2R _ _ sample_i * cos (B2R _ _ phi_)
            - (bsc_r (B2R _ _ bin) * sin (B2R _ _ phi_)
               + bsc_i (B2R _ _ bin) * cos (B2R _ _ phi_))
          = er * sin (B2R _ _ phi_) + ei * cos (B2R _ _ phi_))
    as Her_eq
      by (subst er; subst ei; ring).
  unfold f_bin_sample_error in *.
  match type of Her_eq with
      _ = ?z => interval_intro (Rabs z) upper as Her_err
  end. 
  rewrite <- Her_eq in Her_err; clear Her_eq.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_i_error Her_err);
    clear Hprod_i_error Her_err.
  intro Hprod_i_error.

  assert (B2R _ _ sample_r * cos (B2R _ _ phi_)
          - B2R _ _ sample_i * sin (B2R _ _ phi_)
            - (bsc_r (B2R _ _ bin) * cos (B2R _ _ phi_)
               - bsc_i (B2R _ _ bin) * sin (B2R _ _ phi_))
          = er * cos (B2R _ _ phi_) - ei * sin (B2R _ _ phi_))
    as Hei_eq
      by (subst er; subst ei; ring).
  match type of Hei_eq with
      _ = ?z => interval_intro (Rabs z) upper as Hei_err
  end. 
  rewrite <- Hei_eq in Hei_err; clear Hei_eq.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_r_error Hei_err);
    clear Hprod_r_error Hei_err.
  intro Hprod_r_error.
  clear Hsample_i_error Hsample_i_finite Hsample_i_range Hsample_r_error Hsample_r_finite Hsample_r_range
        er Her ei Hei.

  rewrite Hdxdy_val in Hdxdy2_val.
  rewrite Hdxdy2_val in Hpx_error.
  match type of Hpx_error with
      Rabs (_ - ?z) <= _ =>
      destruct (rememb z) as (px_ & Hpx_)
  end.
  rewrite <- Hpx_ in Hpx_error.
  assert (B2R _ _ (platpos_x (Int.signed p)) - B2R _ _ px - (B2R _ _ (platpos_x (Int.signed p)) - px_)
          = - (B2R _ _ px - px_))
    as Hxdiff_err_eq
      by ring.
  apply (f_equal Rabs) in Hxdiff_err_eq.
  rewrite Rabs_Ropp in Hxdiff_err_eq.
  rewrite <- Hxdiff_err_eq in Hpx_error.
  clear Hxdiff_err_eq.
  generalize (Rabs_triang2 _ _ _ _ _ Hxdiff_error Hpx_error).
  clear Hxdiff_error Hpx_error. intro Hxdiff_error.

  rewrite Hdxdy2_val in Hpy_error.
  match type of Hpy_error with
      Rabs (_ - ?z) <= _ =>
      destruct (rememb z) as (py_ & Hpy_)
  end.
  rewrite <- Hpy_ in Hpy_error.
  assert (B2R _ _ (platpos_y (Int.signed p)) - B2R _ _ py - (B2R _ _ (platpos_y (Int.signed p)) - py_)
          = - (B2R _ _ py - py_))
    as Hydiff_err_eq
      by ring.
  apply (f_equal Rabs) in Hydiff_err_eq.
  rewrite Rabs_Ropp in Hydiff_err_eq.
  rewrite <- Hydiff_err_eq in Hpy_error.
  clear Hydiff_err_eq.
  generalize (Rabs_triang2 _ _ _ _ _ Hydiff_error Hpy_error).
  clear Hydiff_error Hpy_error. intro Hydiff_error.

  generalize (norm_error_propagate _ _ _ _ _ _ _ _ _ Hxdiff_error Hydiff_error Hzdiff_error).
  destruct 1 as (ex & ey & ez & Hex & Hey & Hez & Hnorm_err_eq).
  unfold xdiff_error, px_error, ydiff_error, py_error, zdiff_error,
  xdiff_left, xdiff_right, ydiff_left, ydiff_right, zdiff_left, zdiff_right in *.
  match type of Hnorm_err_eq with
      _ = ?z => interval_intro z upper as Hnorm_error_2
  end.
  rewrite <- Hnorm_err_eq in Hnorm_error_2; clear ex Hex ey Hey ez Hez Hnorm_err_eq.
  clear Hxdiff_error Hydiff_error Hzdiff_error.
  generalize (Rabs_triang2 _ _ _ _ _ Hnorm_error Hnorm_error_2);
    clear Hnorm_error Hnorm_error_2.
  intro Hnorm_error.
  match type of Hnorm_error with
      Rabs (_ - ?n) <= _ =>
      destruct (rememb n) as (norm_ & Hnorm_)
  end.
  rewrite <- Hnorm_ in Hnorm_error.
  
  rewrite Hr0_val, HdR_val in Hbin_error.
  generalize
    (Rmult_le_compat _ _ _ _ (Rabs_pos _) (Rabs_pos (/ dR)) Hnorm_error (Rle_refl _)).
  intro Hnorm_error_.
  rewrite <- Rabs_mult in Hnorm_error_.
  unfold dR in Hnorm_error_ at 2.
  rewrite (Rabs_right (/ _)) in Hnorm_error_ by lra.
  destruct (rememb ((norm_ - SARBounds.R0) * / dR)) as (bin_ & Hbin_).
  assert ((B2R _ _ norm - SARBounds.R0) * / dR - bin_
          = (B2R _ _ norm - norm_) * / dR)
    as Hbin_err_eq
         by (subst bin_; ring).
  rewrite <- Hbin_err_eq in Hnorm_error_; clear Hbin_err_eq.
  generalize (Rabs_triang2 _ _ _ _ _ Hbin_error Hnorm_error_).
  clear Hbin_error Hnorm_error_. intro Hbin_error.
  unfold bin_error, f_norm_error in Hbin_error, Hnorm_error.

  generalize 
    (Rmult_le_compat _ _ _ _ (Rabs_pos (2 * ku)) (Rabs_pos _) (Rle_refl _) (Hnorm_error)).
  clear Hnorm_error. intro Hangle_error.
  unfold ku in Hangle_error at 2.
  rewrite <- Rabs_mult in Hangle_error.
  rewrite Rmult_minus_distr_l in Hangle_error.
  rewrite <- Hku_val in Hangle_error at 1.
  rewrite <- Hku2_val_ in Hangle_error.
  generalize (Rabs_triang2 _ _ _ _ _ Hphi_error Hangle_error).
  clear Hphi_error Hangle_error.
  intro Hangle_error.
  rewrite (Rabs_right (2 * _)) in Hangle_error by lra.

  destruct (rememb (SARBackProj.contrib_bin_component N_RANGE_UPSAMPLED (fun i => B2R _ _ (data_r (Int.signed p) i)) (fun i => B2R _ _ (data_i (Int.signed p) i)))) as (contrib & Hcontrib).
  match type of Hprod_i_error with
      Rabs (_ - ?z) <= _ =>
      assert (z = snd (contrib (B2R _ _ phi_) (B2R _ _ bin))) as Hprod_i_eq
  end.
  {
    rewrite Hcontrib.
    rewrite SARBackProjFacts.contrib_bin_component_eq.
    rewrite Hbsc_r.
    rewrite Hbsc_i.
    reflexivity.
  }
  rewrite Hprod_i_eq in Hprod_i_error; clear Hprod_i_eq.

  match type of Hprod_r_error with
      Rabs (_ - ?z) <= _ =>
      assert (z = fst (contrib (B2R _ _ phi_) (B2R _ _ bin))) as Hprod_r_eq
  end.
  {
    rewrite Hcontrib.
    rewrite SARBackProjFacts.contrib_bin_component_eq.
    rewrite Hbsc_r.
    rewrite Hbsc_i.
    reflexivity.
  }
  rewrite Hprod_r_eq in Hprod_r_error; clear Hprod_r_eq.

  match type of Hbin_error with
      _ <= ?z =>
      generalize (SARBackProjFacts.contrib_bin_component_naive_propagation_bin_intro_2 N_RANGE_UPSAMPLED (fun i => B2R _ _ (data_r (Int.signed p) i))  (fun i => B2R _ _ (data_i (Int.signed p) i)) (B2R _ _ phi_) bin_ (B2R _ _ bin) z SARBounds.abs_data_dist)
  end.
  intro ERR.

  specialize_assert ERR.
  {
    lra.
  }
  specialize_assert ERR.
  {
    unfold abs_data_dist; lra.
  }
  specialize_assert ERR.
  {
    assumption.
  }
  specialize_assert ERR.
  {
    rewrite <- Fcore_Raux.Z2R_IZR.
    cbn.
    unfold bin_left, bin_right in *.
    lra.
  }
  specialize_assert ERR.
  {
    rewrite <- Fcore_Raux.Z2R_IZR.
    cbn.
    unfold bin_left, bin_right in *.
    apply Fcore_Raux.Rabs_le_inv in Hbin_error.
    lra.
  }
  specialize_assert ERR.
  {
    apply Hdata_r_invariant.
    omega.
  }
  specialize_assert ERR.
  {
    apply Hdata_i_invariant.
    omega.
  }
  generalize (ERR _ (or_intror _ (eq_refl _))).
  intro ERI.
  specialize (ERR _ (or_introl _ (eq_refl _))).
  clear Hbin_error.
  unfold abs_data_dist in ERR, ERI.
  match type of ERR with
      _ <= ?z =>
      interval_intro z upper as HB
  end.
  generalize (Rle_trans _ _ _ ERR HB); clear ERR.
  intro ERR.
  generalize (Rle_trans _ _ _ ERI HB); clear ERI.
  intro ERI.
  clear HB.  
  rewrite Hcontrib in Hprod_r_error, Hprod_i_error.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_r_error ERR).
  clear Hprod_r_error ERR; intro Hprod_r_error.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_i_error ERI);
  clear Hprod_i_error ERI; intro Hprod_i_error.

  match type of Hangle_error with
      _ <= ?z =>
      generalize (SARBackProjFacts.contrib_bin_component_propagation_angle N_RANGE_UPSAMPLED (fun i => B2R _ _ (data_r (Int.signed p) i)) (fun i => B2R _ _ (data_i (Int.signed p) i)) bin_ (2 * ku * norm_) (B2R _ _ phi_) z SARBounds.abs_data_max)
  end.
  intro EAR.
  specialize_assert EAR.
  {
    unfold abs_data_max. lra.
  }
  specialize_assert EAR.
  {
    intros i H.
    apply Hdata_r_invariant; omega.
  }
  specialize_assert EAR.
  {
    intros i H.
    apply Hdata_i_invariant; omega.
  }
  specialize_assert EAR.
  {
    assumption.
  }
  generalize (EAR _ (or_intror _ (eq_refl _))).
  intro EAI.
  specialize (EAR _ (or_introl _ (eq_refl _))).
  clear Hangle_error.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_r_error EAR).
  clear Hprod_r_error EAR; intro Hprod_r_error.
  generalize (Rabs_triang2 _ _ _ _ _ Hprod_i_error EAI);
  clear Hprod_i_error EAI; intro Hprod_i_error.
  rewrite <- Hcontrib in Hprod_r_error, Hprod_i_error. 
  assert (contrib (2 * ku * norm_) bin_ = SARBackProj.pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED (B2R _ _ (platpos_x (Int.signed p))) (B2R _ _ (platpos_y (Int.signed p))) (B2R _ _ (platpos_z (Int.signed p))) (fun i => B2R _ _ (data_r (Int.signed p) i)) (fun i => B2R _ _ (data_i (Int.signed p) i)) (B2R _ _ z0) SARBounds.R0 (/ SARBounds.dR)  SARBounds.ku SARBounds.dxdy (Z.to_nat (Int.signed x)) (Z.to_nat (Int.signed y))) as Hpulse_eq.
  {
    rewrite Hcontrib; clear Hcontrib.
    rewrite SARBackProjFacts.pulse'_eq.
    unfold SARBackProjFacts.pulse_.
    unfold SARBackProj.bin_.
    assert (   norm_ =
               sqrt
     ((B2R 53 1024 (platpos_x (Int.signed p)) -
       (- INR BP_NPIX_X / 2 + 1 / 2 + INR (Z.to_nat (Int.signed x))) * dxdy) *
      (B2R 53 1024 (platpos_x (Int.signed p)) -
       (- INR BP_NPIX_X / 2 + 1 / 2 + INR (Z.to_nat (Int.signed x))) * dxdy) +
      (B2R 53 1024 (platpos_y (Int.signed p)) -
       (- INR BP_NPIX_Y / 2 + 1 / 2 + INR (Z.to_nat (Int.signed y))) * dxdy) *
      (B2R 53 1024 (platpos_y (Int.signed p)) -
       (- INR BP_NPIX_Y / 2 + 1 / 2 + INR (Z.to_nat (Int.signed y))) * dxdy) +
      (B2R 53 1024 (platpos_z (Int.signed p)) - B2R 53 1024 z0) *
      (B2R 53 1024 (platpos_z (Int.signed p)) - B2R 53 1024 z0))
           ) as Hnorm'.
    {
      rewrite Hnorm_.
      f_equal.
      rewrite Hpx_.
      rewrite Hpy_.
      repeat rewrite Fcore_Raux.Z2R_IZR.
      repeat rewrite minus_IZR.
      replace (IZR 1) with 1 by reflexivity.
      repeat rewrite INR_IZR_INZ.
      repeat rewrite Z2Nat.id by tauto.
      field.
    }
    f_equal.
    {
      f_equal.
      assumption.
    }
    {
      rewrite Hbin_.
      f_equal.
      f_equal.
      assumption.
    }
  }
  rewrite Hpulse_eq in Hprod_r_error, Hprod_i_error.
  clear contrib Hcontrib Hpulse_eq.

  (* compute handier approximations of the bounds using CoqInterval *)
  unfold abs_data_max in Hprod_r_error, Hprod_i_error.
  match type of Hprod_r_error with
    _ <= ?zr =>
    interval_intro zr upper as GEr
  end.
  generalize (Rle_trans _ _ _ Hprod_r_error GEr).
  clear Hprod_r_error GEr. intro Hprod_r_error.
  match type of Hprod_i_error with
    _ <= ?zr =>
    interval_intro zr upper as GEi
  end.
  generalize (Rle_trans _ _ _ Hprod_i_error GEi).
  clear Hprod_i_error GEi. intro Hprod_i_error.

  (* compute the max of the two bounds using Psatz.lra *)
  match type of Hprod_r_error with
    ?Ur <= ?zr =>
    match type of Hprod_i_error with
        ?Ui <= ?zi =>
        let t z :=
            (assert (Ur <= z) as GEr by lra);
              (assert (Ui <= z) as GEi by lra)
        in
        (
          tryif
            (
              let K := fresh in
              (assert (zr <= zi) as K by lra);
              clear K
            )
          then
            t zi
          else
            t zr
        )
    end
  end;
  clear Hprod_r_error Hprod_i_error.

  (* erase the unneeded values of memory locations *)
  erase_Pval Hm b8 Int.zero.
  erase_Pval Hm b3 Int.zero.
  erase_Pval Hm b4 Int.zero.
  erase_Pval Hm b6 Int.zero.
  erase_Pval Hm b5 Int.zero.
  erase_Pval Hm b7 Int.zero.

  (* terminate the proof *)
  intros.
  solve_trivial.
  eassumption.
Defined.

Definition pulse_error' :=
  let (x, _) := f_sar_backprojection_pulse_contrib_body_correct' in 
  let '(y, _) := x in y
.

Definition pulse_error'_eq := $( field_eq pulse_error' )$ .

Definition pulse_error := $( match type of pulse_error'_eq with _ = ?z => exact z end )$ .

Definition pulse_range' :=
  let (x, _) := f_sar_backprojection_pulse_contrib_body_correct' in 
  let '(_, y) := x in y
.

Definition pulse_range'_eq := $( field_eq pulse_range' )$ .

Definition pulse_range := $( match type of pulse_range'_eq with _ = ?z => exact z end )$ .

Lemma f_sar_backprojection_pulse_contrib_body_correct:
  f_sar_backprojection_pulse_contrib_correct (pulse_error, pulse_range).
Proof.
  unfold pulse_error. rewrite <- pulse_error'_eq.
  unfold pulse_range. rewrite <- pulse_range'_eq.
  unfold pulse_error', pulse_range'.
  destruct f_sar_backprojection_pulse_contrib_body_correct'.
  destruct x.
  assumption.
Qed.
