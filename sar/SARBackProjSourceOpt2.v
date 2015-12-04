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
of the complex exponential.
*)

Require Export SARBackProjSourceOpt1 SARBackProjSourceNormOpt.
Require Export SepLogicVars.

Definition f_sar_backprojection_bin_sample_pre_correct BOUNDS :=
  let '(bin_error, bin_left, bin_right) := BOUNDS in
  forall
    `(HYPS: SARHypotheses)
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
    (Hx_int_range : (0 <= Int.signed x <= Z.of_nat BP_NPIX_X - 1)%Z )
    (px : float)
    (Hpx_range : px_left <= B2R 53 1024 px <= px_right)
    (Hpx_error : Rabs
                (B2R 53 1024 px -
                 (- Fcore_Raux.Z2R (Z.of_nat BP_NPIX_X - 1) +
                  2 * Fcore_Raux.Z2R (Int.signed x)) * 
                 B2R 53 1024 dxdy2) <= px_error)
    (Hpx_finite : is_finite 53 1024 px = true)
    (p : int)
    (contrib_r contrib_i : float)
    (image_r image_i : Z -> option (SepLogic.type_of_chunk Mfloat32))
    (Hp_int_range : (0 <= Int.signed p <= Z.of_nat N_PULSES - 1)%Z)
    (xdiff ydiff zdiff : float)
    (Hxdiff_finite : is_finite 53 1024 xdiff = true)
    (Hxdiff_range : xdiff_left <= B2R 53 1024 xdiff <= xdiff_right)
    (Hxdiff_error : Rabs
                   (B2R 53 1024 xdiff -
                    (B2R 53 1024 (platpos_x (Int.signed p)) - B2R 53 1024 px)) <=
                 xdiff_error)
    (Hydiff_finite : is_finite 53 1024 ydiff = true)
    (Hydiff_range : ydiff_left <= B2R 53 1024 ydiff <= ydiff_right)
    (Hydiff_error : Rabs
                   (B2R 53 1024 ydiff -
                    (B2R 53 1024 (platpos_y (Int.signed p)) - B2R 53 1024 py)) <=
                 ydiff_error)
    (Hzdiff_finite : is_finite 53 1024 zdiff = true)
    (Hzdiff_range : zdiff_left <= B2R 53 1024 zdiff <= zdiff_right)
    (Hzdiff_error : Rabs
                   (B2R 53 1024 zdiff -
                    (B2R 53 1024 (platpos_z (Int.signed p)) - B2R 53 1024 z0)) <=
                 zdiff_error)
    (m : mem)
    (norm : binary_float 53 1024)
    (Hnorm_finite : is_finite 53 1024 norm = true)
    (Hnorm_error : Rabs
                  (B2R 53 1024 norm -
                   sqrt
                     (B2R 53 1024 xdiff * B2R 53 1024 xdiff +
                      B2R 53 1024 ydiff * B2R 53 1024 ydiff +
                      B2R 53 1024 zdiff * B2R 53 1024 zdiff)) <= f_norm_error)
    (Hnorm_range : f_norm_left <= B2R 53 1024 norm <= f_norm_right)
    (Hm : holds
         ((((((((Pperm b3 (Int.unsigned Int.zero) Freeable
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
             (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
          Pval Mfloat64 b7 (Int.unsigned Int.zero) Freeable (Vfloat norm)
          ) m)
    (le0 : Maps.PTree.t val)
    (LE: env_le
     (set_opttemp None Vundef
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
                                    (_image_r, Vptr bir oir) :: Datatypes.nil)
                    (Maps.PTree.empty val)))))) le0)
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
       le0 m f_sar_backprojection_bin_sample_pre E0 le1 m1 out1 /\
     (forall le1_ : Maps.PTree.t val,
      env_le le1 le1_ ->
      out1 = Out_normal /\

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
   exists bin,
   holds
         ((((((((P ++
                    Parray_opt Mfloat32 (Int.unsigned Int.zero) image_r bir
                      (Int.unsigned oir) pir
                      (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                   Parray_opt Mfloat32 (Int.unsigned Int.zero) image_i bii
                     (Int.unsigned oii) pii
                     (Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))) ++
                  Pval Mfloat64 b7 (Int.unsigned Int.zero) Freeable
                    (Vfloat norm)) ++
              Pperm b3 (Int.unsigned Int.zero) Freeable
                (size_chunk_nat Mfloat32)) ++
             Pperm b4 (Int.unsigned Int.zero) Freeable
               (size_chunk_nat Mfloat32)) ++
            Pperm b5 (Int.unsigned Int.zero) Freeable
              (size_chunk_nat Mfloat32)) ++
           Pperm b6 (Int.unsigned Int.zero) Freeable
             (size_chunk_nat Mfloat32)) ++
          Pval Mfloat64 b8 (Int.unsigned Int.zero) Freeable (Vfloat bin)) m1
   /\
   is_finite 53 1024 bin = true
   /\
   bin_left <= B2R _ _ bin <= bin_right
   /\
   Rabs (B2R _ _ bin - (B2R 53 1024 norm - B2R 53 1024 r0) * / B2R 53 1024 dR0) <= bin_error
).

Set Printing Depth 2097152.

Lemma f_sar_backprojection_bin_sample_pre_body_correct' : { BOUNDS |
  f_sar_backprojection_bin_sample_pre_correct BOUNDS }.
Proof.
  eexists (_, _, _).
  unfold f_sar_backprojection_bin_sample_pre_correct.
  intros data_r data_i P bdr odr bdi odi bpx opx platpos_x bpy opy.
  intros platpos_y bpz opz platpos_z bdR odR dR0 bdxdy odxdy dxdy0 bku oku ku0 br0 or0.
  intros r0 bz0 oz0 z0 bir oir pir bii oii pii HYPS b3 b4 b5 b6 b7 b8 ku2.
  intros dxdy2 dR_inv Hku2_finite Hku2_val Hdxdy2_finite Hdxdy2_val HdR_inv_finite.
  intros HdR_inv_error HdR_inv_range y Hy_int_range py Hpy_finite Hpy_error Hpy_range.
  intros x Hx_int_range px Hpx_range Hpx_error Hpx_finite p contrib_r contrib_i.
  intros image_r image_i Hp_int_range xdiff ydiff zdiff Hxdiff_finite Hxdiff_range.
  intros Hxdiff_error Hydiff_finite Hydiff_range Hydiff_error Hzdiff_finite.
  intros Hzdiff_range Hzdiff_error m norm Hnorm_finite Hnorm_error.
  intros Hnorm_range Hm le0 LE ge.
  unfold f_sar_backprojection_bin_sample_pre.
  inversion HYPS.
  revert le0 LE.

  apply exec_Sassign_exists_lifted.
  repeat ClightSep2.run.
  eval_lvalue_exists_Evar.
  apply deepest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  eval_Elvalue_exists.
  eval_lvalue_exists_Evar.
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
  Pval_solve.
  apply deepest_expr_exists.
  intros i Hi.
  vm_compute in Hi.
  subst i.
  solve_trivial.
  eval_Elvalue_exists.
  repeat ClightSep2.run.
  assert (holds P m) as HP by 
 let rec t :=
        match constr:tt with
          | _ => assumption
          | _ => (apply holds_weak_left in Hm; t)
          | _ => (apply holds_weak_right in Hm; t)
        end
    in t.
  rewrite Hr0 by assumption.
  solve_trivial.
  unfold SARBounds.R0 in Hr0_val.
  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vfloat_exists.
  (* here comes the framework into play! *)
  C_to_float_as bin Hbin.
  Transparent Float.of_bits Int64.repr.
  unfold f_norm_left, f_norm_right, dR_inv_left, dR_inv_right in *.
  let t _ :=
      (try rewrite Hr0_val);
      interval_
  in
  compute_fval_as' t Hbin Hbin_finite Hbin_val.
  destruct (rememb (B2R _ _ norm - B2R _ _ r0)) as (d & Hd).
  rewrite <- Hd in Hbin_val.
  destruct (rememb (B2R _ _ bin - d * / B2R _ _ dR0)) as (e & He).
  generalize He. intro He_.
  rewrite <- Hbin_val in He.
  try rewrite Rmult_assoc in He.
  try rewrite <- Rmult_minus_distr_l in He.
  subst d.
  Require Export Interval.Interval_tactic.
  rewrite Hr0_val in He.
  rewrite HdR_val in He.
  unfold dR in He.
  match type of He with
      _ = ?z =>
      interval_intro (Rabs z) upper with (i_prec 96)  as Hbin_error
  end.
  rewrite <- He in Hbin_error.
  clear He.
  subst e.
  rewrite Hr0_val in Hbin_val.
  match type of Hbin_val with
      ?z = _ =>
      interval_intro z with (i_prec 96) as Hbin_range
  end.
  rewrite Hbin_val in Hbin_range.

  solve_trivial.
  repeat ClightSep2.run.
  clear HP.
  holds_storev_solve.
  split.
  {
    constructor.
  }
  intros m Hm.
  unfold set_opttemp.
  intros le1 H.
  solve_trivial.
  eassumption.
Defined.

Definition bin_error' :=
  let (x, _) := f_sar_backprojection_bin_sample_pre_body_correct' in 
  let '(y, _, _) := x in y
.

Definition bin_error'_eq := $( field_eq bin_error' )$ .

Definition bin_error := $( match type of bin_error'_eq with _ = ?z => exact z end )$ .

Definition bin_left' :=
  let (x, _) := f_sar_backprojection_bin_sample_pre_body_correct' in 
  let '(_, y, _) := x in y
.

Definition bin_left'_eq := $( field_eq bin_left' )$ .

Definition bin_left := $( match type of bin_left'_eq with _ = ?z => exact z end )$ .

Definition bin_right' :=
  let (x, _) := f_sar_backprojection_bin_sample_pre_body_correct' in 
  let '(_, _, y) := x in y
.

Definition bin_right'_eq := $( field_eq bin_right' )$ .

Definition bin_right := $( match type of bin_right'_eq with _ = ?z => exact z end )$ .

Lemma f_sar_backprojection_bin_sample_pre_body_correct:
  f_sar_backprojection_bin_sample_pre_correct (bin_error, bin_left, bin_right).
Proof.
  unfold bin_error. rewrite <- bin_error'_eq.
  unfold bin_left. rewrite <- bin_left'_eq.
  unfold bin_right. rewrite <- bin_right'_eq.
  unfold bin_error', bin_left', bin_right'.
  destruct f_sar_backprojection_bin_sample_pre_body_correct'.
  destruct x.
  destruct p.
  assumption.
Qed.

Definition bin_sample_component N_RANGE_UPSAMPLED data bin :=
  if (Fcore_Raux.Rle_bool 0 bin) && (Fcore_Raux.Rlt_bool bin (IZR (N_RANGE_UPSAMPLED - 1)))
  then
    SARBackProj.interpol data bin
  else
    0
  .

Lemma bin_sample_component_eq N_RANGE_UPSAMPLED data bin:
  bin_sample_component N_RANGE_UPSAMPLED data bin =
  SARBackProj.bin_sample_component N_RANGE_UPSAMPLED data bin.
Proof.
  unfold bin_sample_component, SARBackProj.bin_sample_component.
  rewrite Rle_dec_to_bool.
  rewrite Rlt_dec_to_bool.
  reflexivity.
Qed.

Import List.

Definition f_bin_sample_correct BOUNDS
           ge fn_bin_sample
  :=
    let '(f_bin_sample_error, f_bin_sample_left, f_bin_sample_right) := BOUNDS in
    type_of_fundef fn_bin_sample =
    Ctypes.Tfunction
      (Ctypes.Tcons (tptr tfloat)
                    (Ctypes.Tcons (tptr tfloat)
                                  (Ctypes.Tcons (tptr tfloat)
                                                (Ctypes.Tcons (tptr tfloat)
                                                              (Ctypes.Tcons (tptr tdouble) Ctypes.Tnil)))))
      tvoid
      AST.cc_default
    /\
    forall
       bin
      (Hbin_finite: is_finite _ _ bin = true)
      data_r
      (Hdata_r_invariant: data_invariant data_r)
      data_i
      (Hdata_i_invariant: data_invariant data_i)
      P
      bbi obi
      (Hbi: forall m,
              holds P m ->
              Mem.loadv Mfloat64 m (Vptr bbi obi) = Some (Vfloat bin))
      bdr odr
      (Hdr:
         forall i,
           (0 <= i < N_RANGE_UPSAMPLED)%Z ->
           forall m,
             holds P m ->
             Mem.loadv Mfloat32 m (Vptr bdr (Int.add odr (Int.mul (Int.repr (size_chunk Mfloat32)) (Int.repr i)))) = Some (Vsingle (data_r i)))
      bdi odi
      (Hdi:
         forall i,
           (0 <= i < N_RANGE_UPSAMPLED)%Z ->
           forall m,
             holds P m ->
             Mem.loadv Mfloat32 m (Vptr bdi (Int.add odi (Int.mul (Int.repr (size_chunk Mfloat32)) (Int.repr i)))) = Some (Vsingle (data_i i)))
      psr
      (Hpsr: perm_order psr Writable)
      psi
      (Hpsi: perm_order psi Writable)
      bsr osr
      bsi osi
      (osr_align: (align_chunk Mfloat32 | Int.unsigned osr)%Z)
      (osi_align: (align_chunk Mfloat32 | Int.unsigned osi)%Z)
      m
      (Hmem: holds
               (P
                  ++ Pperm bsr (Int.unsigned osr) psr (size_chunk_nat Mfloat32)
                  ++ Pperm bsi (Int.unsigned osi) psi (size_chunk_nat Mfloat32))
               m)
    ,
      let st0 := (Callstate fn_bin_sample
                            (Vptr bsr osr ::
                            Vptr bsi osi ::
                            Vptr bdr odr ::
                            Vptr bdi odi ::
                            Vptr bbi obi ::
                            nil)
                            Kstop
                            m) in
      exists s ,
        star Clight.step2 ge
             st0
             E0
             s /\
        exists m',
          s = Returnstate Vundef Kstop m'
          /\
          exists sample_r,
            exists sample_i,
              (is_finite _ _ sample_r = true /\ is_finite _ _ sample_i = true) /\
              (Rabs (B2R _ _ sample_r - SARBackProj.bin_sample_component N_RANGE_UPSAMPLED (fun i => B2R _ _ (data_r i))  (B2R _ _ bin)) <= f_bin_sample_error  /\
               Rabs (B2R _ _ sample_i - SARBackProj.bin_sample_component N_RANGE_UPSAMPLED (fun i => B2R _ _ (data_i i))  (B2R _ _ bin)) <= f_bin_sample_error) /\
              (f_bin_sample_left <= B2R _ _ sample_r <= f_bin_sample_right /\
               f_bin_sample_left <= B2R _ _ sample_i <= f_bin_sample_right
              ) /\
              holds
                (P
                   ++ Pval Mfloat32 bsr (Int.unsigned osr) psr (Vsingle sample_r)
                   ++ Pval Mfloat32 bsi (Int.unsigned osi) psi (Vsingle sample_i))
                m'.

Theorem f_bin_sample_body_correct' : { BOUNDS |
forall ge,
f_bin_sample_correct BOUNDS ge (Clight.Internal (f_bin_sample N_RANGE_UPSAMPLED))
}.
Proof.
  eexists (_, _, _).
  esplit.
  split; auto.
  intros bin Hbin_finite data_r Hdata_r_invariant data_i Hdata_i_invariant P bbi obi.
  intros Hbi bdr odr Hdr bdi odi Hdi psr Hpsr psi Hpsi bsr osr bsi osi osr_align.
  intros osi_align m Hmem st0.

  destruct Hdata_r_invariant as (Hdata_r_finite & Hdata_r_range & _).
  destruct Hdata_i_invariant as (Hdata_i_finite & Hdata_i_range & _).
  
  unfold abs_data_min, abs_data_max in Hdata_r_range, Hdata_i_range.

  unfold st0; clear st0.
  apply star_exists_step.
  call_fn.
  simpl fn_body.
  repeat ClightSep2.run.

  assert (holds P m)
    as HP
  by let rec t :=
        match constr:tt with
          | _ => assumption
          | _ => (apply holds_weak_left in Hmem; t)
          | _ => (apply holds_weak_right in Hmem; t)
        end
    in t.
  rewrite Hbi by assumption.
  solve_trivial.

  repeat ClightSep2.run.

  apply step_ifthenelse2.

  apply eval_exists_Ebinop.
  repeat ClightSep2.run.

  apply eval_exists_Econst_int.
  solve_trivial.

  simpl typeof.
  rewrite bool_val_int_of_bool.
  solve_trivial.

  apply eval_exists_Ebinop.
  repeat ClightSep2.run.

  apply eval_exists_Ebinop.
  apply eval_exists_Econst_int.
  apply eval_exists_Econst_int.
  solve_trivial.
  rewrite bool_val_int_of_bool.
  solve_trivial.
  destruct (
      if_bool_eq_dec
        (Float.cmp Cge bin (cast_int_float Signed (Int.repr 0)) &&
                   Float.cmp Clt bin
                   (cast_int_float Signed
                                   (Int.sub (Int.repr N_RANGE_UPSAMPLED) (Int.repr 1))))%bool
    ) as (COND & DEC & COND_EQ & LEB_DEC).
  rewrite LEB_DEC ; clear LEB_DEC.
  rewrite Bool.andb_true_iff in COND_EQ.
  cbn in COND_EQ.
  rewrite <- (Float.cmp_swap Cge) in COND_EQ.
  simpl swap_comparison in COND_EQ.
  Transparent Float.cmp.
  unfold Float.cmp in COND_EQ.
  rewrite Bcompare_correct in COND_EQ by auto.
  rewrite Bcompare_correct in COND_EQ by auto.
  rewrite Rcompare_Rlt_true_iff in COND_EQ.
  rewrite Rcompare_Rle_true_iff in COND_EQ.
  Transparent Float.of_int Int.sub Int.repr.
  simpl B2R in COND_EQ.
  unfold Fcore_defs.F2R in COND_EQ.
  cbn in COND_EQ.
  destruct DEC as [LTB | N_LTB].
  {
    rewrite COND_EQ in LTB ; clear COND_EQ.
    destruct LTB as (GEB & LTB).
    generalize (Int_part_nonneg _ GEB). intro GEB_I.
    assert (B2R _ _ bin < Fcore_Raux.Z2R (N_RANGE_UPSAMPLED - 1)) as LTB_I' by (cbn; lra).
    rewrite Fcore_Raux.Z2R_IZR in LTB_I'.
    destruct (base_Int_part (B2R _ _ bin)) as [LTB_K _].
    generalize (Rle_lt_trans _ _ _ LTB_K LTB_I').
    clear LTB_K LTB_I'.
    intro LTB_I.
    apply lt_IZR in LTB_I.

    repeat ClightSep2.run.

    apply eval_exists_Ecast.
    repeat ClightSep2.run.
    simpl typeof.
    apply sem_cast_double_int_exists.
    Transparent Float.to_int.
    unfold Float.to_int.
    rewrite Fappli_IEEE_extra.ZofB_range_correct.
    rewrite Hbin_finite.
    rewrite Fcore_Raux.Ztrunc_floor by assumption.
    repeat rewrite Zfloor_int_part.
    rewrite Z_leb_Rle_bool.
    rewrite Z_leb_Rlt_bool.
    simpl Fcore_Raux.Z2R.
    rewrite Fcore_Raux.Rle_bool_true by lra.
    rewrite Fcore_Raux.Rlt_bool_true by lra.
    solve_trivial.

    repeat ClightSep2.run.

    apply deepest_expr_exists.
    intros i Hi.
    vm_compute in Hi.
    subst i.
    solve_trivial.

    apply eval_exists_Ecast.
    repeat ClightSep2.run.

    simpl cast_int_float.
    apply Float_of_int_forall.
    apply signed_repr_forall.
    apply asplit.
    {
      cbn.
      replace 0 with (IZR 0) in GEB by reflexivity.
      apply RAux.IZR_Int_part in GEB.
      split.
      {
        omega.
      }
      apply le_IZR.
      eapply Rle_trans.
      {
        eapply base_Int_part.
      }
      rewrite <- Fcore_Raux.Z2R_IZR.
      simpl.
      lra.
    }
    intros SIGNED .
    cbn in SIGNED.
    intros u Hu_finite Hu_val.
    apply deepest_expr_exists.
    intros i Hi.
    vm_compute in Hi.
    subst i.
    solve_trivial.

    apply eval_expr_exists_filter_domain.
    apply eval_expr_exists_filter_float.
    apply Vfloat_exists.
    (* here comes the framework into play! *)
    C_to_float_as dx Hdx.  
    cbn in Hdx.
    unfold FPLang.type_lub, FPLang.BMINUS, FPLang.BINOP, FPLang.fprec, FPLang.fprec_gt_0 in Hdx.
    cbn in Hdx.
    rewrite Fcore_Raux.Z2R_IZR in Hu_val.
    generalize (int_part_sterbenz
    _ _ _ _ Hbin_finite Hu_finite Hu_val GEB _ _ _ _ _ Hdx).
    clear Hdx.
    destruct 1 as (Hdx_finite & Hdx_val).

    assert (0 <= B2R _ _ dx <= 1) as Hdx_range.
    {
      rewrite Hdx_val.
      generalize (base_Int_part (B2R _ _ bin)).
      lra.
    }

    apply eval_expr_exists_filter_domain.
    apply eval_expr_exists_filter_float.
    apply Vsingle_exists.
    (* here comes the framework into play! *)
    C_to_float_as dxf Hdxf.
    compute_fval_as Hdxf Hdxf_finite Hdxf_val.

    repeat ClightSep2.run.

    match goal with
        |- exists v2,
             eval_expr _ _ ?te _ ?e v2 /\ _ =>
        match e with
            context [Ederef ?u ?v] =>
            let i := (eval cbn in (next_index xH (Maps.PTree.elements te))) in
            let e1 := constr:(Ederef u v) in
            let e2 := pattern_expr i e1 e in
            apply (subst_expr_exists e1 e2 i)
        end
    end.
    simpl typeof.
    solve_trivial.

    apply shallowest_expr_exists.
    intros i Hi.
    vm_compute in Hi.
    subst i.
    solve_trivial.

    apply eval_exists_Ebinop.
    repeat ClightSep2.run.

    replace (sizeof ge tfloat) with (Memdata.size_chunk Mfloat32) by reflexivity.
    rewrite Hdr by (assumption || omega).
    solve_trivial.

    generalize (Hdata_r_finite (Int_part (B2R _ _ bin)) $( omega )$ ).
    intro Hdata_r_bin_finite.
    destruct (Hdata_r_range (Int_part (B2R _ _ bin)) $( omega )$ ).

    match goal with
        |- exists v2,
             eval_expr _ _ ?te _ ?e v2 /\ _ =>
        match e with
            context [Ederef ?u ?v] =>
            let i := (eval cbn in (next_index xH (Maps.PTree.elements te))) in
            let e1 := constr:(Ederef u v) in
            let e2 := pattern_expr i e1 e in
            apply (subst_expr_exists e1 e2 i)
        end
    end.
    simpl typeof.
    solve_trivial.

    apply shallowest_expr_exists.
    intros i Hi.
    vm_compute in Hi.
    subst i.
    solve_trivial.

    apply eval_exists_Ebinop.
    repeat ClightSep2.run.
    apply eval_exists_Ebinop.
    repeat ClightSep2.run.
    apply eval_exists_Econst_int.
    solve_trivial.
    simpl typeof.
    repeat ClightSep2.run.

    rewrite add_repr.

    replace (sizeof ge tfloat) with (Memdata.size_chunk Mfloat32) by reflexivity.
    rewrite Hdr by (assumption || omega).
    solve_trivial.

    generalize (Hdata_r_finite (Int_part (B2R _ _ bin) + 1)%Z $( omega )$ ).
    intro Hdata_r_bin_1_finite.
    destruct (Hdata_r_range (Int_part (B2R _ _ bin) + 1)%Z $( omega )$ ).

    apply eval_expr_exists_filter_domain.
    apply eval_expr_exists_filter_float.
    apply Vsingle_exists.
    (* here comes the framework into play! *)
    C_to_float_as sample_r Hsample_r.
    Transparent Float32.of_bits.
    let t _ :=
        (try rewrite <- Hdxf_val);
          interval_
    in
    compute_fval_as' t Hsample_r Hsample_r_finite Hsample_r_val.
    rewrite <- Hdxf_val in Hsample_r_val.
    solve_trivial.

    repeat ClightSep2.run.
    clear HP.
    holds_storev_solve.
    intros m Hmem.

    assert (holds P m) as HP by 
                           let rec t :=
                               match constr:tt with
                                 | _ => assumption
                                 | _ => (apply holds_weak_left in Hmem; t)
                                 | _ => (apply holds_weak_right in Hmem; t)
                               end
                           in t.

    repeat ClightSep2.run.

    match goal with
        |- exists v2,
             eval_expr _ _ ?te _ ?e v2 /\ _ =>
        match e with
            context [Ederef ?u ?v] =>
            let i := (eval cbn in (next_index xH (Maps.PTree.elements te))) in
            let e1 := constr:(Ederef u v) in
            let e2 := pattern_expr i e1 e in
            apply (subst_expr_exists e1 e2 i)
        end
    end.

    simpl typeof.
    solve_trivial.

    apply shallowest_expr_exists.
    intros i Hi.
    vm_compute in Hi.
    subst i.
    solve_trivial.

    apply eval_exists_Ebinop.
    repeat ClightSep2.run.

    rewrite Hdi by (assumption || omega).
    solve_trivial.

    generalize (Hdata_i_finite (Int_part (B2R _ _ bin)) $( omega )$ ).
    intro Hdata_i_bin_finite.
    destruct (Hdata_i_range (Int_part (B2R _ _ bin)) $( omega )$ ).

    match goal with
        |- exists v2,
             eval_expr _ _ ?te _ ?e v2 /\ _ =>
        match e with
            context [Ederef ?u ?v] =>
            let i := (eval cbn in (next_index xH (Maps.PTree.elements te))) in
            let e1 := constr:(Ederef u v) in
            let e2 := pattern_expr i e1 e in
            apply (subst_expr_exists e1 e2 i)
        end
    end.

    simpl typeof.
    solve_trivial.

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
    apply eval_exists_Econst_int.
    solve_trivial.
    simpl typeof.
    apply eval_exists_Ebinop.
    repeat ClightSep2.run.

    rewrite add_repr.

    rewrite Hdi by (assumption || omega).
    solve_trivial.

    generalize (Hdata_i_finite (Int_part (B2R _ _ bin) + 1)%Z $( omega )$ ).
    intro Hdata_i_bin_1_finite.
    destruct (Hdata_i_range (Int_part (B2R _ _ bin) + 1)%Z $( omega )$ ).

    apply eval_expr_exists_filter_domain.
    apply eval_expr_exists_filter_float.
    apply Vsingle_exists.
    (* here comes the framework into play! *)
    C_to_float_as sample_i Hsample_i.
    Transparent Float32.of_bits.
    let t _ :=
        (try rewrite <- Hdxf_val);
          interval_
    in
    compute_fval_as' t Hsample_i Hsample_i_finite Hsample_i_val.
    rewrite <- Hdxf_val in Hsample_i_val.
    solve_trivial.

    repeat ClightSep2.run.

    clear HP.
    holds_storev_solve.
    intros m Hmem.

    repeat ClightSep2.run.

    apply star_exists_refl.
    solve_trivial.

    exists sample_r, sample_i.
    split; auto.
    split.
    {
      repeat rewrite <- bin_sample_component_eq.
      unfold bin_sample_component.
      rewrite Fcore_Raux.Rle_bool_true by lra.
      rewrite <- Fcore_Raux.Z2R_IZR.
      simpl Fcore_Raux.Z2R.
      rewrite Fcore_Raux.Rlt_bool_true by lra.
      simpl.
      unfold SARBackProj.interpol.
      rewrite <- Hsample_r_val.
      rewrite <- Hsample_i_val.
      rewrite <- Hdx_val.
      match goal with
          |- context [ ?a * / ?a ] =>
          replace (a * / a) with 1 by field
      end.

      split.

      {
        match goal with
            |- Rabs ?z <= _ =>
            destruct (eqpivot z) as (v & LV & RV)
        end.
        rewrite LV; clear LV.
        ring_simplify in RV.
        match type of RV with
            v = ?z =>
            interval_intro z with (i_prec 48) as L;
              rewrite <- RV in L;
              clear RV
        end.
        interval_intro (Rabs v) as AL.
        destruct AL as (_ & AL).
        eexact AL.
      }
      match goal with
          |- Rabs ?z <= _ =>
          destruct (eqpivot z) as (v & LV & RV)
      end.
      rewrite LV; clear LV.
      ring_simplify in RV.
      rewrite RV; clear RV.
      interval with (i_prec 48).
    }

    split.
    {
      match type of Hsample_i_val with
          ?z = _ =>
          interval_intro z as Hsample_i_range
      end.
      rewrite Hsample_i_val in Hsample_i_range.
      match type of Hsample_r_val with
          ?z = _ =>
          interval_intro z as Hsample_r_range
      end.
      rewrite Hsample_r_val in Hsample_r_range.
      split; eassumption.
    }

    revert Hmem.
    apply holds_list_comm_aux.
    apply count_occ_list_comm.
    intro; repeat rewrite count_occ_app; omega.
  }

  (* FALSE *)
  rewrite COND_EQ in N_LTB ; clear COND_EQ.
  repeat ClightSep2.run.

  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  (* here comes the framework into play! *)
  C_to_float_as fzero Hfzero.
  vm_compute in Hfzero.
  subst fzero.
  solve_trivial.

  repeat ClightSep2.run.

  clear HP.
  holds_storev_solve.
  intros m Hmem.

  repeat ClightSep2.run.

  apply eval_expr_exists_filter_domain.
  apply eval_expr_exists_filter_float.
  apply Vsingle_exists.
  (* here comes the framework into play! *)
  C_to_float_as fzero Hfzero.
  vm_compute in Hfzero.
  subst fzero.
  solve_trivial.

  repeat ClightSep2.run.

  holds_storev_solve.
  intros m Hmem.

  repeat ClightSep2.run.

  apply star_exists_refl.
  solve_trivial.

  exists (B754_zero _ _ false), (B754_zero _ _ false).
  split; auto.

  split.
  {
    repeat rewrite <- bin_sample_component_eq.
    unfold bin_sample_component.
    destruct (
        Fcore_Raux.Rle_bool 0 (B2R 53 1024 bin) &&
                            Fcore_Raux.Rlt_bool (B2R 53 1024 bin) (IZR (N_RANGE_UPSAMPLED - 1))
      ) eqn:BOOL.
    {
      rewrite Bool.andb_true_iff in BOOL.
      rewrite Rle_bool_iff in BOOL.
      rewrite Rlt_bool_iff in BOOL.
      rewrite <- Fcore_Raux.Z2R_IZR in BOOL.
      simpl Fcore_Raux.Z2R in BOOL.
      lra.
    }
    simpl.
    replace (0 - 0) with 0 by ring.
    rewrite Rabs_R0.
    lra.
  }

  split.
  {
    cbn. lra.
  }

  revert Hmem.
  apply holds_list_comm_aux.
  apply count_occ_list_comm.
  intro; repeat rewrite count_occ_app; omega.
  
Defined.

Definition f_bin_sample_error' :=
 let (x, _) := f_bin_sample_body_correct' in 
 let '(y, _, _) := x in y.

Definition f_bin_sample_error'_eq := 
  $( field_eq f_bin_sample_error' )$ .

Definition f_bin_sample_error := 
  $( match type of f_bin_sample_error'_eq with _ = ?z => exact z end )$ .

Definition f_bin_sample_left' :=
 let (x, _) := f_bin_sample_body_correct' in 
 let '(_, y, _) := x in y.

Definition f_bin_sample_left'_eq := 
  $( field_eq f_bin_sample_left' )$ .

Definition f_bin_sample_left := 
  $( match type of f_bin_sample_left'_eq with _ = ?z => exact z end )$ .

Definition f_bin_sample_right' :=
 let (x, _) := f_bin_sample_body_correct' in 
 let '(_, _, y) := x in y.

Definition f_bin_sample_right'_eq := 
  $( field_eq f_bin_sample_right' )$ .

Definition f_bin_sample_right := 
  $( match type of f_bin_sample_right'_eq with _ = ?z => exact z end )$ .


Lemma f_bin_sample_body_correct ge:
  f_bin_sample_correct (f_bin_sample_error, f_bin_sample_left, f_bin_sample_right) ge (Clight.Internal (f_bin_sample N_RANGE_UPSAMPLED)).
Proof.
  unfold f_bin_sample_error.
  rewrite <- f_bin_sample_error'_eq.
  unfold f_bin_sample_left.
  rewrite <- f_bin_sample_left'_eq.
  unfold f_bin_sample_right.
  rewrite <- f_bin_sample_right'_eq.
  unfold f_bin_sample_error' .
  unfold f_bin_sample_left' .
  unfold f_bin_sample_right' .
  destruct f_bin_sample_body_correct'.
  destruct x.
  destruct p.
  auto.
Qed.
