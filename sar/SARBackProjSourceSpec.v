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

Specifications of SAR backprojection absolute error against which to
verify our C implementation. Summarizes the hypotheses on the input
data. The specification is parameterized over the error bound.
*)

Require Export Memory.
Require Export SARBackProjSourceDecomp.
Open Scope R_scope.

Require Export Flocq.Appli.Fappli_IEEE.

Definition data_invariant (data: _ -> Floats.float32) :=
  (
    forall i,
      (0 <= i < N_RANGE_UPSAMPLED)%Z ->
      is_finite _ _ (data i) = true
  ) /\ (
    forall i,
      (0 <= i < N_RANGE_UPSAMPLED)%Z ->
      abs_data_min <= Rabs (B2R _ _ (data i)) <= abs_data_max
  ) /\ (
    forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z ->  Rabs (B2R _ _ (data (i + 1)%Z) - B2R _ _ (data i)) <= SARBounds.abs_data_dist
  ).

Set Printing Depth 2097152.

(* Summary of hypotheses on the input data *)

Inductive SARHypotheses
          (data_r: _) (data_i: _)
          (P: _)
          (bdr: _) (odr: _)
          (bdi: _) (odi: _)
          (bpx: _) (opx: _) (platpos_x: _)
          (bpy: _) (opy: _) (platpos_y: _)
          (bpz: _) (opz: _) (platpos_z: _)
          (bdR: _) (odR: _) (dR: _)
          (bdxdy: _) (odxdy: _) (dxdy: _)
          (bku: _) (oku: _) (ku: _)
          (br0: _) (or0: _) (r0: _)
          (bz0: _) (oz0: _) (z0: _)
          (bir: Values.block) oir pir
          (bii: Values.block) oii pii

: Prop := SARHypothesesIntro

      (** Hint: read-only data does not need to be represented in separation logic.
          Everything should be provable from the framed property P. The statement
          here implies that those locations are disjoint from the data areas
          to which SAR backprojection will write.
       *)

      (Hdata_r_invariant:
         forall p,
           (0 <= p < Z.of_nat N_PULSES)%Z ->
           data_invariant (data_r p))
      (Hdata_i_invariant: 
         forall p,
           (0 <= p < Z.of_nat N_PULSES)%Z ->
           data_invariant (data_i p))

      (Hdata_r:
         forall p,
           (0 <= p < Z.of_nat N_PULSES)%Z ->
           forall i,
             (0 <= i < N_RANGE_UPSAMPLED)%Z ->
           forall m,
             holds P m ->
             Mem.loadv Mfloat32 m (Vptr bdr (Int.add (Int.add odr (Int.mul (Int.repr (size_chunk Mfloat32 * N_RANGE_UPSAMPLED)) (Int.repr p))) (Int.mul (Int.repr (size_chunk Mfloat32)) (Int.repr i)))) = Some (Vsingle (data_r p i)))

      (Hdata_i:
         forall p,
           (0 <= p < Z.of_nat N_PULSES)%Z ->
           forall i,
             (0 <= i < N_RANGE_UPSAMPLED)%Z ->
           forall m,
             holds P m ->
             Mem.loadv Mfloat32 m (Vptr bdi (Int.add (Int.add odi (Int.mul (Int.repr (size_chunk Mfloat32 * N_RANGE_UPSAMPLED)) (Int.repr p))) (Int.mul (Int.repr (size_chunk Mfloat32)) (Int.repr i)))) = Some (Vsingle (data_i p i)))

      (Hplatpos_x_array:
         forall p,
           (0 <= p < Z.of_nat N_PULSES)%Z ->
           forall m,
             holds P m ->
             Mem.loadv Mfloat64 m (Vptr bpx (Int.add opx (Int.mul (Int.repr (size_chunk Mfloat64)) (Int.repr p)))) = Some (Vfloat (platpos_x p)))
      (platpos_x_finite: forall i, (0 <= i < Z.of_nat N_PULSES)%Z ->
                                   is_finite _ _ (platpos_x i) = true)
      (platpos_x_range: forall i, (0 <= i < Z.of_nat N_PULSES)%Z ->
                                  SARBounds.platpos_x_min <= B2R _ _ (platpos_x i) <= SARBounds.platpos_x_max)

      (Hplatpos_y_array:
         forall p,
           (0 <= p < Z.of_nat N_PULSES)%Z ->
           forall m,
             holds P m ->
             Mem.loadv Mfloat64 m (Vptr bpy (Int.add opy (Int.mul (Int.repr (size_chunk Mfloat64)) (Int.repr p)))) = Some (Vfloat (platpos_y p)))
      (platpos_y_finite: forall i, (0 <= i < Z.of_nat N_PULSES)%Z ->
                is_finite _ _ (platpos_y i) = true)
      (platpos_y_range: forall i, (0 <= i < Z.of_nat N_PULSES)%Z ->
                SARBounds.platpos_y_min <= B2R _ _ (platpos_y i) <= SARBounds.platpos_y_max)

      (Hplatpos_z_array:
         forall p,
           (0 <= p < Z.of_nat N_PULSES)%Z ->
           forall m,
             holds P m ->
             Mem.loadv Mfloat64 m (Vptr bpz (Int.add opz (Int.mul (Int.repr (size_chunk Mfloat64)) (Int.repr p)))) = Some (Vfloat (platpos_z p)))
      (platpos_z_finite: forall i, (0 <= i < Z.of_nat N_PULSES)%Z ->
                is_finite _ _ (platpos_z i) = true)
      (platpos_z_range: forall i, (0 <= i < Z.of_nat N_PULSES)%Z ->
                SARBounds.platpos_z_min <= B2R _ _ (platpos_z i) <= SARBounds.platpos_z_max)

      (HdR: forall m,
              holds P m ->
              Mem.loadv Mfloat64 m (Vptr bdR odR) = Some (Vfloat dR))
      (HdR_finite: is_finite _ _ dR = true)
      (HdR_val: B2R _ _ dR = SARBounds.dR)

      (Hdxdy: forall m,
                holds P m ->
                Mem.loadv Mfloat64 m (Vptr bdxdy odxdy) = Some (Vfloat dxdy))
      (Hdxdy_finite: is_finite _ _ dxdy = true)
      (Hdxdy_val: B2R _ _ dxdy = SARBounds.dxdy)

      (Hku: forall m,
              holds P m ->
              Mem.loadv Mfloat64 m (Vptr bku oku) = Some (Vfloat ku))
      (Hku_finite: is_finite _ _ ku = true)
      (Hku_val: B2R _ _ ku = SARBounds.ku)

      (Hr0: forall m,
              holds P m ->
              Mem.loadv Mfloat64 m (Vptr br0 or0) = Some (Vfloat r0))
      (Hr0_finite: is_finite _ _ r0 = true)
      (Hr0_val: B2R _ _ r0 = SARBounds.R0)

      (Hz0: forall m,
              holds P m ->
              Mem.loadv Mfloat64 m (Vptr bz0 oz0) = Some (Vfloat z0))
      (Hz0_finite: is_finite _ _ z0 = true)
      (Hz0_val: SARBounds.z0_low <= B2R _ _ z0 <= SARBounds.z0_high)

      (Hoir_align: (align_chunk Mfloat32 | Int.unsigned oir)%Z)
      (Hoir_bound: (Int.unsigned oir + size_chunk Mfloat32 * Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y <= Int.max_unsigned)%Z)
      (Hpir: perm_order pir Writable)
         
      (Hoii_align: (align_chunk Mfloat32 | Int.unsigned oii)%Z)
      (Hoii_bound: (Int.unsigned oii + size_chunk Mfloat32 * Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y <= Int.max_unsigned)%Z)
      
      (Hpii: perm_order pii Writable)

.

Existing Class SARHypotheses.

Require SARBackProj.
Import List.

Definition sar_backprojection_spec
           ge
           fn_sar_backprojection
           pixel_bound
  :=
    type_of_fundef fn_sar_backprojection =
    Ctypes.Tfunction
      (typelist_of_list_type
         (
           tptr (tarray tfloat (Z.of_nat BP_NPIX_X)) ::
           tptr (tarray tfloat (Z.of_nat BP_NPIX_X)) ::
           tptr (tarray tfloat N_RANGE_UPSAMPLED) ::
           tptr (tarray tfloat N_RANGE_UPSAMPLED) ::
           tptr tdouble ::
           tptr tdouble ::
           tptr tdouble ::
           tptr tdouble ::
           tptr tdouble ::
           tptr tdouble ::
           tptr tdouble ::
           tptr tdouble ::
           nil)
      )
      tvoid
      AST.cc_default
    /\
    forall `(HYPS: SARHypotheses)
      m
      (Hm:
         holds
           (P ++
              Pperm bir (Int.unsigned oir) pir (size_chunk_nat Mfloat32 * Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y))              
              ++
              Pperm bii (Int.unsigned oii) pii (size_chunk_nat Mfloat32 * Z.to_nat (Z.of_nat BP_NPIX_X * Z.of_nat BP_NPIX_Y)))
           m)
    ,
      let st0 := (Callstate fn_sar_backprojection
                            (Vptr bir oir ::
                            Vptr bii oii ::
                            Vptr bdr odr ::
                            Vptr bdi odi ::
                            Vptr bpx opx ::
                            Vptr bpy opy ::
                            Vptr bpz opz ::
                            Vptr bku oku ::
                            Vptr br0 or0 ::
                            Vptr bdR odR ::
                            Vptr bdxdy odxdy ::
                            Vptr bz0 oz0 ::
                            nil)
                            Kstop
                            m) in
      exists s ,
        star Clight.step2 ge
             st0
             E0
             s /\
        exists m',
          s = Returnstate Vundef Kstop m' /\
          exists image_r image_i,
            holds (P ++
                     Parray_int Mfloat32 image_r bir oir pir (Int.mul (Int.repr (Z.of_nat BP_NPIX_X)) (Int.repr (Z.of_nat BP_NPIX_Y)))
                     ++
                    Parray_int Mfloat32 image_i bii oii pii (Int.mul (Int.repr (Z.of_nat BP_NPIX_X)) (Int.repr (Z.of_nat BP_NPIX_Y))))
                  m' /\
            forall y,
              (y < BP_NPIX_Y)%nat ->
              forall x,
                (x < BP_NPIX_X)%nat ->
                let ir := image_r (Z.of_nat (y * BP_NPIX_X + x)) in
                let ii := image_i (Z.of_nat (y * BP_NPIX_X + x)) in
                is_finite _ _ ir = true /\
                is_finite _ _ ii = true /\
                let '(tr, ti) := 
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
                                        (y)
                                        (x)
                                        (0, 0)
                                        O N_PULSES                    
 in
                Rabs (B2R _ _ ir - tr) <= pixel_bound /\
                Rabs (B2R _ _ ii - ti) <= pixel_bound.
