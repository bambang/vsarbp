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

   Real-number mathematical specification of the
   SAR backprojection algorithm with linear interpolation.

  Properties of this algorithm (e.g. error propagation) are
  proved in SARBackProjFacts.
**)

Require Export Reals.
Require Export Bool.
Open Scope R_scope.
Require Export List.
Require Export LibTac.

Definition interpol data bin :=
  let bin_floor := Int_part bin in
  let w := bin - IZR bin_floor in
  (1 - w) * data bin_floor + w * data (bin_floor + 1)%Z.

Definition bin_sample_component N_RANGE_UPSAMPLED data bin :=
  if (Rle_dec 0 bin) && (Rlt_dec bin (IZR (N_RANGE_UPSAMPLED - 1)))
  then
    interpol data bin
  else
    0
  .

Definition contrib_bin_component_naive  data_r data_i angle bin :=
    let sample_r := interpol data_r bin in
    let sample_i := interpol data_i bin in
    let matched_filter_r := cos angle in
    let matched_filter_i := sin angle in
    (sample_r * matched_filter_r - sample_i * matched_filter_i,
     sample_r * matched_filter_i + sample_i * matched_filter_r)
.

Definition contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin :=
  if (Rle_dec 0 bin) && (Rlt_dec bin (IZR (N_RANGE_UPSAMPLED - 1)))
  then
    contrib_bin_component_naive data_r data_i angle bin
  else
    (0, 0)
  .

Definition bin_
platpos_x platpos_y platpos_z
z0 R0 dR_inv
px py
:=
let xdiff := platpos_x - px in
let ydiff := platpos_y - py in
let zdiff := platpos_z - z0 in
let R := sqrt (xdiff * xdiff + ydiff * ydiff + zdiff * zdiff) in
(R, (R - R0) * dR_inv).


Definition bin BP_NPIX_X BP_NPIX_Y platpos_x platpos_y platpos_z z0 R0 dR_inv dxdy x y :=
  let px := (- INR BP_NPIX_X / 2 + 1 / 2 + INR x) * dxdy in
  let py := (- INR BP_NPIX_Y / 2 + 1 / 2 + INR y) * dxdy in
  bin_ platpos_x platpos_y platpos_z z0 R0 dR_inv px py
.

Definition pulse  BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy x y :=
  let '(R, bin) := bin BP_NPIX_X BP_NPIX_Y (platpos_x) (platpos_y) (platpos_z) z0 R0 dR_inv dxdy x y in
  contrib_bin_component N_RANGE_UPSAMPLED (data_r) (data_i) (2 * ku * R) bin
.

Definition Mplus a b := (fst a + fst b, snd a + snd b).

(* SAR backprojection: here is the specification of our C code, 
   expressed in real numbers with exact operations (no rounding,
   no approximation).

  BP_NPIX_X, BP_NPIX_Y: dimensions of the image
  N_RANGE_UPSAMPLED: range of bin sampling
  platpos_x, platpos_y, platpos_z: platform positions
  data_r, data_i: sensor data 
  z0, R0, dR_inv, ku: radar parameters (see paper)
  y, x: pixel coordinates
  contrib: contributions of previous pulses
  p: current pulse
  n: number of remaining pulses (computation fuel) *)

Fixpoint sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x contrib (p n: nat) {struct n} :=
  match n with
  | O => contrib
  | S n' =>
    let contrib_p := pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED (platpos_x p) (platpos_y p) (platpos_z p) (data_r p) (data_i p) z0 R0 dR_inv ku dxdy x y in
    let contrib' := Mplus contrib contrib_p in
    sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x contrib' (S p) n'
  end.
