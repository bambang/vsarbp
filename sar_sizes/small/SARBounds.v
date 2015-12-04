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

Bounds for small images. Those bounds have been extracted from the
DARPA PERFECT suite ( http://hpc.pnl.gov/PERFECT/ )
*)

Require Import ZArith RAux.
Require Flocq.Core.Fcore_Raux.
Definition abs_data_border: R := (16231879/4294967296)%R .
Definition abs_data_min: R := (6115167/4503599627370496)%R .
Definition abs_data_max: R := (4194091/4194304)%R .
Definition abs_data_dist: R := (2873621/16777216)%R .

Definition platpos_x_min: R := (7227795/1024)%R .
Definition platpos_x_max: R := (14481547/2048)%R. 

Definition platpos_y_min: R := (0)%R .
Definition platpos_y_max: R := (13866841/32768)%R. 

Definition platpos_z_min: R := (14481547/2048)%R .
Definition platpos_z_max: R := (14481547/2048)%R. 

Definition dxdy := Eval compute in (4503599627370496 * / Fcore_Raux.Z2R (2 ^ 54))%R. 
Definition dR := Eval compute in (4503599627370496 * / Fcore_Raux.Z2R (2 ^ 57))%R.
Definition N_PULSES := (512)%nat .
Definition N_RANGE := (512)%Z .
Definition N_RANGE_UPSAMPLED := (4096)%Z .
Definition BP_NPIX_Y := (512)%nat .
Definition BP_NPIX_X := (512)%nat .
Definition ku := Eval compute in (7368997658362958 * / Fcore_Raux.Z2R (2 ^ 45))%R. 
(*
Definition z0 := Eval compute in (0 * / R_of_Z (2 ^ 1074))%R. 
*)
Definition z0_low := 0%R.
Definition z0_high := 0%R.
Definition R0 := Eval compute in (5462373766791168 * / Fcore_Raux.Z2R (2 ^ 39))%R.
