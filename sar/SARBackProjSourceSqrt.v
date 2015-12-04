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

Specifications of ISO C square root.
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
Require Import compcert.Ctypes.
Require Import compcert.Clight.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Appli.Fappli_IEEE.

Open Scope R_scope.

Require Import Clight2FP.
Existing Instance Clight2FP.nans.

Definition _sqrt_correct ge cef_sqrt :=
  type_of_fundef cef_sqrt =
  Ctypes.Tfunction (Ctypes.Tcons Clightdefs.tdouble Ctypes.Tnil)
                   Clightdefs.tdouble cc_default /\
  forall x m,
    is_finite _ _ x = true ->
    0 <= B2R _ _ x ->
    let s0 := (Callstate cef_sqrt
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
      y = FPLang.Bsqrt FPLang.Tdouble x.
