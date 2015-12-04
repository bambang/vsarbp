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

Linking hypotheses on any program to be linked with our
implementation of SAR backprojection.
*)

Require Export SARBackProjSourceOpt2.

Require SARBackProjSourceSqrt SARBackProjSourceSin.

Inductive LinkingHypotheses (ge: Clight.genv)
          bf_sqrt cef_sqrt
          b_sin fn_sin
          b_cos fn_cos
          
: Prop :=
  | LinkingHypothesesIntro
     (** the program is linked with our implementation **)
      (p :=
      (Clight.globalenv (SARBackProjSource.prog N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES))))
      (Hp_extends: forall i b, 
       Globalenvs.Genv.find_symbol p i = Some b ->
       exists b_,
         Globalenvs.Genv.find_symbol ge i = Some b_ /\
         forall f,
           Globalenvs.Genv.find_funct_ptr p b = Some f ->
        Globalenvs.Genv.find_funct_ptr ge b_ = Some f)

     (** the program is linked with implementations of ISO C99 sqrt, sin and cos **)
      (Hbf_sqrt: Globalenvs.Genv.find_symbol ge _sqrt = Some bf_sqrt)
      (Hcef_sqrt: Globalenvs.Genv.find_funct_ptr ge bf_sqrt = Some cef_sqrt)
      (Hcef_sqrt_correct: SARBackProjSourceSqrt._sqrt_correct ge cef_sqrt)

      (Hb_sin: Globalenvs.Genv.find_symbol ge _sin = Some b_sin)
      (Hfn_sin: Globalenvs.Genv.find_funct_ptr ge b_sin = Some fn_sin)
      (Hfn_sin_correct: SARBackProjSourceSin.f_unary_correct sin ge fn_sin)

      (Hb_cos: Globalenvs.Genv.find_symbol ge _cos = Some b_cos)
      (Hfn_cos: Globalenvs.Genv.find_funct_ptr ge b_cos = Some fn_cos)
      (Hfn_cos_correct: SARBackProjSourceSin.f_unary_correct cos ge fn_cos)

.

Existing Class LinkingHypotheses.

