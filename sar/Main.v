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

Final proof, main theorem.
Submitted to CPP 2016
*)

Require Export
SARBackProjSourceSpec
SARBackProjSourceLink SARBackProjSourceOpt.

(**
This file summarizes the main result on our
implementation of SAR backprojection:

For every program linked with our implementation,
SAR backprojection introduces at most `pixel_error'
total rounding and approximation error for each pixel.

The hypotheses and correctness statement are specified in
SARSpecs.v

The real-number algorithm for SAR backprojection is
specified in SARBackProj.v

The code is defined in SARBackProjSource.v,
which was obtained from backprojection.c
using CompCert clightgen.

The numerical bounds on the input data are defined in SARBounds.v,
which was obtained from a pass on the PERFECT data suite (
http://hpc.pnl.gov/PERFECT/ )

The implementation error bound is *computed* in
SARBackProjSourceOpt.v, along with the proof. Since the same proof
scripts are used for all image sizes (small, medium and large), no
computed numerical values will textually appear in them.

Among the proofs that are not too hard to read:
- SARBackProjSourceNormOpt.v: proof of C implementation
  of square root and norm
- SARBackProjSourceSinOpt.v: proof of C implementation
  of sine
**)

Theorem sar_backprojection_correct: 
  forall (ge: Clight.genv)
         `(LINK: LinkingHypotheses ge),
    sar_backprojection_spec
      ge
      (Clight.Internal
         (f_sar_backprojection2 N_RANGE_UPSAMPLED (Z.of_nat BP_NPIX_X) (Z.of_nat BP_NPIX_Y) (Z.of_nat N_PULSES)))
      pixel_error.
Proof.
  exact SARBackProjSourceOpt.sar_backprojection_correct.
Qed.

Eval unfold sar_backprojection_spec, pixel_error in
 $( let t := type of sar_backprojection_correct in exact t )$ .

Print Assumptions sar_backprojection_correct.
