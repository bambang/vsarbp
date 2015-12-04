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
(** Author: Tahina Ramananandro <ramananandro@reservoir.com>

Reduce a fraction (given as a real number constant) to the lowest
denominator.
*)

Require Export LibTac RAux Flocq.Core.Fcore_Raux.

Ltac field_eq r :=
      let x := fresh in
      let L := fresh in
      let e := fresh in
      destruct (eqpivot r) as (x & L & e);
        cbn in e;
        field_simplify in e;
        replace (x / 1)%R with x in e by field;
        let t := (type of e) in
        match t with
          _ = ?u =>
          let tac a b k :=
              let pa := R_to_pos a in
              let pb := R_to_pos b in
              let d := (eval vm_compute in (Pos.gcd pa pb)) in
              let qa := (eval vm_compute in (Fcore_Raux.Z2R (Z.div (Z.pos pa) (Z.pos d)))) in
              let qb := (eval vm_compute in (Fcore_Raux.Z2R (Z.div (Z.pos pb) (Z.pos d)))) in
              k qa qb
          in
          match u with
            | 0%R => idtac
            | 0%R / _ => (replace u with 0%R in e by field)
            | (-?a) / ?b =>
              let k qa qb :=
                  (replace u with (-qa / qb)%R in e by field)
              in
              tac a b k
            | ?a / ?b =>
              let k qa qb :=
                  (replace u with (qa / qb)%R in e by field)
              in
              tac a b k
          end
        end;
        let t := (type of e) in
        idtac t;
        exact (Logic.eq_trans L e)
.
