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

Properties of the real-number SAR backprojection algorithm,
in particular error propagation.
*)

Require Export RAux.
Require Export Bool.
Open Scope R_scope.
Require Export List.
Require Export LibTac.
Require Export SARBackProj.
Require Flocq.Core.Fcore_Raux.

Lemma interpol_bin_propagation data eps_bin eps_res bin1 bin2:
       eps_bin < 1 ->
       (forall i, eps_bin * Rabs (data (i + 1)%Z - data i) <= eps_res / 2) ->
       Rabs (bin2 - bin1) <= eps_bin ->
       Rabs (interpol data bin2 - interpol data bin1) <= eps_res.
Proof.
  intros EPS_BIN DATA_DISTR'.
  intro TEMP.
  assert (forall i, eps_bin * Rabs (data (i + 1)%Z - data i) <= eps_res) as DATA_DISTR.
  {
    intros.
    specialize (DATA_DISTR' i).
    eapply Rle_trans; eauto.
    assert (0 <= eps_bin * Rabs (data (i + 1)%Z - data i)).
    {
      apply Rmult_le_pos; auto using Rabs_pos.
      generalize (Rabs_pos (bin2 - bin1)).
      lra.
    }
    lra.
  }
  revert TEMP.
  revert bin1 bin2.
  cut (forall bin1 bin2, 0 <= bin2 - bin1 <= eps_bin ->  Rabs (interpol data bin2 - interpol data bin1) <= eps_res).
  {
    intros CUT bin1 bin2 ABS.
    apply Fcore_Raux.Rabs_le_inv in ABS.
    destruct (Rle_dec bin1 bin2).
    {
      apply CUT.
      lra.
    }
    rewrite Rabs_minus_sym.
    apply CUT.
    lra.
  }
  intros bin1 bin2 ARG.
  destruct (base_Int_part bin1).
  destruct (base_Int_part bin2).
  destruct (Rle_dec (IZR (Int_part bin2)) bin1).
  {
    assert (Int_part bin2 = Int_part bin1)
      as INT
      by
        (apply Int_part_unique; auto; lra).
    assert (interpol data bin2 - interpol data bin1 =
    ((bin2 - bin1) * (data (Int_part bin1 + 1)%Z - data (Int_part bin1)%Z))) as INTERP.
    {
      unfold interpol. rewrite INT. ring.
    }
    rewrite INTERP.
    rewrite Rabs_mult.
    eapply Rle_trans; [ | now apply (DATA_DISTR (Int_part bin1)) ].
    apply Rmult_le_compat_r.
    {
      apply Rabs_pos.
    }
    rewrite Rabs_right by lra.
    tauto.
  }
  assert (Int_part bin1 + 1 = Int_part bin2)%Z
      as INT.
  {
    apply Int_part_unique.
    {
      apply Rle_trans with (IZR (Int_part bin2)); auto.
      apply IZR_le.
      assert (IZR (Int_part bin1) < IZR (Int_part bin2)) as LT by lra.
      apply lt_IZR in LT.
      omega.
    }
    rewrite plus_IZR; simpl; lra.
  }
  unfold interpol.
  repeat rewrite <- INT.
  repeat rewrite plus_IZR.
  simpl.
  match goal with
      |- Rabs ?x <= _ => ring_simplify x
  end.
  unfold Rminus.
  remember (data (Int_part bin1 + 1 + 1)%Z) as i2.
  remember (data (Int_part bin1 + 1)%Z) as i1.
  remember (data (Int_part bin1)%Z) as i0.
  remember (IZR (Int_part bin1)) as j.
  repeat rewrite (Rmult_comm i1).
  match goal with
      |- Rabs ?x <= _ =>
      replace x with (((j + 1) - bin1) * (i1 - i0) + (bin2 - (j + 1)) * (i2 - i1)) by ring
  end.
  replace eps_res with (eps_res / 2 + eps_res / 2) by field.
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  apply Rplus_le_compat.
  {
    rewrite Rabs_mult.
    apply Rle_trans with (eps_bin * Rabs (i1 - i0)).
    {
      apply Rmult_le_compat; auto using Rabs_pos; try lra.
      subst.
      replace 1 with (IZR 1) by reflexivity.
      rewrite <- plus_IZR.
      rewrite INT.
      apply Rabs_le; lra.
    }
    subst; eauto.
  }
  rewrite Rabs_mult.
  apply Rle_trans with (eps_bin * Rabs (i2 - i1)).
  {
    apply Rmult_le_compat; auto using Rabs_pos; try lra.
    subst.
    replace 1 with (IZR 1) by reflexivity.
    rewrite <- plus_IZR.
    rewrite INT.
    apply Rabs_le; lra.
  }
  subst; eauto.
Qed.

Lemma interpol_data_propagation data1 data2 eps_data eps_res bin:
  (forall i, Rabs (data2 i - data1 i) <= eps_data) ->
  eps_data <= eps_res / 2 ->
  Rabs (interpol data2 bin - interpol data1 bin) <= eps_res.
Proof.
  intros DATA_ERROR.
  unfold interpol.
  intro EPS_COND.
  match goal with 
      |- Rabs ?x <= _ =>
      match x with
          ?a * ?b1 + ?c * ?d1 - (?a * ?b2 + ?c * ?d2) =>
          replace x with (a * (b1 - b2) + c * (d1 - d2)) by ring
      end
  end.
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  repeat rewrite Rabs_mult.
  replace eps_res with (eps_res / 2 + eps_res / 2) by field.
  destruct (base_Int_part bin).
  apply Rplus_le_compat.
  {
    apply Rle_trans with (1 * eps_data); try lra.
    apply Rmult_le_compat; auto using Rabs_pos.
    apply Rabs_le; lra.
  }
  apply Rle_trans with (1 * eps_data); try lra.
  apply Rmult_le_compat; auto using Rabs_pos.
  apply Rabs_le; lra.
Qed.

Lemma bin_sample_component_range N_RANGE_UPSAMPLED data bin M:
  0 <= M ->
  (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z -> Rabs (data i) <= M) ->
  Rabs (bin_sample_component N_RANGE_UPSAMPLED data bin) <= M.
Proof.
  intros HM Hdata.
  unfold bin_sample_component.
  destruct (Rle_dec 0 bin) as [LO | ] ; simpl; try (rewrite Rabs_R0; auto).
  destruct (Rlt_dec bin (IZR (N_RANGE_UPSAMPLED - 1))) as [ HI | ] ; simpl; try (rewrite Rabs_R0; auto).
  unfold interpol.
  replace 0 with (IZR 0) in LO by reflexivity.
  apply IZR_Int_part in LO.
  destruct (base_Int_part bin).
  assert (IZR (Int_part bin) < IZR (N_RANGE_UPSAMPLED - 1)) as LT by lra.
  apply lt_IZR in LT.
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  repeat rewrite Rabs_mult.
  eapply Rle_trans.
  {
    apply Rplus_le_compat.
    {
      apply Rmult_le_compat; auto using Rabs_pos.
      {
        rewrite Rabs_right by lra.
        apply Rle_refl.
      }
      eapply Hdata.
      omega.
    }
    apply Rmult_le_compat; auto using Rabs_pos.
    {
      rewrite Rabs_right by lra.
      apply Rle_refl.
    }
    eapply Hdata.
    omega.
  }
  eapply (eq_ind_r (fun t => t <= _)).
  {
    apply Rle_refl.
  }
  ring.
Qed.

Lemma bin_sample_component_data_ext data1 data2 N_RANGE_UPSAMPLED bin:
  (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z -> data2 i = data1 i) ->
  bin_sample_component N_RANGE_UPSAMPLED data1 bin = bin_sample_component N_RANGE_UPSAMPLED data2 bin.
Proof.
  intro Hext.
  unfold bin_sample_component.
  destruct (Rle_dec 0 bin) as [ bin_pos | ] ; simpl; auto.
  destruct (Rlt_dec bin (IZR (N_RANGE_UPSAMPLED - 1))); simpl; auto.
  unfold interpol.
  replace 0 with (IZR 0) in bin_pos by reflexivity.
  apply IZR_Int_part in bin_pos.
  destruct (base_Int_part bin).
  assert (Int_part bin < N_RANGE_UPSAMPLED - 1)%Z by (apply lt_IZR; lra).
  rewrite Hext by omega.
  rewrite Hext by omega.
  reflexivity.
Qed.

Lemma bin_sample_component_right_border N_RANGE_UPSAMPLED data eps_bin eps_res bin:
 0 < IZR (N_RANGE_UPSAMPLED - 1) - bin <= eps_bin ->
 eps_bin < 1 ->
 0 <= bin ->
 ((2 <= N_RANGE_UPSAMPLED)%Z ->
            forall e : R, 0 <= e <= eps_bin -> Rabs (e * data (N_RANGE_UPSAMPLED - 2)%Z + (1 - e) * data (N_RANGE_UPSAMPLED - 1)%Z) <= eps_res) ->
Rabs (interpol data bin) <= eps_res.
Proof.
  intros Hbin Heps_bin Hbin_pos Hdata_N_2.
  assert ((N_RANGE_UPSAMPLED - 2)%Z = Int_part bin) as Ibin2.
  {
    apply Int_part_unique;
    replace (N_RANGE_UPSAMPLED - 2)%Z with (N_RANGE_UPSAMPLED - 1 - 1)%Z by omega;
    rewrite minus_IZR;
    simpl;
    lra.
  }
  unfold interpol.
  rewrite <- Ibin2.
  replace (N_RANGE_UPSAMPLED - 2 + 1)%Z with (N_RANGE_UPSAMPLED - 1)%Z by omega.
  replace (N_RANGE_UPSAMPLED - 2)%Z with (N_RANGE_UPSAMPLED - 1 - 1)%Z at 1 3 by omega.
  rewrite minus_IZR.
  simpl.
  remember (IZR (N_RANGE_UPSAMPLED - 1)) as Q.
  replace (1 - (bin - (Q - 1))) with (Q - bin) by lra.
  replace (bin - (Q - 1)) with (1 - (Q - bin)) by lra.
  apply Hdata_N_2.
  {
    replace 0 with (IZR 0) in Hbin_pos by reflexivity.
    apply IZR_Int_part in Hbin_pos.
    omega.
  }
  lra.
Qed.

Definition partial_to_total_data {A} N_RANGE_UPSAMPLED (data: _ -> A) i :=
   if Z_le_dec 0 i
    then if Z_le_dec i (N_RANGE_UPSAMPLED - 1)
         then data i
         else if Z_le_dec 0 (N_RANGE_UPSAMPLED - 1)
              then data (N_RANGE_UPSAMPLED - 1)%Z
              else data 0%Z
    else data 0%Z
  .

Lemma partial_to_total_data_eq {A} N_RANGE_UPSAMPLED (data: _ -> A) i (Hi: (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z)
:
  partial_to_total_data N_RANGE_UPSAMPLED data i = data i.
Proof.
    intros.
    unfold partial_to_total_data.
    destruct (Z_le_dec 0 i); try omega.
    destruct (Z_le_dec i (N_RANGE_UPSAMPLED - 1)); try omega.
    reflexivity.
Qed.

Lemma partial_to_total_data_diff N_RANGE_UPSAMPLED data eps_res
  (Heps_res: 0 <= eps_res)
  eps_bin
  (Hdata: forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z -> eps_bin * Rabs (data (i + 1)%Z - data i) <= eps_res)
  i
:
  eps_bin * Rabs (partial_to_total_data N_RANGE_UPSAMPLED data (i + 1)%Z - partial_to_total_data N_RANGE_UPSAMPLED data i) <= eps_res
.
Proof.
    unfold partial_to_total_data.
    destruct (Z_le_dec 0 i).
    {
      destruct (Z_le_dec 0 (i + 1)); try omega.
      destruct (Z_le_dec (i + 1) (N_RANGE_UPSAMPLED - 1)).
      {
        destruct (Z_le_dec i (N_RANGE_UPSAMPLED - 1)); try omega.
        apply Hdata.
        omega.
      }
      destruct (Z_le_dec i (N_RANGE_UPSAMPLED - 1)).
      {
        destruct (Z_le_dec 0 (N_RANGE_UPSAMPLED - 1)); try omega.
        replace i with (N_RANGE_UPSAMPLED - 1)%Z by omega.
        rewrite Rminus_diag.
        rewrite Rabs_R0.
        lra.
      }
      rewrite Rminus_diag.
      rewrite Rabs_R0.
      lra.
    }
    destruct (Z_le_dec 0 (i + 1)).
    {
      replace i with (-1)%Z by omega.
      simpl.
      destruct (Z_le_dec 0 (N_RANGE_UPSAMPLED - 1));
      rewrite Rminus_diag;
      rewrite Rabs_R0;
      lra.
    }
    rewrite Rminus_diag;
    rewrite Rabs_R0;
    lra.
Qed.

Lemma bin_sample_component_propagation N_RANGE_UPSAMPLED data eps_bin eps_res bin1 bin2:
       eps_bin < 1 ->
       0 <= eps_res ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z -> eps_bin * Rabs (data (i + 1)%Z - data i) <= eps_res / 2) ->
       Rabs (bin2 - bin1) <= eps_bin ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> forall e, 0 <= e <= eps_bin -> Rabs ((1 - e) * data 0%Z + e * data 1%Z) <= eps_res) ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> forall e, 0 <= e <= eps_bin -> Rabs (e * data (N_RANGE_UPSAMPLED - 2)%Z + (1 - e) * data (N_RANGE_UPSAMPLED - 1)%Z) <= eps_res) ->
       Rabs (bin_sample_component N_RANGE_UPSAMPLED data bin2 - bin_sample_component N_RANGE_UPSAMPLED data bin1) <= eps_res.
Proof.
  intros Heps_bin Heps_res Hdata Hbin Hdata_0 Hdata_N_2.

  pose (data' := partial_to_total_data N_RANGE_UPSAMPLED data).

  assert (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z ->
            data' i = data i) as EXT
  by apply partial_to_total_data_eq.

  repeat rewrite (bin_sample_component_data_ext data data') by assumption.

  assert (forall i, eps_bin * Rabs (data' (i + 1)%Z - data' i) <= eps_res / 2) as Hdata'
  by (apply partial_to_total_data_diff; auto; lra).

  assert ((2 <= N_RANGE_UPSAMPLED)%Z -> forall e, 0 <= e <= eps_bin -> Rabs ((1 - e) * data' 0%Z + e * data' 1%Z) <= eps_res) as Hdata'_0.
  {
    intro.
    repeat rewrite EXT by omega.
    auto.
  }

  assert (
    (2 <= N_RANGE_UPSAMPLED)%Z -> forall e, 0 <= e <= eps_bin ->
    Rabs (e * data' (N_RANGE_UPSAMPLED - 2)%Z + (1 - e) * data' (N_RANGE_UPSAMPLED - 1)%Z) <= eps_res
  ) as Hdata'_N_2.
  {
    intro.
    repeat rewrite EXT by omega.
    auto.
  }

  clear EXT.
  revert Hdata' Hdata'_0 Hdata'_N_2.
  generalize data'.
  clear data Hdata Hdata_0 Hdata_N_2 data'.
  intros data Hdata Hdata_0 Hdata_N_2.

  unfold bin_sample_component.
  destruct (Rle_dec 0 bin2) as [ Hbin2_pos | Hbin2_neg ]; simpl.
  {
    destruct (Rlt_dec bin2 (IZR (N_RANGE_UPSAMPLED - 1))) as [ Hbin2_le | Hbin2_ge ] ; simpl.
    {
      destruct (Rle_dec 0 bin1) as [ Hbin1_pos | Hbin1_neg ]; simpl.
      {
        destruct (Rlt_dec bin1 (IZR (N_RANGE_UPSAMPLED - 1))) as [ Hbin1_le | Hbin1_ge ] ; simpl.
        {
          eapply interpol_bin_propagation; eauto.
        }
        rewrite Rminus_0_r.
        eapply bin_sample_component_right_border; eauto.
        apply Fcore_Raux.Rabs_le_inv in Hbin.
        lra.
      }
      rewrite Rminus_0_r.
      apply Fcore_Raux.Rabs_le_inv in Hbin.
      assert (0%Z = Int_part bin2) as Ibin2.
      {
        apply Int_part_unique.
        {
          assumption.
        }
        simpl.
        lra.
      }
      unfold interpol.
      rewrite <- Ibin2.
      simpl.
      rewrite Rminus_0_r.
      apply Hdata_0.
      {
        cut (0 < N_RANGE_UPSAMPLED - 1)%Z; [ omega | ].
        apply lt_IZR.
        simpl.
        lra.
      }
      lra.
    }
    rewrite Rminus_0_l.
    rewrite Rabs_Ropp.
    destruct (Rle_dec 0 bin1); simpl; try (rewrite Rabs_R0; lra).
    destruct (Rlt_dec bin1 (IZR (N_RANGE_UPSAMPLED - 1))); simpl; try (rewrite Rabs_R0; lra).
    eapply bin_sample_component_right_border; eauto.
    apply Fcore_Raux.Rabs_le_inv in Hbin.
    lra.
  }
  rewrite Rminus_0_l.
  rewrite Rabs_Ropp.
  destruct (Rle_dec 0 bin1); simpl; try (rewrite Rabs_R0; lra).
  destruct (Rlt_dec bin1 (IZR (N_RANGE_UPSAMPLED - 1))); simpl; try (rewrite Rabs_R0; lra).
  apply Fcore_Raux.Rabs_le_inv in Hbin.
  assert (0%Z = Int_part bin1) as Ibin1.
  {
    apply Int_part_unique.
    {
      assumption.
    }
    simpl.
    lra.
  }
  unfold interpol.
  rewrite <- Ibin1.
  simpl.
  rewrite Rminus_0_r.
  apply Hdata_0.
  {
    cut (0 < N_RANGE_UPSAMPLED - 1)%Z; [ omega | ].
    apply lt_IZR.
    simpl.
    lra.
  }
  lra.
Qed.

Lemma bin_sample_component_propagation_simple N_RANGE_UPSAMPLED data eps_bin eps_res bin1 bin2:
       eps_bin < 1 ->
       0 <= eps_res ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z -> eps_bin * Rabs (data (i + 1)%Z - data i) <= eps_res / 2) ->
       Rabs (bin2 - bin1) <= eps_bin ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> Rabs (data 0%Z) <= eps_res / 2) ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> Rabs (data (N_RANGE_UPSAMPLED - 1)%Z) <= eps_res / 2) ->
       Rabs (bin_sample_component N_RANGE_UPSAMPLED data bin2 - bin_sample_component N_RANGE_UPSAMPLED data bin1) <= eps_res.
Proof.
  intros Heps_bin Heps_res Hdata Hbin Hdata_0 Hdata_N.
  eapply bin_sample_component_propagation; eauto.
  {
    intros.
    replace ((1 - e) * data 0%Z + e * data 1%Z)
    with (data 0%Z + e * (data 1%Z - data 0%Z))
    by ring.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    eapply Rle_trans.
    {
      apply Rplus_le_compat.
      {
        eapply Hdata_0.
        assumption.
      }
      rewrite Rabs_mult.
      rewrite Rabs_right by lra.
      eapply Rle_trans.
      {
        apply Rmult_le_compat_r.
        {
          apply Rabs_pos.
        }
        instantiate (1 := eps_bin).
        lra.
      }
      replace 1%Z with (0 + 1)%Z by reflexivity.
      eapply Hdata.
      omega.
    }
    lra.
  }
  intros.
  replace (e * data (N_RANGE_UPSAMPLED - 2)%Z + (1 - e) * data (N_RANGE_UPSAMPLED - 1)%Z)
  with (data (N_RANGE_UPSAMPLED - 1)%Z + e * (data (N_RANGE_UPSAMPLED - 2)%Z - data (N_RANGE_UPSAMPLED - 1)%Z))
  by ring.
  eapply Rle_trans.
  {
    eapply Rabs_triang.
  }
  eapply Rle_trans.
  {
    apply Rplus_le_compat.
    {
      eapply Hdata_N.
      assumption.
    }
    rewrite Rabs_mult.
    rewrite Rabs_right by lra.
    eapply Rle_trans.
    {
      apply Rmult_le_compat_r.
      {
        apply Rabs_pos.
      }
      instantiate (1 := eps_bin).
      lra.
    }
    rewrite Rabs_minus_sym.
    replace (N_RANGE_UPSAMPLED - 1)%Z with (N_RANGE_UPSAMPLED - 2 + 1)%Z by ring.
    eapply Hdata.
    omega.
  }
  lra.
Qed.

Definition contrib_bin_component_2 N_RANGE_UPSAMPLED data_r data_i angle bin :=
  let sample_r := bin_sample_component N_RANGE_UPSAMPLED data_r bin in
  let sample_i := bin_sample_component N_RANGE_UPSAMPLED data_i bin in
  let matched_filter_r := cos angle in
  let matched_filter_i := sin angle in
  (sample_r * matched_filter_r - sample_i * matched_filter_i,
   sample_r * matched_filter_i + sample_i * matched_filter_r)
.

Lemma contrib_bin_component_eq N_RANGE_UPSAMPLED data_r data_i angle bin:
  contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin =
  contrib_bin_component_2 N_RANGE_UPSAMPLED data_r data_i angle bin.
Proof.
  unfold contrib_bin_component, contrib_bin_component_2, bin_sample_component.
  destruct (
   Rle_dec 0 bin && Rlt_dec bin (IZR (N_RANGE_UPSAMPLED - 1))
  ); auto.
  f_equal; ring.
Qed.

Lemma contrib_bin_component_ext N_RANGE_UPSAMPLED
  data_r1 data_r2
  (Hdata_r: forall i, (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z -> data_r2 i = data_r1 i)
  data_i1 data_i2
  (Hdata_i: forall i, (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z -> data_i2 i = data_i1 i)
  angle bin
:
  contrib_bin_component N_RANGE_UPSAMPLED data_r2 data_i2 angle bin =
  contrib_bin_component N_RANGE_UPSAMPLED data_r1 data_i1 angle bin
.
Proof.
  repeat rewrite contrib_bin_component_eq.
  unfold contrib_bin_component_2.
  repeat rewrite (bin_sample_component_data_ext data_r1 data_r2) by assumption.
  repeat rewrite (bin_sample_component_data_ext data_i1 data_i2) by assumption.
  reflexivity.
Qed.

Lemma contrib_bin_component_propagation_angle N_RANGE_UPSAMPLED data_r data_i bin angle1 angle2 eps_angle M:
  0 <= M ->
  (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z -> Rabs (data_r i) <= M) ->
  (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 1)%Z -> Rabs (data_i i) <= M) ->
  Rabs (angle2 - angle1) <= eps_angle ->
  forall f, (f = fst \/ f = snd) ->
       Rabs (f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle2 bin) - 
             f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle1 bin)) <= 2 * M * eps_angle.
Proof.
  intros HM Hdata_r Hdata_i Hangle f Hf.
  repeat rewrite contrib_bin_component_eq.
  destruct Hf; subst; simpl.
  {
    match goal with
    |- Rabs ?z <= _ =>
      replace z with
      (bin_sample_component N_RANGE_UPSAMPLED data_r bin * (cos angle2 - cos angle1) -
       bin_sample_component N_RANGE_UPSAMPLED data_i bin * (sin angle2 - sin angle1))
      by ring
    end.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    rewrite Rabs_Ropp.
    repeat rewrite Rabs_mult.
    eapply Rle_trans.
    {
      apply Rplus_le_compat.
      {
        apply Rmult_le_compat; auto using Rabs_pos.
        {
          eapply bin_sample_component_range; eauto.
        }
        apply cos_abs_error.
        eassumption.
      }
      apply Rmult_le_compat; auto using Rabs_pos.
      {
        eapply bin_sample_component_range; eauto.
      }
      apply sin_abs_error.
      eassumption.
    }
    lra.
  }
    match goal with
    |- Rabs ?z <= _ =>
      replace z with
      (bin_sample_component N_RANGE_UPSAMPLED data_r bin * (sin angle2 - sin angle1) +
       bin_sample_component N_RANGE_UPSAMPLED data_i bin * (cos angle2 - cos angle1))
      by ring
    end.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    repeat rewrite Rabs_mult.
    eapply Rle_trans.
    {
      apply Rplus_le_compat.
      {
        apply Rmult_le_compat; auto using Rabs_pos.
        {
          eapply bin_sample_component_range; eauto.
        }
        apply sin_abs_error.
        eassumption.
      }
      apply Rmult_le_compat; auto using Rabs_pos.
      {
        eapply bin_sample_component_range; eauto.
      }
      apply cos_abs_error.
      eassumption.
    }
    lra.
Qed.

Lemma contrib_bin_component_propagation_bin N_RANGE_UPSAMPLED data_r data_i angle bin1 bin2 eps_bin eps_res:
       eps_bin < 1 ->
       0 <= eps_res ->
       Rabs (bin2 - bin1) <= eps_bin ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z -> eps_bin * Rabs (data_r (i + 1)%Z - data_r i) <= eps_res / sqrt 2 / 2) ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> Rabs (data_r 0%Z) <= eps_res / sqrt 2 / 2) ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> Rabs (data_r (N_RANGE_UPSAMPLED - 1)%Z) <= eps_res / sqrt 2 / 2) ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z -> eps_bin * Rabs (data_i (i + 1)%Z - data_i i) <= eps_res / sqrt 2 / 2) ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> Rabs (data_i 0%Z) <= eps_res / sqrt 2 / 2) ->
       ((2 <= N_RANGE_UPSAMPLED)%Z -> Rabs (data_i (N_RANGE_UPSAMPLED - 1)%Z) <= eps_res / sqrt 2 / 2) ->
       forall f, (f = fst \/ f = snd) ->
       Rabs (f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin2) - 
             f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin1)) <= eps_res.
Proof.
  intros Heps_bin Heps_res Hbin Hdata_r Hdata_r_0 Hdata_r_N Hdata_i Hdata_i_0 Hdata_i_N f Hf.
  repeat rewrite contrib_bin_component_eq.
  unfold contrib_bin_component_2.
  assert (0 < sqrt 2).
  {
    apply sqrt_pos_strict.
    lra.
  }
  assert (0 <= eps_res / sqrt 2).
  {
    apply Rmult_le_pos; auto.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    assumption.
  }
  assert (Rabs (bin_sample_component N_RANGE_UPSAMPLED data_r bin2 - bin_sample_component N_RANGE_UPSAMPLED data_r bin1) <= eps_res / sqrt 2)
  by (eapply bin_sample_component_propagation_simple; eauto; lra).
  assert (Rabs (bin_sample_component N_RANGE_UPSAMPLED data_i bin2 - bin_sample_component N_RANGE_UPSAMPLED data_i bin1) <= eps_res / sqrt 2)
  by (eapply bin_sample_component_propagation_simple; eauto; lra).
  destruct Hf; subst; simpl.
  {
    match goal with
    |- Rabs ?z <= _ =>
       replace z with
       ((bin_sample_component N_RANGE_UPSAMPLED data_r bin2 - bin_sample_component N_RANGE_UPSAMPLED data_r bin1) * cos angle -
        (bin_sample_component N_RANGE_UPSAMPLED data_i bin2 - bin_sample_component N_RANGE_UPSAMPLED data_i bin1) * sin angle)
       by ring
    end.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    rewrite Rabs_Ropp.
    repeat rewrite Rabs_mult.
    eapply Rle_trans.
    {
      apply Rplus_le_compat.
      {
        apply Rmult_le_compat_r; auto using Rabs_pos.
        eassumption.
      }
      apply Rmult_le_compat_r; auto using Rabs_pos.
      eassumption.
    }
    match goal with
    |- ?a <= _ =>
    replace a with (eps_res / sqrt 2 * (Rabs (cos angle) + Rabs (sin angle))) by ring
    end.
    eapply Rle_trans.
    {
      apply Rmult_le_compat_l; auto.
      apply abs_cos_sin_plus_le.
    }
    eapply (eq_ind_r (fun t => t <= _)).
    {
      eapply Rle_refl.
    }
    field.
    lra.
  }
  match goal with
  |- Rabs ?z <= _ =>
     replace z with
     ((bin_sample_component N_RANGE_UPSAMPLED data_r bin2 - bin_sample_component N_RANGE_UPSAMPLED data_r bin1) * sin angle +
      (bin_sample_component N_RANGE_UPSAMPLED data_i bin2 - bin_sample_component N_RANGE_UPSAMPLED data_i bin1) * cos angle)
     by ring
  end.
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  repeat rewrite Rabs_mult.
  eapply Rle_trans.
  {
    apply Rplus_le_compat.
    {
      apply Rmult_le_compat_r; auto using Rabs_pos.
      eassumption.
    }
    apply Rmult_le_compat_r; auto using Rabs_pos.
    eassumption.
  }
    match goal with
    |- ?a <= _ =>
    replace a with (eps_res / sqrt 2 * (Rabs (cos angle) + Rabs (sin angle))) by ring
    end.
    eapply Rle_trans.
    {
      apply Rmult_le_compat_l; auto.
      apply abs_cos_sin_plus_le.
    }
    eapply (eq_ind_r (fun t => t <= _)).
    {
      eapply Rle_refl.
    }
    field.
    lra.
Qed.

Lemma contrib_bin_component_naive_propagation_bin_aux data_r data_i angle bin1 bin2 eps_bin eps_res:
       eps_bin < 1 ->
       0 <= eps_res ->
       Rabs (bin2 - bin1) <= eps_bin ->
       (forall i, eps_bin * Rabs (data_r (i + 1)%Z - data_r i) <= eps_res / sqrt 2 / 2) ->
       (forall i, eps_bin * Rabs (data_i (i + 1)%Z - data_i i) <= eps_res / sqrt 2 / 2) ->
       forall f, (f = fst \/ f = snd) ->
       Rabs (f (contrib_bin_component_naive data_r data_i angle bin2) - 
             f (contrib_bin_component_naive data_r data_i angle bin1)) <= eps_res.
Proof.
  intros Heps_bin Heps_res Hbin Hdata_r Hdata_i f Hf.
  unfold contrib_bin_component_naive.
  assert (0 < sqrt 2).
  {
    apply sqrt_pos_strict.
    lra.
  }
  assert (0 <= eps_res / sqrt 2).
  {
    apply Rmult_le_pos; auto.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    assumption.
  }
  assert (Rabs (interpol data_r bin2 - interpol data_r bin1) <= eps_res / sqrt 2)
  by (eapply interpol_bin_propagation; eauto).
  assert (Rabs (interpol data_i bin2 - interpol data_i bin1) <= eps_res / sqrt 2)
  by (eapply interpol_bin_propagation; eauto).
  destruct Hf; subst; simpl.
  {
    match goal with
    |- Rabs ?z <= _ =>
       replace z with
       ((interpol data_r bin2 - interpol data_r bin1) * cos angle -
        (interpol data_i bin2 - interpol data_i bin1) * sin angle)
       by ring
    end.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    rewrite Rabs_Ropp.
    repeat rewrite Rabs_mult.
    eapply Rle_trans.
    {
      apply Rplus_le_compat.
      {
        apply Rmult_le_compat_r; auto using Rabs_pos.
        eassumption.
      }
      apply Rmult_le_compat_r; auto using Rabs_pos.
      eassumption.
    }
    match goal with
    |- ?a <= _ =>
    replace a with (eps_res / sqrt 2 * (Rabs (cos angle) + Rabs (sin angle))) by ring
    end.
    eapply Rle_trans.
    {
      apply Rmult_le_compat_l; auto.
      apply abs_cos_sin_plus_le.
    }
    eapply (eq_ind_r (fun t => t <= _)).
    {
      eapply Rle_refl.
    }
    field.
    lra.
  }
  match goal with
  |- Rabs ?z <= _ =>
     replace z with
     ((interpol data_r bin2 - interpol data_r bin1) * sin angle +
      (interpol data_i bin2 - interpol data_i bin1) * cos angle)
     by ring
  end.
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  repeat rewrite Rabs_mult.
  eapply Rle_trans.
  {
    apply Rplus_le_compat.
    {
      apply Rmult_le_compat_r; auto using Rabs_pos.
      eassumption.
    }
    apply Rmult_le_compat_r; auto using Rabs_pos.
    eassumption.
  }
    match goal with
    |- ?a <= _ =>
    replace a with (eps_res / sqrt 2 * (Rabs (cos angle) + Rabs (sin angle))) by ring
    end.
    eapply Rle_trans.
    {
      apply Rmult_le_compat_l; auto.
      apply abs_cos_sin_plus_le.
    }
    eapply (eq_ind_r (fun t => t <= _)).
    {
      eapply Rle_refl.
    }
    field.
    lra.
Qed.

Lemma contrib_bin_component_naive_propagation_bin_elim N_RANGE_UPSAMPLED data_r data_i angle bin1 bin2 eps_bin eps_res:
       eps_bin < 1 ->
       0 <= eps_res ->
       Rabs (bin2 - bin1) <= eps_bin ->
       0 <= bin2 < IZR (N_RANGE_UPSAMPLED - 1) ->
       0 <= bin1 < IZR (N_RANGE_UPSAMPLED - 1) ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z ->  eps_bin * Rabs (data_r (i + 1)%Z - data_r i) <= eps_res / sqrt 2 / 2) ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z ->  eps_bin * Rabs (data_i (i + 1)%Z - data_i i) <= eps_res / sqrt 2 / 2) ->
       forall f, (f = fst \/ f = snd) ->
       Rabs (f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin2) - 
             f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin1)) <= eps_res.
Proof.
  intros Heps_bin Heps_res Hbin Hbin2 Hbin1 Hdata_r Hdata_i f Hf.

  generalize (partial_to_total_data_eq N_RANGE_UPSAMPLED data_r).
  intro Hdata_r_ext.
  generalize (partial_to_total_data_eq N_RANGE_UPSAMPLED data_i).
  intro Hdata_i_ext.

  repeat rewrite <- ( contrib_bin_component_ext
  _ _ _ Hdata_r_ext _ _ Hdata_i_ext ).

  clear Hdata_r_ext Hdata_i_ext.

  assert (0 < sqrt 2).
  {
    apply sqrt_pos_strict.
    lra.
  }
  assert (0 <= eps_res / sqrt 2).
  {
    apply Rmult_le_pos; auto.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    assumption.
  }
  assert (0 <= eps_res / sqrt 2 / 2) as Heps_res' by lra.

  generalize (partial_to_total_data_diff
  _ _ _ Heps_res' _ Hdata_r).
  clear Hdata_r.
  intro Hdata_r.
  generalize (partial_to_total_data_diff
  _ _ _ Heps_res' _ Hdata_i).
  clear Hdata_i.
  intro Hdata_i.

  unfold contrib_bin_component.

  destruct (Rle_dec 0 bin2); try lra.
  destruct (Rlt_dec bin2 (IZR (N_RANGE_UPSAMPLED - 1))); try lra.
  destruct (Rle_dec 0 bin1); try lra.
  destruct (Rlt_dec bin1 (IZR (N_RANGE_UPSAMPLED - 1))); try lra.
  simpl.

  eapply contrib_bin_component_naive_propagation_bin_aux; eauto.
Qed.

Corollary contrib_bin_component_naive_propagation_bin_intro N_RANGE_UPSAMPLED data_r data_i angle bin1 bin2 eps_bin eps_res:
       eps_bin < 1 ->
       0 <= eps_res ->
       Rabs (bin2 - bin1) <= eps_bin ->
       0 <= bin2 < IZR (N_RANGE_UPSAMPLED - 1) ->
       0 <= bin1 < IZR (N_RANGE_UPSAMPLED - 1) ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z ->  eps_bin * Rabs (data_r (i + 1)%Z - data_r i) <= eps_res) ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z ->  eps_bin * Rabs (data_i (i + 1)%Z - data_i i) <= eps_res) ->
       forall f, (f = fst \/ f = snd) ->
       Rabs (f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin2) - 
             f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin1)) <= eps_res * sqrt 2 * 2
.
Proof.
  intros.
  assert (0 < sqrt 2).
  {
    apply sqrt_pos_strict.
    lra.
  }
  assert (0 <= eps_res * sqrt 2).
  {
    apply Rmult_le_pos; auto.
    lra.
  }
  assert (0 <= eps_res * sqrt 2 * 2) by lra.
  eapply contrib_bin_component_naive_propagation_bin_elim; eauto.
  {
    intros.
    eapply Rle_trans; eauto.
    apply Req_le.
    field.
    lra.
  }
  intros.
  eapply Rle_trans; eauto.
  apply Req_le.
  field.
  lra.
Qed.

Corollary contrib_bin_component_naive_propagation_bin_intro_2 N_RANGE_UPSAMPLED data_r data_i angle bin1 bin2 eps_bin eps_res:
       eps_bin < 1 ->
       0 <= eps_res ->
       Rabs (bin2 - bin1) <= eps_bin ->
       0 <= bin2 < IZR (N_RANGE_UPSAMPLED - 1) ->
       0 <= bin1 < IZR (N_RANGE_UPSAMPLED - 1) ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z ->  Rabs (data_r (i + 1)%Z - data_r i) <= eps_res) ->
       (forall i, (0 <= i <= N_RANGE_UPSAMPLED - 2)%Z ->  Rabs (data_i (i + 1)%Z - data_i i) <= eps_res) ->
       forall f, (f = fst \/ f = snd) ->
       Rabs (f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin2) - 
             f (contrib_bin_component N_RANGE_UPSAMPLED data_r data_i angle bin1)) <= (eps_bin * eps_res) * sqrt 2 * 2
.
Proof.
  intros H H0 H1 H2 H3 H4 H5 f H6.
  assert (0 <= eps_bin) as H7.
  {
    generalize (Rabs_pos (bin2 - bin1)).
    lra.
  }
  eapply contrib_bin_component_naive_propagation_bin_intro; eauto.
  {
    apply Rmult_le_pos; auto.
  }
  {
    intros i H8.
    apply Rmult_le_compat_l; auto.
  }
  {
    intros i H8.
    apply Rmult_le_compat_l; auto.
  }
Qed.

Definition pulse_ N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv px py ku :=
  let '(R, bin) := bin_ (platpos_x) (platpos_y) (platpos_z) z0 R0 dR_inv px py in
  contrib_bin_component N_RANGE_UPSAMPLED (data_r) (data_i) (2 * ku * R) bin.

Lemma pulse'_eq BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy x y :
  pulse BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy x y =
  let px := (- INR BP_NPIX_X / 2 + 1 / 2 + INR x) * dxdy in
  let py := (- INR BP_NPIX_Y / 2 + 1 / 2 + INR y) * dxdy in
  pulse_ N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv px py ku
.
Proof.
  reflexivity.
Qed.

Lemma Mplus_assoc a b c: Mplus a (Mplus b c) = Mplus (Mplus a b) c.
Proof.
  unfold Mplus;
  destruct a; destruct b; destruct c; simpl; f_equal; ring.
Qed.

Lemma Mplus_comm a b: Mplus a b = Mplus b a.
Proof.
  unfold Mplus; f_equal; ring.
Qed.

Lemma Mplus_0_l a:
  Mplus (0, 0) a = a.
Proof.
  unfold Mplus; destruct a; simpl; f_equal; ring.
Qed.

Lemma Mplus_0_r a:
  Mplus a (0, 0) = a.
Proof.
  unfold Mplus; destruct a; simpl; f_equal; ring.
Qed.

(* Auxiliaries *)

Fixpoint sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku contrib (p n: nat) {struct n} :=
  match n with
  | O => contrib
  | S n' =>
    let contrib_p := pulse_ N_RANGE_UPSAMPLED (platpos_x p) (platpos_y p) (platpos_z p) (data_r p) (data_i p) z0 R0 dR_inv px py ku in
    let contrib' := Mplus contrib contrib_p in
    sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku contrib' (S p) n'
  end.

Lemma sar_backprojection_eq BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x n:
  forall contrib p,
    sar_backprojection BP_NPIX_X BP_NPIX_Y N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv ku dxdy y x contrib p n =
    let py := (- INR BP_NPIX_Y / 2 + 1 / 2 + INR y) * dxdy in
    let px := (- INR BP_NPIX_X / 2 + 1 / 2 + INR x) * dxdy in
    sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku contrib p n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma sar_backprojection'_charac N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku n:
  forall p contrib,
    sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku contrib p n =
    Mplus contrib (sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku (0, 0) p n).
Proof.
  induction n; simpl; intros.
  {
    rewrite Mplus_0_r.
    reflexivity.
  }
  rewrite IHn.
  rewrite <- Mplus_assoc.
  f_equal.
  rewrite Mplus_0_l.
  symmetry.
  apply IHn.
Qed.

Lemma sar_backprojection'_S N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku p n:
  sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku (0,0) p (S n) =
  Mplus
   (pulse_ N_RANGE_UPSAMPLED (platpos_x p) (platpos_y p) (platpos_z p) (data_r p) (data_i p) z0 R0 dR_inv px py ku)
   (sar_backprojection' N_RANGE_UPSAMPLED platpos_x platpos_y platpos_z data_r data_i z0 R0 dR_inv py px ku (0,0) (S p) n).
Proof.
  simpl.
  rewrite sar_backprojection'_charac.
  rewrite Mplus_0_l.
  reflexivity.
Qed.
