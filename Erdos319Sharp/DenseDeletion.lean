import Erdos319Sharp.CoreMissingPowers

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- The regular core retains the cleaning bound relative to the given sign class. -/
theorem eventually_dense_tail_core_with_deletion (a : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) :
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N →
      ((Finset.Icc 1 N \ B).card : ℝ) ≤ (a / 8) * N →
      ∃ F ⊆ B ∩ tailInterval a N,
        (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
        (((B ∩ tailInterval a N) \ F).card : ℝ) ≤
          (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) ∧
        ((tailInterval a N \ F).card : ℝ) ≤ (Finset.Icc 1 N \ B).card +
          (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) ∧
        (N : ℝ) / 2 ≤ F.card ∧
        |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 ∧
        ∀ r : ℚ, r.den ∣ F.lcm id →
          (Real.log (1 / a) + 1) / Real.log N ≤ (r : ℝ) → (r : ℝ) ≤ 2 →
          ∃ U ⊆ F, reciprocalSum U = r := by
  have haQuarter := small_tail_parameter a ha hMass
  have haOne : a ≤ 1 := haQuarter.trans (by norm_num)
  have hLossLimit : Tendsto (fun N : ℕ => (Real.log N) ^ (-(1 / 40 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)).comp tendsto_log_coe_at_top
  have hScaleLimit : Tendsto (fun N : ℕ => (Real.log N) ^ (-(3 / 100 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 100)).comp tendsto_log_coe_at_top
  have hTail := (tendsto_tailInterval_reciprocal a ha haOne).eventually
    (Ioo_mem_nhds (by linarith : Real.log (1 / a) - 1 / 4 < Real.log (1 / a))
      (by linarith : Real.log (1 / a) < Real.log (1 / a) + 1 / 4))
  filter_upwards [eventually_quantitative_regular_subset, hTail,
    hLossLimit.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < a / 8)),
    eventually_exact_subset_from_mass_bounds 1,
    hScaleLimit.eventually (Iio_mem_nhds ha),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_gt_atTop (0 : ℕ)]
    with N hClean hTailNear hLossSmall hExact hScale hL hN
  intro B hB hMissing
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hLPos : 0 < Real.log N := by linarith
  obtain ⟨F, hF, _, hSmooth, hMult, hRich, hPrune⟩ :=
    hClean (B ∩ tailInterval a N) (Finset.inter_subset_left.trans hB)
  have hFTail : F ⊆ tailInterval a N := hF.trans Finset.inter_subset_right
  have hFPrefix : F ⊆ Finset.Icc 1 N := (hF.trans Finset.inter_subset_left).trans hB
  have hTotal : ((tailInterval a N \ F).card : ℝ) ≤
      (Finset.Icc 1 N \ B).card + (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) := by
    have hCover := tail_omission_card_le a N B F
    linarith only [hCover, hPrune]
  have hLoss : ((tailInterval a N \ F).card : ℝ) ≤ (a / 4) * N := by
    have hSmall := mul_le_mul_of_nonneg_left hLossSmall.le hNReal.le
    nlinarith only [hTotal, hMissing, hSmall]
  have hCount : ((tailInterval a N \ F).card : ℝ) + F.card = (tailInterval a N).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hFTail
  have hCard : (N : ℝ) / 2 ≤ F.card := by
    have hTailCard := tailInterval_card_lower a ha.le haOne N
    have hQuarter := mul_le_mul_of_nonneg_right haQuarter hNReal.le
    nlinarith only [hCount, hLoss, hTailCard, hQuarter, hNReal.le]
  have hFMass := tail_subset_mass_bounds a ha N hN F hFTail
  have hLossMass : ((tailInterval a N \ F).card : ℝ) / (a * N) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos ha hNReal)).mpr
    nlinarith only [hLoss]
  have hApprox : |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hTailNear.1, hTailNear.2, hFMass.1, hFMass.2]
  have hMin : ∀ n ∈ F, a * N ≤ (n : ℝ) := by
    intro n hn
    exact ((mem_tailInterval a ha.le N n).mp (hFTail hn)).2.2.le
  have hCardEnough : (N : ℝ) / (Real.log N) ^ (1 : ℕ) ≤ F.card := by
    have hCompare : (N : ℝ) / Real.log N ≤ (N : ℝ) / 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith)
    simpa only [pow_one] using hCompare.trans hCard
  have hcLower : (Real.log N) ^ (-3 / 100 : ℝ) ≤ a := by
    convert hScale.le using 1 <;> norm_num
  refine ⟨F, hF, hSmooth, hPrune, hTotal, hCard, hApprox, ?_⟩
  intro r hDen hLower hUpper
  have hrPos : (0 : ℝ) < r :=
    (div_pos (by linarith : 0 < Real.log (1 / a) + 1) hLPos).trans_le hLower
  have hr : 0 < r := by exact_mod_cast hrPos
  have hTargetLower : (1 + 1 / Real.log N) * (r : ℝ) ≤ (reciprocalSum F : ℝ) := by
    have hInv : (1 : ℝ) / Real.log N ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hL
    have hMul := mul_le_mul_of_nonneg_left hUpper
      (show 0 ≤ 1 + 1 / Real.log N by positivity)
    have hLowMass := (abs_le.mp hApprox).1
    nlinarith only [hInv, hMul, hLowMass, hMass]
  have hTargetUpper : (reciprocalSum F : ℝ) ≤ Real.log N * (r : ℝ) := by
    have hCross := (div_le_iff₀ hLPos).mp hLower
    have hHighMass := (abs_le.mp hApprox).2
    nlinarith only [hCross, hHighMass]
  exact hExact a ((Real.log N) ^ (-(1 / 25 : ℝ))) F ha haOne hcLower (by norm_num)
    hFPrefix hMin hSmooth hMult hRich hCardEnough r hr hDen hTargetLower hTargetUpper

theorem eventually_dense_sign_core_with_deletion (a K ε : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ →
      ((N - A.card : ℕ) : ℝ) ≤ K * ((N : ℝ) * minorityScale N) →
      ∃ B : Finset ℕ, (B = positivePart A δ ∨ B = negativePart A δ) ∧
        ∃ F ⊆ B ∩ tailInterval a N,
          (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
          (((B ∩ tailInterval a N) \ F).card : ℝ) ≤
            (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) ∧
          ((tailInterval a N \ F).card : ℝ) ≤ (N : ℝ) * coreOmissionRate K N ∧
          (N : ℝ) / 2 ≤ F.card ∧
          |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 ∧
          (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) ≤ ε ∧
          ∀ r : ℚ, r.den ∣ F.lcm id →
            (Real.log (1 / a) + 1) / Real.log N ≤ (r : ℝ) → (r : ℝ) ≤ 2 →
            ∃ U ⊆ F, reciprocalSum U = r := by
  have hLimit : Tendsto (fun N : ℕ => (201 + 2 * |K|) * minorityScale N)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_minorityScale_zero.const_mul (201 + 2 * |K|)
  filter_upwards [eventually_minority_bound 1 (by norm_num),
    eventually_dense_tail_core_with_deletion a ha hMass,
    hLimit.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < a / 8)),
    eventually_core_missing_mass_small a K ε ha.le (small_tail_parameter a ha hMass) hε,
    eventually_positive_scale] with N hMinority hCore hSmall hMissingSmall hScale
  intro A δ hA hPrimitive hDeficit
  have hNonneg : 0 ≤ (N : ℝ) * minorityScale N :=
    mul_nonneg hScale.1.le (div_pos hScale.2.2 hScale.2.1).le
  have hDeficitAbs : ((N - A.card : ℕ) : ℝ) ≤ |K| * ((N : ℝ) * minorityScale N) :=
    hDeficit.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hNonneg)
  have hMin : min ((positivePart A δ).card : ℝ) ((negativePart A δ).card : ℝ) ≤
      (201 + |K|) * ((N : ℝ) * minorityScale N) := by
    have h := hMinority A δ hA hPrimitive
    norm_num only [one_mul] at h
    nlinarith only [h, hDeficitAbs]
  obtain ⟨B, hChoice, hB, hMissing⟩ :=
    exists_dense_sign_part N A δ ((201 + |K|) * ((N : ℝ) * minorityScale N)) hA hMin
  have hBbound : ((Finset.Icc 1 N \ B).card : ℝ) ≤
      (201 + 2 * |K|) * ((N : ℝ) * minorityScale N) := by
    nlinarith only [hMissing, hDeficitAbs]
  have hBsmall : ((Finset.Icc 1 N \ B).card : ℝ) ≤ (a / 8) * N := by
    have h := mul_le_mul_of_nonneg_left hSmall.le (Nat.cast_nonneg N)
    nlinarith only [hBbound, h]
  obtain ⟨F, hF, hSmooth, hPrune, hLoss, hCard, hApprox, hTargets⟩ := hCore B hB hBsmall
  have hRateLoss : ((tailInterval a N \ F).card : ℝ) ≤ (N : ℝ) * coreOmissionRate K N := by
    unfold coreOmissionRate
    nlinarith only [hLoss, hBbound]
  have hPrefix : F ⊆ Finset.Icc 1 N := (hF.trans Finset.inter_subset_left).trans hB
  exact ⟨B, hChoice, F, hF, hSmooth, hPrune, hRateLoss, hCard, hApprox,
    hMissingSmall F hPrefix hRateLoss, hTargets⟩

theorem tendsto_log_power_div_minorityScale_zero (s : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => (Real.log N) ^ (-s) / minorityScale N)
      atTop (𝓝 0) := by
  have hLog : Tendsto (fun N : ℕ => Real.log (Real.log N) / (Real.log N) ^ s)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero.comp tendsto_log_coe_at_top
  have hProduct : Tendsto (fun N : ℕ =>
      (Real.log (Real.log N) / (Real.log N) ^ s) *
        (Real.log (Real.log (Real.log N)))⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      hLog.mul (tendsto_inv_atTop_zero.comp tendsto_logloglog_nat)
  apply hProduct.congr'
  filter_upwards [eventually_positive_scale,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hScale hLogPos
  unfold minorityScale
  rw [Real.rpow_neg hLogPos.le]
  field_simp [hScale.2.1.ne', hScale.2.2.ne', (Real.rpow_pos_of_pos hLogPos s).ne']

theorem tendsto_core_deletion_ratio_zero :
    Tendsto (fun N : ℕ => ((N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ))) /
      ((N : ℝ) * minorityScale N)) atTop (𝓝 0) := by
  apply (tendsto_log_power_div_minorityScale_zero (1 / 40) (by norm_num)).congr'
  filter_upwards [eventually_positive_scale] with N hScale
  exact (mul_div_mul_left _ _ hScale.1.ne').symm

end Erdos319Sharp
