import Erdos319Sharp.LocalizationEstimates

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_packet_sieve_budget :
    ∀ᶠ N : ℕ in atTop, ∀ c η : ℝ, 0 < c →
      (Real.log N) ^ (-3 / 100 : ℝ) ≤ c →
      (Real.log N) ^ (-1 / 25 : ℝ) ≤ η →
      ∀ q : ℕ, (q : ℝ) ≤ smoothCutoff 6 N →
        (N : ℝ) / (c * N) *
          (Real.exp (-(∑ p ∈ primeBand (packetMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹)) +
            Real.exp (2 * ∑ p ∈ primeBand (packetMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹) /
              (2 : ℝ) ^ (2 * sieveLevel N)) +
          (q : ℝ) / (c * N) * (localizationRoughBound N : ℝ) ^ (2 * sieveLevel N) ≤ η / 4 := by
  have hDecay : Tendsto (fun N : ℕ => (Real.log N) ^ (-3 / 100 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 100)).comp tendsto_log_coe_at_top
  have hExp : Tendsto (fun N : ℕ => Real.log N * Real.exp (-5 * localizationPower N))
      atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_log_pow_mul_exp_neg_localizationPower 1 5 (by norm_num)
  have hTotal : Tendsto (fun N : ℕ => 2 * (Real.log N) ^ (-3 / 100 : ℝ) +
      Real.log N * Real.exp (-5 * localizationPower N)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (hDecay.const_mul 2).add hExp
  have hSmall := hTotal.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hSmall, eventually_packet_prime_mass, eventually_localizationRoughBound_le,
    eventually_sieveLevel_tail_bound, eventually_sieveLevel_le_loglog_sq,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)]
    with N hSmallN hMass hYN hTail hLevel hL hLL hN c η hc hcLower hηLower q hq
  have hLPos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hL
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hN
  let P := primeBand (packetMediumBound N) (localizationRoughBound N)
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ N := by
    intro p hp
    have hMem := Finset.mem_filter.mp hp
    exact ⟨hMem.2, (Finset.mem_Icc.mp hMem.1).2.trans hYN⟩
  have hFirst : Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) ≤ (Real.log N) ^ (-1 / 10 : ℝ) := by
    calc
      _ ≤ Real.exp (-(1 / 10 : ℝ) * Real.log (Real.log N)) := by
        apply Real.exp_le_exp.mpr
        linarith only [hMass.2]
      _ = (Real.log N) ^ (-1 / 10 : ℝ) := by
        rw [Real.rpow_def_of_pos hLPos]
        congr 1
        ring
  have hTailPower : Real.exp (-16 * Real.log (Real.log N)) = (Real.log N) ^ (-16 : ℝ) := by
    rw [Real.rpow_def_of_pos hLPos]
    congr 1
    ring
  have hSecond : Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * sieveLevel N) ≤
      (Real.log N) ^ (-1 / 10 : ℝ) := by
    calc
      _ ≤ Real.exp (-16 * Real.log (Real.log N)) := hTail P hP
      _ = (Real.log N) ^ (-16 : ℝ) := hTailPower
      _ ≤ (Real.log N) ^ (-1 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hCount := localizationRough_q_sieve_cost N q c hc hN hLL hLevel hq
  have hCancel : (N : ℝ) / (c * N) = 1 / c := by field_simp [hc.ne', hNPos.ne']
  let B := 2 * (Real.log N) ^ (-1 / 10 : ℝ) + Real.exp (-5 * localizationPower N)
  have hRaw : (N : ℝ) / (c * N) *
      (Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
        Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * sieveLevel N)) +
      (q : ℝ) / (c * N) * (localizationRoughBound N : ℝ) ^ (2 * sieveLevel N) ≤ B / c := by
    rw [hCancel]
    calc
      _ ≤ (1 / c) * (2 * (Real.log N) ^ (-1 / 10 : ℝ)) +
          Real.exp (-5 * localizationPower N) / c := by
        exact add_le_add (mul_le_mul_of_nonneg_left (by linarith only [hFirst, hSecond])
          (by positivity)) hCount
      _ = B / c := by dsimp [B]; ring
  have hScale : B * (Real.log N) ^ (7 / 100 : ℝ) ≤
      2 * (Real.log N) ^ (-3 / 100 : ℝ) + Real.log N * Real.exp (-5 * localizationPower N) := by
    have hPower : (Real.log N) ^ (-1 / 10 : ℝ) * (Real.log N) ^ (7 / 100 : ℝ) =
        (Real.log N) ^ (-3 / 100 : ℝ) := by
      rw [← Real.rpow_add hLPos]
      norm_num
    have hScalePower : (Real.log N) ^ (7 / 100 : ℝ) ≤ Real.log N := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (7 / 100 : ℝ) ≤ 1)
    calc
      _ = 2 * ((Real.log N) ^ (-1 / 10 : ℝ) * (Real.log N) ^ (7 / 100 : ℝ)) +
          (Real.log N) ^ (7 / 100 : ℝ) * Real.exp (-5 * localizationPower N) := by dsimp [B]; ring
      _ ≤ 2 * (Real.log N) ^ (-3 / 100 : ℝ) +
          Real.log N * Real.exp (-5 * localizationPower N) := by
        rw [hPower]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hScalePower
          (Real.exp_nonneg (-5 * localizationPower N)))
  have hCancelPower : (Real.log N) ^ (7 / 100 : ℝ) * (Real.log N) ^ (-7 / 100 : ℝ) = 1 := by
    rw [← Real.rpow_add hLPos]
    norm_num
  have hB : B ≤ (Real.log N) ^ (-7 / 100 : ℝ) / 4 := by
    have hProduct := mul_le_mul_of_nonneg_right (hScale.trans hSmallN.le)
      (Real.rpow_nonneg hLPos.le (-7 / 100 : ℝ))
    calc
      B = (B * (Real.log N) ^ (7 / 100 : ℝ)) * (Real.log N) ^ (-7 / 100 : ℝ) := by
        rw [mul_assoc, hCancelPower, mul_one]
      _ ≤ (1 / 4 : ℝ) * (Real.log N) ^ (-7 / 100 : ℝ) := hProduct
      _ = (Real.log N) ^ (-7 / 100 : ℝ) / 4 := by ring
  have hParameters : (Real.log N) ^ (-7 / 100 : ℝ) ≤ c * η := by
    calc
      _ = (Real.log N) ^ (-3 / 100 : ℝ) * (Real.log N) ^ (-1 / 25 : ℝ) := by
        rw [← Real.rpow_add hLPos]
        norm_num
      _ ≤ c * η := mul_le_mul hcLower hηLower (by positivity) hc.le
  calc
    _ ≤ B / c := hRaw
    _ ≤ ((c * η) / 4) / c := div_le_div_of_nonneg_right
      (hB.trans (div_le_div_of_nonneg_right hParameters (by norm_num))) hc.le
    _ = η / 4 := by field_simp [hc.ne']

theorem eventually_sieve_tail_le_packetDensity :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≤ N) →
      Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * sieveLevel N) ≤ packetDensity N / 4 := by
  filter_upwards [eventually_sieveLevel_tail_bound,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (4 : ℝ))] with N hTail hL P hP
  have hLPos : 0 < Real.log N := by linarith
  calc
    _ ≤ Real.exp (-16 * Real.log (Real.log N)) := hTail P hP
    _ = (Real.log N) ^ (-16 : ℝ) := by
      rw [Real.rpow_def_of_pos hLPos]
      congr 1
      ring
    _ ≤ (Real.log N) ^ ((-7 / 25 : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = packetDensity N / Real.log N := by
      rw [Real.rpow_sub hLPos, Real.rpow_one]
      rfl
    _ ≤ packetDensity N / 4 := div_le_div_of_nonneg_left (packetDensity_pos hLPos).le (by norm_num) hL

theorem eventually_common_sieve_support :
    ∀ᶠ N : ℕ in atTop, 1 ≤
      (∑ p ∈ primeBand (localizationPrimeLower N) (packetCommonBound N), (p : ℝ)⁻¹) -
        2 * Real.log (2 / packetDensity N) := by
  filter_upwards [eventually_common_prime_mass,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_log_coe_at_top.eventually
      (eventually_ge_atTop (100 * (1 + 2 * Real.log 2)))] with N hMass hL hLL
  have hLog : Real.log (packetDensity N) = (-7 / 25 : ℝ) * Real.log (Real.log N) :=
    Real.log_rpow hL _
  rw [Real.log_div (by norm_num) (packetDensity_pos hL).ne', hLog]
  linarith only [hMass.2.2, hLL]

theorem eventually_common_sieve_count :
    ∀ᶠ N : ℕ in atTop, (packetCommonBound N : ℝ) ^ (2 * sieveLevel N) ≤
      packetDensity N * packetMediumBound N / 4 := by
  have hGrowth := (tendsto_stretchedExponent (3 / 5) 1 4 (by norm_num) (by norm_num)).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hGrowth, eventually_sieveLevel_le_loglog_sq,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually
      (eventually_ge_atTop (max 1 (Real.log 2 + Real.log 4)))] with N hGrowthN hLevel hL hLL
  have hLPos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hL
  have hLLPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hLL)
  let v := (Real.log N) ^ (3 / 5 : ℝ)
  let x := v / (16 * (Real.log (Real.log N)) ^ 2)
  have hv : 0 < v := Real.rpow_pos_of_pos hLPos _
  have hx : 0 ≤ x := by dsimp [x]; positivity
  change 1 ≤ v / (4 * (Real.log (Real.log N)) ^ 1) at hGrowthN
  simp only [pow_one] at hGrowthN
  have hVLarge : 4 * Real.log (Real.log N) ≤ v := by
    simpa only [one_mul] using (le_div_iff₀ (by positivity)).mp hGrowthN
  have hLevelR : ((2 * sieveLevel N : ℕ) : ℝ) ≤ 2 * (Real.log (Real.log N)) ^ 2 := by
    exact_mod_cast mul_le_mul_of_nonneg_left hLevel (by norm_num : (0 : ℝ) ≤ 2)
  have hExponent : ((2 * sieveLevel N : ℕ) : ℝ) * x ≤ v / 4 := by
    calc
      _ ≤ (2 * (Real.log (Real.log N)) ^ 2) * x := mul_le_mul_of_nonneg_right hLevelR hx
      _ = v / 8 := by dsimp [x]; field_simp [hLLPos.ne']; ring
      _ ≤ v / 4 := by linarith
  have hCount := floor_exp_pow_le x (v / 4) (2 * sieveLevel N) hx hExponent
  have hLog : Real.log (2 / packetDensity N) + Real.log 4 ≤ 3 * v / 4 := by
    have hLogDensity : Real.log (packetDensity N) =
        (-7 / 25 : ℝ) * Real.log (Real.log N) := Real.log_rpow hLPos _
    rw [Real.log_div (by norm_num) (packetDensity_pos hLPos).ne', hLogDensity]
    have hConst := (le_max_right _ _).trans hLL
    linarith
  have hFinal := exp_quarter_le_density_floor_exp (packetDensity N) v (packetDensity_pos hLPos) hv.le hLog
  change (packetCommonBound N : ℝ) ^ (2 * sieveLevel N) ≤ packetDensity N * packetMediumBound N / 4
  simpa [packetCommonBound, packetMediumBound, stretchedCutoff, stretchedExponent, x, v]
    using hCount.trans hFinal

end Erdos319Sharp
