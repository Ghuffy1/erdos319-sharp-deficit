import Erdos319Sharp.MinorityBand

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem tendsto_minority_endpoint_log_ratio :
    Tendsto (fun N : ℕ => Real.log (minorityLower N) / Real.log (minorityUpper N))
      atTop (𝓝 0) := by
  have h := (tendsto_log_minorityLower_div_logloglog.mul tendsto_minorityScale_zero).div
    tendsto_log_minorityUpper_div_loglog (by norm_num : (1 / 100 : ℝ) ≠ 0)
  apply (show Tendsto (fun N : ℕ =>
    (Real.log (minorityLower N) / Real.log (Real.log (Real.log N)) * minorityScale N) /
      (Real.log (minorityUpper N) / Real.log (Real.log N))) atTop (𝓝 0) by
    simpa only [Pi.div_def, mul_zero, zero_div] using h).congr'
  filter_upwards [eventually_positive_scale] with N hN
  dsimp [minorityScale]
  field_simp [hN.2.1.ne', hN.2.2.ne']

theorem eventually_minority_endpoint_order :
    ∀ᶠ N : ℕ in atTop, minorityLower N ≤ minorityUpper N := by
  filter_upwards [
    tendsto_minority_endpoint_log_ratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_minorityLower.eventually (eventually_ge_atTop (2 : ℕ)),
    tendsto_minorityUpper.eventually (eventually_ge_atTop (2 : ℕ))]
    with N hRatio hLower hUpper
  have hLowerPos : (0 : ℝ) < minorityLower N := by exact_mod_cast (by omega : 0 < minorityLower N)
  have hUpperOne : (1 : ℝ) < minorityUpper N := by exact_mod_cast (by omega : 1 < minorityUpper N)
  have hLogUpper : 0 < Real.log (minorityUpper N) := Real.log_pos hUpperOne
  have hLogs : Real.log (minorityLower N) < Real.log (minorityUpper N) := by
    simpa only [one_mul] using (div_lt_iff₀ hLogUpper).mp hRatio
  have hOrder := (Real.log_lt_log_iff hLowerPos (zero_lt_one.trans hUpperOne)).mp hLogs
  exact_mod_cast hOrder.le

theorem primeAvoidanceDensity_primeInterval (a b : ℕ) (hab : a ≤ b) :
    primeAvoidanceDensity (primeInterval a b) = primeProduct b / primeProduct a := by
  apply (eq_div_iff (primeProduct_pos a).ne').mpr
  simpa only [primeAvoidanceDensity, primeInterval, primeProduct, Nat.primesLE_eq_filter_range] using
    (Finset.prod_sdiff (f := fun p : ℕ => (1 - (1 : ℝ) / p)) (Nat.primesLE_mono hab))

theorem tendsto_minority_density_ratio :
    Tendsto (fun N : ℕ => primeAvoidanceDensity (minorityPrimeBand N) / minorityScale N)
      atTop (𝓝 200) := by
  have hMertens : Tendsto (fun N : ℕ =>
      (primeProduct (minorityUpper N) * Real.log (minorityUpper N)) /
        (primeProduct (minorityLower N) * Real.log (minorityLower N))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Pi.div_def, div_self (Real.exp_ne_zero _)] using
      (tendsto_primeProduct_mul_log.comp tendsto_minorityUpper).div
        (tendsto_primeProduct_mul_log.comp tendsto_minorityLower) (Real.exp_ne_zero _)
  have h := (hMertens.mul tendsto_log_minorityLower_div_logloglog).div
    tendsto_log_minorityUpper_div_loglog (by norm_num : (1 / 100 : ℝ) ≠ 0)
  apply (show Tendsto (fun N : ℕ =>
    ((primeProduct (minorityUpper N) * Real.log (minorityUpper N)) /
      (primeProduct (minorityLower N) * Real.log (minorityLower N)) *
      (Real.log (minorityLower N) / Real.log (Real.log (Real.log N)))) /
      (Real.log (minorityUpper N) / Real.log (Real.log N))) atTop (𝓝 200) by
    convert h using 1 <;> norm_num).congr'
  filter_upwards [eventually_positive_scale, eventually_minority_endpoint_order,
    tendsto_minorityLower.eventually (eventually_ge_atTop (2 : ℕ)),
    tendsto_minorityUpper.eventually (eventually_ge_atTop (2 : ℕ))]
    with N hN hOrder hLower hUpper
  have hLogLower : 0 < Real.log (minorityLower N) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < minorityLower N))
  have hLogUpper : 0 < Real.log (minorityUpper N) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < minorityUpper N))
  rw [minorityPrimeBand, primeAvoidanceDensity_primeInterval _ _ hOrder]
  dsimp [minorityScale]
  field_simp [(primeProduct_pos (minorityLower N)).ne', hLogLower.ne', hLogUpper.ne',
    hN.2.1.ne', hN.2.2.ne']

theorem tendsto_minority_density_zero :
    Tendsto (fun N : ℕ => primeAvoidanceDensity (minorityPrimeBand N)) atTop (𝓝 0) := by
  have h := tendsto_minority_density_ratio.mul tendsto_minorityScale_zero
  apply (show Tendsto (fun N : ℕ =>
    (primeAvoidanceDensity (minorityPrimeBand N) / minorityScale N) * minorityScale N)
    atTop (𝓝 0) by simpa using h).congr'
  filter_upwards [eventually_positive_scale] with N hN
  have hScale : minorityScale N ≠ 0 := div_ne_zero hN.2.2.ne' hN.2.1.ne'
  exact div_mul_cancel₀ _ hScale

theorem eventually_minorityPrimeBand_conditions :
    ∀ᶠ N : ℕ in atTop, (minorityPrimeBand N).Nonempty ∧
      (∀ p ∈ minorityPrimeBand N, p.Prime ∧ (Real.log (Real.log N)) ^ 2 ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ)) := by
  filter_upwards [tendsto_minority_density_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ))]
    with N hDensity hL
  constructor
  · by_contra hEmpty
    have hEq := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    simpa [hEq, primeAvoidanceDensity] using hDensity
  · intro p hp
    obtain ⟨hPrime, hLower, hUpper⟩ := mem_primeInterval.mp hp
    refine ⟨hPrime, ?_, ?_⟩
    · have hCeil : (Real.log (Real.log N)) ^ 2 ≤ (minorityLower N : ℝ) := Nat.le_ceil _
      exact hCeil.trans (by exact_mod_cast hLower.le)
    · have hFloor : (minorityUpper N : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ) :=
        Nat.floor_le (Real.rpow_nonneg hL _)
      have hUpperR : (p : ℝ) ≤ minorityUpper N := by exact_mod_cast hUpper
      exact hUpperR.trans hFloor

end Erdos319Sharp
