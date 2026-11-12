import Erdos319Sharp.MinorityError

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def minorityCoefficient (N : ℕ) : ℝ :=
  Real.sqrt (primeAvoidanceDensity (minorityPrimeBand N)) /
    (1 - Real.sqrt (primeAvoidanceDensity (minorityPrimeBand N)))

def minorityMainTerm (N : ℕ) : ℝ :=
  primeAvoidanceDensity (minorityPrimeBand N) / minorityScale N +
    (minorityCoefficient N + 1) *
      (minorityBandError (minorityPrimeBand N) N / ((N : ℝ) * minorityScale N))

theorem tendsto_minorityCoefficient_zero : Tendsto minorityCoefficient atTop (𝓝 0) := by
  have hRoot := Real.continuous_sqrt.tendsto 0 |>.comp tendsto_minority_density_zero
  have h := hRoot.div (tendsto_const_nhds.sub hRoot) (by norm_num : (1 : ℝ) - Real.sqrt 0 ≠ 0)
  change Tendsto (fun N : ℕ => Real.sqrt (primeAvoidanceDensity (minorityPrimeBand N)) /
    (1 - Real.sqrt (primeAvoidanceDensity (minorityPrimeBand N)))) atTop (𝓝 0)
  simpa only [Pi.div_def, Function.comp_def, Real.sqrt_zero, sub_zero, zero_div] using h

theorem tendsto_minorityMainTerm : Tendsto minorityMainTerm atTop (𝓝 200) := by
  have h := tendsto_minority_density_ratio.add
    ((tendsto_minorityCoefficient_zero.add_const 1).mul tendsto_minority_error_ratio_zero)
  change Tendsto (fun N : ℕ => primeAvoidanceDensity (minorityPrimeBand N) / minorityScale N +
    (minorityCoefficient N + 1) *
      (minorityBandError (minorityPrimeBand N) N / ((N : ℝ) * minorityScale N))) atTop (𝓝 200)
  simpa only [add_zero, mul_zero] using h

theorem tendsto_minority_threshold_ratio :
    Tendsto (fun N : ℕ => 4 /
      (Real.log (Real.log N) * Real.log (Real.log (Real.log N)))) atTop (𝓝 0) := by
  have h := ((tendsto_inv_atTop_zero.comp tendsto_log_log_coe_at_top).mul
    (tendsto_inv_atTop_zero.comp tendsto_logloglog_nat)).const_mul 4
  simpa only [Function.comp_def, div_eq_mul_inv, mul_inv, mul_assoc, mul_zero] using h

theorem eventually_minority_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ →
      min ((positivePart A δ).card : ℝ) ((negativePart A δ).card : ℝ) ≤
        (200 + ε) * ((N : ℝ) * minorityScale N) + ε * ((N - A.card : ℕ) : ℝ) := by
  filter_upwards [eventually_minority_prime_band_bound, eventually_minorityPrimeBand_conditions,
    eventually_positive_scale,
    tendsto_minorityMainTerm.eventually (Iio_mem_nhds (by linarith : (200 : ℝ) < 200 + ε)),
    tendsto_minorityCoefficient_zero.eventually (Iio_mem_nhds hε),
    tendsto_minority_threshold_ratio.eventually (Iio_mem_nhds hε)]
    with N hFinite hBand hN hMain hCoefficient hThreshold
  intro A δ hA hPrimitive
  have hScale : 0 < minorityScale N := div_pos hN.2.2 hN.2.1
  have hSizeScale : 0 < (N : ℝ) * minorityScale N := mul_pos hN.1 hScale
  have hDeficit : (0 : ℝ) ≤ ((N - A.card : ℕ) : ℝ) := Nat.cast_nonneg _
  apply (hFinite A δ (minorityPrimeBand N) hA hPrimitive hBand.1 hBand.2).trans
  apply max_le
  · have hEquality : 4 * (N : ℝ) / (Real.log (Real.log N)) ^ 2 =
        (4 / (Real.log (Real.log N) * Real.log (Real.log (Real.log N)))) *
          ((N : ℝ) * minorityScale N) := by
      dsimp [minorityScale]
      field_simp [hN.2.1.ne', hN.2.2.ne']
    rw [hEquality]
    have hSmall := mul_le_mul_of_nonneg_right hThreshold.le hSizeScale.le
    have hExtra := mul_nonneg hε.le hDeficit
    nlinarith only [hSmall, hExtra, hSizeScale.le]
  · have hEquality : minorityEstimate N A (minorityPrimeBand N) =
        ((N : ℝ) * minorityScale N) * minorityMainTerm N +
          minorityCoefficient N * ((N - A.card : ℕ) : ℝ) := by
      unfold minorityEstimate minorityMainTerm
      change (N : ℝ) * primeAvoidanceDensity (minorityPrimeBand N) +
        minorityCoefficient N * (((N - A.card : ℕ) : ℝ) + minorityBandError (minorityPrimeBand N) N) +
          minorityBandError (minorityPrimeBand N) N =
        ((N : ℝ) * minorityScale N) *
          (primeAvoidanceDensity (minorityPrimeBand N) / minorityScale N +
            (minorityCoefficient N + 1) *
              (minorityBandError (minorityPrimeBand N) N / ((N : ℝ) * minorityScale N))) +
          minorityCoefficient N * ((N - A.card : ℕ) : ℝ)
      field_simp [hN.1.ne', hScale.ne']
      <;> ring
    rw [hEquality]
    have hMainBound := mul_le_mul_of_nonneg_left hMain.le hSizeScale.le
    have hDeficitBound := mul_le_mul_of_nonneg_right hCoefficient.le hDeficit
    nlinarith only [hMainBound, hDeficitBound]

end Erdos319Sharp
