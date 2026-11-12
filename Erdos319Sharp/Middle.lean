import Erdos319Sharp.Uniform

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem tendsto_tenth_root_decay (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (2 * x + 1) * Real.exp (-b * x ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := by
  have hRoot := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)
  have hPower (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 10 : ℝ)) ^ (10 : ℝ) = x := by
    rw [← Real.rpow_mul hx]
    norm_num
  have hWeighted : Tendsto (fun x : ℝ => x * Real.exp (-b * x ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 10 b hb).comp hRoot
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_def, hPower x hx]
  have hBare : Tendsto (fun x : ℝ => Real.exp (-b * x ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_zero, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb).comp hRoot
  have hSum := (hWeighted.const_mul 2).add hBare
  simp only [mul_zero, zero_add] at hSum
  apply hSum.congr'
  filter_upwards with x using by ring

/-- The middle-frequency decay remains uniform when variance and relative
cardinality have fixed inverse-logarithmic lower bounds. -/
theorem eventually_middle_parameters_of_log_bounds (k l : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ τ C : ℝ,
      1 / (Real.log N) ^ k ≤ τ → (N : ℝ) / (Real.log N) ^ l ≤ C →
      (2 * N + 1 : ℝ) *
        Real.exp (-(8 * τ * C * ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 4 := by
  have hRatio := (tendsto_log_pow_div_nat_rpow (k + l) (1 / 10) (by norm_num)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hDecay := ((tendsto_tenth_root_decay 8 (by norm_num)).comp
    tendsto_natCast_atTop_atTop).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hRatio, hDecay,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hRatioN hDecayN hL hN τ C hτ hC
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hRootPositive : 0 < (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hNR _
  have hLogBound : (Real.log N) ^ (k + l) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    ((div_lt_one hRootPositive).mp hRatioN).le
  have hτPositive : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hProduct : (N : ℝ) / (Real.log N) ^ (k + l) ≤ τ * C := by
    have h := mul_le_mul hτ hC
      (by positivity : 0 ≤ (N : ℝ) / (Real.log N) ^ l) hτPositive.le
    convert h using 1 <;> rw [pow_add] <;> ring
  have hExponent : (N : ℝ) ^ (1 / 10 : ℝ) ≤
      (N : ℝ) ^ (1 / 5 : ℝ) / (Real.log N) ^ (k + l) := by
    apply (le_div_iff₀ (pow_pos hL _)).mpr
    calc
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hLogBound hRootPositive.le
      _ = _ := by rw [← Real.rpow_add hNR]; norm_num
  have hEnergy : 8 * (N : ℝ) ^ (1 / 10 : ℝ) ≤
      8 * τ * C * ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by
    calc
      _ ≤ 8 * ((N : ℝ) ^ (1 / 5 : ℝ) / (Real.log N) ^ (k + l)) :=
        mul_le_mul_of_nonneg_left hExponent (by norm_num)
      _ = 8 * ((N : ℝ) / (Real.log N) ^ (k + l)) *
          ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by
        rw [← middle_exponent_identity (N : ℝ) hNR]
        ring
      _ ≤ _ := by
        have hProductEight : 8 * ((N : ℝ) / (Real.log N) ^ (k + l)) ≤ 8 * τ * C := by
          nlinarith only [hProduct]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hProductEight (sq_nonneg _)) (sq_nonneg _)
  have hExp := Real.exp_le_exp.mpr (neg_le_neg hEnergy)
  exact (mul_le_mul_of_nonneg_left hExp
    (by positivity : (0 : ℝ) ≤ 2 * N + 1)).trans
      (by simpa only [Function.comp_def, neg_mul] using hDecayN.le)

end Erdos319Sharp
