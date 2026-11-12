import Erdos319Sharp.Uniform

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- Major-arc parameters are uniform above any fixed inverse-logarithmic
lower bound for the minimum denominator fraction. -/
theorem eventually_major_parameters_of_log_bound (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → 1 / (Real.log N) ^ k ≤ c →
      (N : ℝ) ^ (3 / 5 : ℝ) ≤ c * N / 2 ∧
      2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (c * N) ≤ 1 ∧
      (2 * Real.exp 1) * (N * (2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (c * N)) ^ 3) ≤
        Real.log (3 / 2) := by
  have hAngleLimit : Tendsto (fun N : ℕ =>
      (2 * Real.pi) * ((Real.log N) ^ k / (N : ℝ) ^ (2 / 5 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_log_pow_div_nat_rpow k (2 / 5) (by norm_num)).const_mul (2 * Real.pi)
  have hBudgetLimit : Tendsto (fun N : ℕ =>
      ((2 * Real.exp 1) * (2 * Real.pi) ^ 3) *
        ((Real.log N) ^ (3 * k) / (N : ℝ) ^ (1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_log_pow_div_nat_rpow (3 * k) (1 / 5) (by norm_num)).const_mul
        ((2 * Real.exp 1) * (2 * Real.pi) ^ 3)
  filter_upwards [hAngleLimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hBudgetLimit.eventually (Iio_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2))),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hAngleSmall hBudgetSmall hL hN c hc hcLower
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hInverse : c⁻¹ ≤ (Real.log N) ^ k := by
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / (Real.log N) ^ k) hcLower
  have hCoefficient : 2 * Real.pi / c ≤ (2 * Real.pi) * (Real.log N) ^ k := by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hInverse (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have hAngleBound : 2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (c * N) ≤
      (2 * Real.pi) * ((Real.log N) ^ k / (N : ℝ) ^ (2 / 5 : ℝ)) := by
    rw [major_angle_identity c (N : ℝ) hNR]
    calc
      _ ≤ ((2 * Real.pi) * (Real.log N) ^ k) * (N : ℝ) ^ (-(2 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_right hCoefficient (Real.rpow_nonneg hNR.le _)
      _ = _ := by rw [Real.rpow_neg hNR.le]; ring
  have hPower : ((Real.log N) ^ k) ^ 3 = (Real.log N) ^ (3 * k) := by
    rw [← pow_mul, Nat.mul_comm k 3]
  have hBudgetBound : (2 * Real.exp 1) *
      (N * (2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (c * N)) ^ 3) ≤
      ((2 * Real.exp 1) * (2 * Real.pi) ^ 3) *
        ((Real.log N) ^ (3 * k) / (N : ℝ) ^ (1 / 5 : ℝ)) := by
    rw [major_cubic_identity c (N : ℝ) hNR]
    calc
      _ ≤ ((2 * Real.exp 1) * ((2 * Real.pi) * (Real.log N) ^ k) ^ 3) *
          (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
        gcongr
      _ = _ := by rw [mul_pow, hPower, Real.rpow_neg hNR.le]; ring
  have hAngle := hAngleBound.trans_lt hAngleSmall
  have hMultiply : 2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) < c * N :=
    (div_lt_one (mul_pos hc hNR)).mp hAngle
  have hPi : (1 : ℝ) ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hNonnegative : 0 ≤ (N : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_nonneg hNR.le _
  refine ⟨?_, hAngle.le, (hBudgetBound.trans_lt hBudgetSmall).le⟩
  nlinarith [mul_le_mul_of_nonneg_right hPi hNonnegative]

end Erdos319Sharp
