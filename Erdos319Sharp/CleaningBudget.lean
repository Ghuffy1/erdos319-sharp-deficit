import Erdos319Sharp.Baseline

set_option autoImplicit false

open Filter Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def cleaningBudget (N : ℕ) : ℝ :=
  (Real.log N) ^ (-3 / 100 : ℝ) + (Real.log N) ^ (-(1 / 10 : ℝ)) +
    (Real.log N) ^ (-1 : ℝ) + 2 * (Real.log N) ^ (-(1 / 25 : ℝ)) * Real.log (Real.log N)

theorem eventually_cleaning_log_budget :
    ∀ᶠ N : ℕ in atTop, 2 * Real.log (Real.log N) ≤ (Real.log N) ^ (1 / 100 : ℝ) := by
  have hLimit : Tendsto (fun N : ℕ => Real.log (Real.log N) / (Real.log N) ^ (1 / 100 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).tendsto_div_nhds_zero.comp
        tendsto_log_coe_at_top)
  filter_upwards [hLimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (1 : ℕ)] with N hSmall hN
  have hPos : 0 < (Real.log N) ^ (1 / 100 : ℝ) :=
    Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hN)) _
  have h := (div_lt_iff₀ hPos).mp hSmall
  linarith

theorem eventually_cleaningBudget_le :
    ∀ᶠ N : ℕ in atTop, cleaningBudget N ≤ (Real.log N) ^ (-(1 / 40 : ℝ)) := by
  have hGrow : Tendsto (fun N : ℕ => (Real.log N) ^ (1 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp tendsto_log_coe_at_top
  filter_upwards [eventually_cleaning_log_budget,
    hGrow.eventually (eventually_ge_atTop (4 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hLog hFour hL
  have hLPos : 0 < Real.log N := by linarith
  have hSmooth : (Real.log N) ^ (-(1 / 10 : ℝ)) ≤ (Real.log N) ^ (-3 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hMult : (Real.log N) ^ (-1 : ℝ) ≤ (Real.log N) ^ (-3 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hPrune : 2 * (Real.log N) ^ (-(1 / 25 : ℝ)) * Real.log (Real.log N) ≤
      (Real.log N) ^ (-3 / 100 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hLog
      (Real.rpow_nonneg hLPos.le (-(1 / 25 : ℝ)))
    have hIdentity : (Real.log N) ^ (-(1 / 25 : ℝ)) * (Real.log N) ^ (1 / 100 : ℝ) =
        (Real.log N) ^ (-3 / 100 : ℝ) := by
      rw [← Real.rpow_add hLPos]
      norm_num
    rw [hIdentity] at h
    nlinarith only [h]
  have hPower : (Real.log N) ^ (1 / 200 : ℝ) * (Real.log N) ^ (-3 / 100 : ℝ) =
      (Real.log N) ^ (-(1 / 40 : ℝ)) := by rw [← Real.rpow_add hLPos]; norm_num
  calc
    cleaningBudget N ≤ 4 * (Real.log N) ^ (-3 / 100 : ℝ) := by
      unfold cleaningBudget
      linarith only [hSmooth, hMult, hPrune]
    _ ≤ (Real.log N) ^ (1 / 200 : ℝ) * (Real.log N) ^ (-3 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right hFour (Real.rpow_nonneg hLPos.le _)
    _ = (Real.log N) ^ (-(1 / 40 : ℝ)) := hPower

end Erdos319Sharp
