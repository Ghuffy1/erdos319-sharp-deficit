import Erdos319Sharp.Baseline

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem neg_log_one_sub_le_twice (x : ℝ) (hx : 0 ≤ x) (hxHalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hDen : 0 < 1 - x := by linarith
  have hLog := Real.log_le_sub_one_of_pos (inv_pos.mpr hDen)
  rw [Real.log_inv] at hLog
  have hIdentity : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  rw [hIdentity] at hLog
  exact hLog.trans ((div_le_iff₀ hDen).mpr (by nlinarith))

theorem eventually_primePowerTail_log_rate :
    ∀ᶠ N : ℕ in atTop, primePowerTail N (smoothCutoff 6 N) ≤ (Real.log N) ^ (-(1 / 10 : ℝ)) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨C, hC, hBound⟩ := hb.exists_pos
  have hSmall : Tendsto (fun N : ℕ => 6 * (Real.log N) ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_log_coe_at_top).const_mul 6
  have hLarge : Tendsto (fun N : ℕ => (Real.log N) ^ (1 / 10 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp tendsto_log_coe_at_top
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hBound.bound,
    (tendsto_smoothCutoff 6).eventually hBound.bound,
    hSmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hLarge.eventually (eventually_ge_atTop (3 * C + 12)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with N hEN hES hSmallN hLargeN hL hN
  have hLPos : 0 < Real.log N := by linarith
  let x := 6 * (Real.log N) ^ (-(1 / 5 : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxHalf : x ≤ 1 / 2 := hSmallN.le
  have hPower : (Real.log N) ^ (-(1 / 5 : ℝ)) * Real.log N = (Real.log N) ^ (4 / 5 : ℝ) := by
    calc
      _ = (Real.log N) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log N) ^ (4 / 5 : ℝ) := by rw [← Real.rpow_add hLPos]; norm_num
  have hLogS : Real.log (smoothCutoff 6 N) = (1 - x) * Real.log N := by
    rw [log_smoothCutoff 6 (by omega)]
    dsimp [x]
    nlinarith only [hPower]
  have hLogSPos : 0 < Real.log (smoothCutoff 6 N) := by
    rw [hLogS]
    exact mul_pos (by linarith) hLPos
  have hLogSLower : (1 / 2 : ℝ) * Real.log N ≤ Real.log (smoothCutoff 6 N) := by
    rw [hLogS]
    nlinarith only [mul_le_mul_of_nonneg_right hxHalf hLPos.le]
  have hErrorN : |primePowerRecipSum N - (Real.log (Real.log N) + b)| ≤ C / Real.log N := by
    simpa only [primePowerRecipSum, one_div, Nat.floor_natCast, Real.norm_eq_abs,
      abs_inv, abs_of_pos hLPos, div_eq_mul_inv, one_mul] using hEN
  have hErrorS : |primePowerRecipSum (smoothCutoff 6 N) -
      (Real.log (Real.log (smoothCutoff 6 N)) + b)| ≤ C / Real.log (smoothCutoff 6 N) := by
    simpa only [primePowerRecipSum, one_div, Real.norm_eq_abs,
      abs_inv, abs_of_pos hLogSPos, div_eq_mul_inv, one_mul] using hES
  have hErrorSBound : C / Real.log (smoothCutoff 6 N) ≤ 2 * C / Real.log N := by
    calc
      _ ≤ C / ((1 / 2) * Real.log N) :=
        div_le_div_of_nonneg_left hC.le (by positivity) hLogSLower
      _ = _ := by ring
  have hLogDifference : Real.log (Real.log N) - Real.log (Real.log (smoothCutoff 6 N)) ≤
      12 * (Real.log N) ^ (-(1 / 5 : ℝ)) := by
    rw [hLogS, Real.log_mul (by linarith : 1 - x ≠ 0) hLPos.ne']
    have h := neg_log_one_sub_le_twice x hx hxHalf
    dsimp [x] at h
    linarith
  have hTail : primePowerTail N (smoothCutoff 6 N) ≤
      3 * C / Real.log N + 12 * (Real.log N) ^ (-(1 / 5 : ℝ)) := by
    rw [primePowerTail_eq_difference (smoothCutoff_pos 6 (by omega)).le (smoothCutoff_le 6 (by norm_num) N)]
    have hUpper := (abs_le.mp hErrorN).2
    have hLower := (abs_le.mp hErrorS).1
    have hThree : 3 * C / Real.log N = C / Real.log N + 2 * C / Real.log N := by ring
    rw [hThree]
    linarith only [hUpper, hLower, hLogDifference, hErrorSBound]
  have hInv : (Real.log N)⁻¹ ≤ (Real.log N) ^ (-(1 / 5 : ℝ)) := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (-1 : ℝ) ≤ -(1 / 5 : ℝ))
  calc
    primePowerTail N (smoothCutoff 6 N) ≤
        3 * C / Real.log N + 12 * (Real.log N) ^ (-(1 / 5 : ℝ)) := hTail
    _ ≤ (3 * C + 12) * (Real.log N) ^ (-(1 / 5 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 3 * C by positivity)
      simp only [div_eq_mul_inv]
      nlinarith only [h]
    _ ≤ (Real.log N) ^ (1 / 10 : ℝ) * (Real.log N) ^ (-(1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_right hLargeN (Real.rpow_nonneg hLPos.le _)
    _ = (Real.log N) ^ (-(1 / 10 : ℝ)) := by rw [← Real.rpow_add hLPos]; norm_num

end Erdos319Sharp
