import Erdos319Sharp.DenseDeletion

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def lowerOmissionError (a : ℝ) (N : ℕ) : ℝ :=
  2 * (Real.log N) ^ (-(1 / 10 : ℝ)) + (Real.log N) ^ (-(1 / 40 : ℝ)) +
    (Real.log (1 / a) + 5) * (Real.log N) ^ (-1 : ℝ)

theorem tendsto_lowerOmissionError_ratio_zero (a : ℝ) :
    Tendsto (fun N : ℕ => lowerOmissionError a N / minorityScale N) atTop (𝓝 0) := by
  have hFirst := (tendsto_log_power_div_minorityScale_zero (1 / 10) (by norm_num)).const_mul 2
  have hSecond := tendsto_log_power_div_minorityScale_zero (1 / 40) (by norm_num)
  have hThird := (tendsto_log_power_div_minorityScale_zero 1 (by norm_num)).const_mul
    (Real.log (1 / a) + 5)
  have hSum : Tendsto (fun N : ℕ =>
      2 * ((Real.log N) ^ (-(1 / 10 : ℝ)) / minorityScale N) +
        (Real.log N) ^ (-(1 / 40 : ℝ)) / minorityScale N +
          (Real.log (1 / a) + 5) * ((Real.log N) ^ (-1 : ℝ) / minorityScale N))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (hFirst.add hSecond).add hThird
  apply hSum.congr'
  filter_upwards with N
  unfold lowerOmissionError
  ring

theorem eventually_smoothCutoff_le_div_log :
    ∀ᶠ N : ℕ in atTop, smoothCutoff 6 N ≤ (N : ℝ) / Real.log N := by
  filter_upwards [(tendsto_log_times_smooth_factor 6 (by norm_num)).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hSmall hLog
  unfold smoothCutoff
  have hBound : Real.exp (-6 * (Real.log N) ^ (4 / 5 : ℝ)) ≤ 1 / Real.log N :=
    (le_div_iff₀ hLog).mpr (by nlinarith only [hSmall])
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hBound (Nat.cast_nonneg N)

theorem exists_lower_bound_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ a θ : ℝ, 0 < a ∧ 3 ≤ Real.log (1 / a) ∧ 0 < θ ∧
      0 < 1 - 2 * a - θ - 2 * θ * Real.exp (2 * θ) ∧
      Real.exp (-Real.eulerMascheroniConstant) - ε / 2 <
        (1 - 2 * a - θ - 2 * θ * Real.exp (2 * θ)) *
          (Real.exp (-Real.eulerMascheroniConstant) - θ) := by
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let a : ℕ → ℝ := fun k => Real.exp (-(k : ℝ))
  let W : ℕ → ℝ := fun k => 1 - 2 * a k - u k - 2 * u k * Real.exp (2 * u k)
  have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, Function.comp_def] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hFirst : Tendsto (fun k => 1 - 2 * a k - u k) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (ha.const_mul 2)).sub hu
  have hTwo : Tendsto (fun k => 2 * u k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hu.const_mul 2
  have hExp : Tendsto (fun k => Real.exp (2 * u k)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto (0 : ℝ)).comp hTwo
  have hSecond : Tendsto (fun k => 2 * u k * Real.exp (2 * u k)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hTwo.mul hExp
  have hW : Tendsto W atTop (𝓝 1) := by
    simpa only [W, sub_zero] using hFirst.sub hSecond
  have hTarget : Tendsto (fun k => W k * (Real.exp (-Real.eulerMascheroniConstant) - u k))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa only [sub_zero, one_mul] using hW.mul (tendsto_const_nhds.sub hu)
  obtain ⟨k, hkPos, hkClose, hk⟩ := ((hW.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
    ((hTarget.eventually (Ioi_mem_nhds (by linarith : Real.exp (-Real.eulerMascheroniConstant) - ε / 2 <
      Real.exp (-Real.eulerMascheroniConstant)))).and (eventually_ge_atTop (3 : ℕ)))).exists
  refine ⟨a k, u k, Real.exp_pos _, ?_, ?_, hkPos, hkClose⟩
  · dsimp [a]
    rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
    exact_mod_cast hk
  · dsimp [u]
    positivity

end Erdos319Sharp
