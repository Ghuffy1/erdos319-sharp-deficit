import Erdos319Sharp.ExactTarget
import Erdos319Sharp.Fourier

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem tendsto_log_pow_div_nat_rpow (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => (Real.log N) ^ k / (N : ℝ) ^ s) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_natCast] using
    h.comp tendsto_natCast_atTop_atTop

/-- The smooth-lcm bounds hold uniformly when the minimum denominator
fraction has a fixed inverse-logarithmic lower bound. -/
theorem eventually_uniform_smooth_lcm_log_growth (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ,
      0 < c → 1 / (Real.log N) ^ k ≤ c →
      ∀ A : Finset ℕ,
        (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
        ((A.lcm id : ℕ) : ℝ) ≤ Real.exp (((c * N) ^ 2 / N) / 4) ∧
          Real.log 4 < ((c * N) ^ 2 / N) / 4 := by
  have hTail :=
    (tendsto_log_pow_mul_exp_neg_localizationPower (2 * k + 1) 6 (by norm_num)).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hLogFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hRatio := (tendsto_log_pow_div_nat_rpow (2 * k) 1 (by norm_num)).eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * Real.log 4)))
  filter_upwards [hTail, hRatio,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    (tendsto_smoothCutoff 6).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hTailN hRatioN hL hS hN c hc hcLower A hSmooth
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLP : 0 < (Real.log N) ^ (2 * k) := pow_pos hL _
  have hPower : (Real.log N) ^ (2 * k) = ((Real.log N) ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  have hcSquare : 1 / (Real.log N) ^ (2 * k) ≤ c ^ 2 := by
    rw [hPower, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hcLower 2
  have hTailProduct : (Real.log N) ^ (2 * k) *
      (Real.log N * Real.exp (-6 * localizationPower N)) ≤ 1 / 4 := by
    simpa only [pow_succ, mul_assoc] using hTailN.le
  have hTailBound : Real.log N * Real.exp (-6 * localizationPower N) ≤
      (1 / (Real.log N) ^ (2 * k)) / 4 := by
    rw [div_right_comm]
    exact (le_div_iff₀ hLP).mpr (by simpa only [mul_comm] using hTailProduct)
  have hTailC : Real.log N * Real.exp (-6 * localizationPower N) ≤ c ^ 2 / 4 :=
    hTailBound.trans (div_le_div_of_nonneg_right hcSquare (by norm_num))
  have hRatioN' : (Real.log N) ^ (2 * k) / (N : ℝ) < 1 / (4 * Real.log 4) := by
    simpa only [Real.rpow_one] using hRatioN
  have hCross := (div_lt_div_iff₀ hNR (by positivity : (0 : ℝ) < 4 * Real.log 4)).mp hRatioN'
  have hSizeBase : Real.log 4 < (N : ℝ) / (4 * (Real.log N) ^ (2 * k)) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Real.log N) ^ (2 * k))).mpr
    nlinarith only [hCross]
  have hSize : Real.log 4 < (c ^ 2 / 4) * N := by
    apply hSizeBase.trans_le
    calc
      (N : ℝ) / (4 * (Real.log N) ^ (2 * k)) =
          ((1 / (Real.log N) ^ (2 * k)) / 4) * N := by ring
      _ ≤ (c ^ 2 / 4) * N :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcSquare (by norm_num)) hNR.le
  have hSpos := smoothCutoff_pos 6 hN
  have hLogS : Real.log (smoothCutoff 6 N) ≤ Real.log N :=
    Real.log_le_log hSpos (smoothCutoff_le 6 (by norm_num) N)
  have hExponent : smoothCutoff 6 N * Real.log (smoothCutoff 6 N) ≤ (c ^ 2 / 4) * N := by
    calc
      _ ≤ smoothCutoff 6 N * Real.log N := mul_le_mul_of_nonneg_left hLogS hSpos.le
      _ = (Real.log N * Real.exp (-6 * localizationPower N)) * N := by
        unfold smoothCutoff localizationPower
        ring
      _ ≤ (c ^ 2 / 4) * N := mul_le_mul_of_nonneg_right hTailC hNR.le
  have hForm : ((c * N) ^ 2 / (N : ℝ)) / 4 = (c ^ 2 / 4) * N := by
    field_simp [hNR.ne']
  rw [hForm]
  exact ⟨(smooth_lcm_le_exp A (smoothCutoff 6 N) hS hSmooth).trans
    (Real.exp_le_exp.mpr hExponent), hSize⟩

end Erdos319Sharp
