import Erdos319Sharp.ConstructionMassWindow
import Erdos319Sharp.BoundaryScales
import Erdos319Sharp.SmoothTailRate

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def constructionPrimeLoss (η : ℝ) (N : ℕ) : ℝ :=
  (constructionTarget η N + 1 / constructionPrimeBase N) *
    (1 + Real.log (4 * constructionMass N))

def constructionSmoothLoss (N : ℕ) : ℝ :=
  2 * constructionMass N * (Real.log N) ^ (-(1 / 10 : ℝ))

def constructionBulkError (η : ℝ) (N : ℕ) : ℝ :=
  |(harmonic N : ℝ) - (harmonic (constructionBoundary N) : ℝ) - Real.log (constructionMass N)| +
    constructionPrimeLoss η N + constructionSmoothLoss N

theorem tendsto_log_affine_product_div (c d : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x + c) * (Real.log x + d) / x) atTop (𝓝 0) := by
  have hSquare : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hLinear := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul (c + d)
  have hConstant := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (c * d)
  apply (show Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x +
      (c + d) * (Real.log x / x) + c * d * x⁻¹) atTop (𝓝 0) from
    by simpa only [id_eq, mul_zero, zero_add, add_zero] using (hSquare.add hLinear).add hConstant).congr'
  filter_upwards with x
  ring

theorem tendsto_log_constructionMass_div_primeBase :
    Tendsto (fun N : ℕ => Real.log (constructionMass N) / constructionPrimeBase N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    div_nonneg (Real.log_nonneg (constructionMass_one_le N)) (Nat.cast_nonneg _))) ?_
    tendsto_constructionMass_div_primeBase
  filter_upwards with N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := Real.log_le_sub_one_of_pos
    (lt_of_lt_of_le (by norm_num) (constructionMass_one_le N))
  linarith

theorem tendsto_constructionPrimeLoss (η : ℝ) :
    Tendsto (constructionPrimeLoss η) atTop (𝓝 0) := by
  let d : ℝ := 1 + Real.log 4
  have hFirst := (tendsto_log_affine_product_div η d).comp tendsto_constructionMass
  have hInverse : Tendsto (fun N : ℕ => (1 : ℝ) / constructionPrimeBase N) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_constructionPrimeBase)
  have hSecond : Tendsto (fun N : ℕ =>
      (Real.log (constructionMass N) + d) / constructionPrimeBase N) atTop (𝓝 0) := by
    apply (show Tendsto (fun N : ℕ => Real.log (constructionMass N) / constructionPrimeBase N +
        d * (1 / constructionPrimeBase N)) atTop (𝓝 0) from
      by simpa only [mul_zero, add_zero] using
        tendsto_log_constructionMass_div_primeBase.add (hInverse.const_mul d)).congr'
    filter_upwards with N
    ring
  apply (show Tendsto (fun N : ℕ =>
      (Real.log (constructionMass N) + η) * (Real.log (constructionMass N) + d) / constructionMass N +
        (Real.log (constructionMass N) + d) / constructionPrimeBase N) atTop (𝓝 0) from
    by simpa only [Function.comp_def, zero_add] using hFirst.add hSecond).congr'
  filter_upwards with N
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  unfold constructionPrimeLoss constructionTarget d
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hMassPos.ne']
  ring

theorem tendsto_constructionMass_div_log_power (s : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => constructionMass N / (Real.log N) ^ s) atTop (𝓝 0) := by
  have hSmall : Tendsto (fun N : ℕ => Real.log (Real.log N) / (Real.log N) ^ s) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hs).tendsto_div_nhds_zero.comp tendsto_log_coe_at_top
  have h := tendsto_constructionMass_ratio.mul hSmall
  apply (show Tendsto (fun N : ℕ =>
      (constructionMass N / Real.log (Real.log N)) *
        (Real.log (Real.log N) / (Real.log N) ^ s)) atTop (𝓝 0) from
    by simpa only [mul_zero] using h).congr'
  filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLL hL
  field_simp [hLL.ne', (Real.rpow_pos_of_pos hL s).ne']

theorem tendsto_constructionSmoothLoss : Tendsto constructionSmoothLoss atTop (𝓝 0) := by
  have h := (tendsto_constructionMass_div_log_power (1 / 10) (by norm_num)).const_mul 2
  apply (show Tendsto (fun N : ℕ => 2 * (constructionMass N / (Real.log N) ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) from by simpa only [mul_zero] using h).congr'
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLog
  simp only [constructionSmoothLoss, Real.rpow_neg hLog.le, div_eq_mul_inv]
  ring

theorem tendsto_constructionBulkError (η : ℝ) :
    Tendsto (constructionBulkError η) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ =>
    |(harmonic N : ℝ) - (harmonic (constructionBoundary N) : ℝ) - Real.log (constructionMass N)| +
      constructionPrimeLoss η N + constructionSmoothLoss N) atTop (𝓝 0)
  simpa only [abs_zero, zero_add] using
    (tendsto_constructionBoundary_harmonic_gap.abs.add (tendsto_constructionPrimeLoss η)).add
      tendsto_constructionSmoothLoss

end Erdos319Sharp
