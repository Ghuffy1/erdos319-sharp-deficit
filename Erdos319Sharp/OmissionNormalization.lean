import Erdos319Sharp.UpperWitnessConstruction
import Erdos319Sharp.DenseDeletion

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def constructionOmissionNormalized (N : ℕ) : ℝ :=
  constructionOmissionBound N * Real.log (Real.log N) /
    ((N : ℝ) * Real.log (Real.log (Real.log N)))

theorem tendsto_loglog_div_constructionMass :
    Tendsto (fun N : ℕ => Real.log (Real.log N) / constructionMass N) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  simpa only [inv_div, Real.exp_neg] using
    tendsto_constructionMass_ratio.inv₀ (Real.exp_ne_zero Real.eulerMascheroniConstant)

theorem tendsto_log_constructionMass_plus_one_ratio :
    Tendsto (fun N : ℕ => (Real.log (constructionMass N) + 1) /
      Real.log (Real.log (Real.log N))) atTop (𝓝 1) := by
  have hLog := tendsto_constructionMass_ratio.log (Real.exp_ne_zero Real.eulerMascheroniConstant)
  have hInverse : Tendsto (fun N : ℕ => (Real.log (Real.log (Real.log N)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_logloglog_nat
  have hError := (hLog.add_const 1).mul hInverse
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  apply (show Tendsto (fun N : ℕ => 1 +
      (Real.log (constructionMass N / Real.log (Real.log N)) + 1) /
        Real.log (Real.log (Real.log N))) atTop (𝓝 1) from
    by simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, add_zero] using hOne.add hError).congr'
  filter_upwards [eventually_positive_scale] with N hScale
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  rw [Real.log_div hMassPos.ne' hScale.2.1.ne']
  field_simp [hScale.2.2.ne']
  <;> ring

theorem tendsto_boundary_normalized_zero :
    Tendsto (fun N : ℕ => (constructionBoundary N : ℝ) * Real.log (Real.log N) /
      ((N : ℝ) * Real.log (Real.log (Real.log N)))) atTop (𝓝 0) := by
  have hInverse : Tendsto (fun N : ℕ => (Real.log (Real.log (Real.log N)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_logloglog_nat
  have h := (tendsto_constructionBoundary_mass_ratio.mul tendsto_loglog_div_constructionMass).mul hInverse
  apply (show Tendsto (fun N : ℕ =>
      ((constructionBoundary N : ℝ) * constructionMass N / N) *
        (Real.log (Real.log N) / constructionMass N) * (Real.log (Real.log (Real.log N)))⁻¹)
      atTop (𝓝 0) from by simpa only [one_mul, mul_zero] using h).congr'
  filter_upwards [eventually_positive_scale] with N hScale
  have hMass : constructionMass N ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)).ne'
  field_simp [hScale.1.ne', hScale.2.2.ne', hMass]

theorem tendsto_target_normalized :
    Tendsto (fun N : ℕ => constructionTarget 1 N * Real.log (Real.log N) /
      Real.log (Real.log (Real.log N))) atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := tendsto_log_constructionMass_plus_one_ratio.mul tendsto_loglog_div_constructionMass
  apply (show Tendsto (fun N : ℕ =>
      ((Real.log (constructionMass N) + 1) / Real.log (Real.log (Real.log N))) *
        (Real.log (Real.log N) / constructionMass N)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) from by simpa only [one_mul] using h).congr'
  filter_upwards [eventually_positive_scale] with N hScale
  have hMass : constructionMass N ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)).ne'
  unfold constructionTarget
  field_simp [hScale.2.2.ne', hMass]

theorem tendsto_primeStep_normalized_zero :
    Tendsto (fun N : ℕ => (1 / (constructionPrimeBase N : ℝ)) * Real.log (Real.log N) /
      Real.log (Real.log (Real.log N))) atTop (𝓝 0) := by
  have hInverse : Tendsto (fun N : ℕ => (Real.log (Real.log (Real.log N)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_logloglog_nat
  have h := (tendsto_constructionMass_div_primeBase.mul tendsto_loglog_div_constructionMass).mul hInverse
  apply (show Tendsto (fun N : ℕ =>
      (constructionMass N / constructionPrimeBase N) *
        (Real.log (Real.log N) / constructionMass N) * (Real.log (Real.log (Real.log N)))⁻¹)
      atTop (𝓝 0) from by simpa only [zero_mul] using h).congr'
  filter_upwards [eventually_positive_scale,
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))] with N hScale hB
  have hMass : constructionMass N ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)).ne'
  have hBase : (constructionPrimeBase N : ℝ) ≠ 0 := by exact_mod_cast (by omega : constructionPrimeBase N ≠ 0)
  field_simp [hScale.2.2.ne', hMass, hBase]

theorem tendsto_smooth_normalized_zero :
    Tendsto (fun N : ℕ => (Real.log N) ^ (-(1 / 10 : ℝ)) * Real.log (Real.log N) /
      Real.log (Real.log (Real.log N))) atTop (𝓝 0) := by
  apply (tendsto_log_power_div_minorityScale_zero (1 / 10) (by norm_num)).congr'
  filter_upwards [eventually_positive_scale] with N hScale
  unfold minorityScale
  field_simp [hScale.2.1.ne', hScale.2.2.ne']

theorem tendsto_constructionOmissionNormalized :
    Tendsto constructionOmissionNormalized atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := ((tendsto_boundary_normalized_zero.add tendsto_target_normalized).add
    tendsto_primeStep_normalized_zero).add tendsto_smooth_normalized_zero
  apply (show Tendsto (fun N : ℕ =>
      (constructionBoundary N : ℝ) * Real.log (Real.log N) / ((N : ℝ) * Real.log (Real.log (Real.log N))) +
        constructionTarget 1 N * Real.log (Real.log N) / Real.log (Real.log (Real.log N)) +
          (1 / (constructionPrimeBase N : ℝ)) * Real.log (Real.log N) / Real.log (Real.log (Real.log N)) +
            (Real.log N) ^ (-(1 / 10 : ℝ)) * Real.log (Real.log N) / Real.log (Real.log (Real.log N)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) from
    by simpa only [zero_add, add_zero] using h).congr'
  filter_upwards [eventually_positive_scale,
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))] with N hScale hB
  have hBase : (constructionPrimeBase N : ℝ) ≠ 0 := by exact_mod_cast (by omega : constructionPrimeBase N ≠ 0)
  unfold constructionOmissionNormalized constructionOmissionBound
  field_simp [hScale.1.ne', hScale.2.2.ne', hBase]
  <;> ring

end Erdos319Sharp
