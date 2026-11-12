import Erdos319Sharp.SharpUpper
import Erdos319Sharp.SharpLower

set_option autoImplicit false

open Filter
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem sharpAsymptotic_proved : SharpAsymptotic :=
  sharpAsymptotic_of_bounds sharpUpperWitnesses_proved sharpLowerBound_proved

theorem erdos319_sharp_deficit :
    Tendsto (fun N : ℕ => ((N : ℝ) - maxSize N) * Real.log (Real.log N) /
      ((N : ℝ) * Real.log (Real.log (Real.log N)))) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := sharpAsymptotic_proved

theorem erdos319_sharp_deficit_ratio :
    Tendsto (fun N : ℕ => ((N : ℝ) - maxSize N) /
      (Real.exp (-Real.eulerMascheroniConstant) * (N : ℝ) *
        Real.log (Real.log (Real.log N)) / Real.log (Real.log N))) atTop (𝓝 1) := by
  have h := erdos319_sharp_deficit.div_const (Real.exp (-Real.eulerMascheroniConstant))
  apply (show Tendsto (fun N : ℕ =>
      (((N : ℝ) - maxSize N) * Real.log (Real.log N) /
        ((N : ℝ) * Real.log (Real.log (Real.log N)))) / Real.exp (-Real.eulerMascheroniConstant))
      atTop (𝓝 1) from by simpa only [div_self (Real.exp_ne_zero _)] using h).congr'
  filter_upwards [eventually_positive_scale] with N hScale
  field_simp [hScale.1.ne', hScale.2.1.ne', hScale.2.2.ne', Real.exp_ne_zero (-Real.eulerMascheroniConstant)]

end Erdos319Sharp
