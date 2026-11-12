import Erdos319Sharp.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

open Filter
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- The number of omitted denominators, interpreted in the real numbers. -/
def deficit (N : ℕ) : ℝ := (N : ℝ) - maxSize N

def normalizedDeficit (N : ℕ) : ℝ :=
  deficit N * Real.log (Real.log (N : ℝ)) /
    ((N : ℝ) * Real.log (Real.log (Real.log (N : ℝ))))

/-- The full sharp asymptotic required by the research goal. -/
def SharpAsymptotic : Prop :=
  Tendsto normalizedDeficit atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

theorem deficit_nonneg (N : ℕ) : 0 ≤ deficit N := by
  unfold deficit
  exact sub_nonneg.mpr (by exact_mod_cast maxSize_le N)

theorem deficit_eq_nat_sub (N : ℕ) :
    deficit N = ((N - maxSize N : ℕ) : ℝ) := by
  simp [deficit, Nat.cast_sub (maxSize_le N)]

theorem tendsto_logloglog_nat :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem eventually_positive_scale :
    ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) ∧
      0 < Real.log (Real.log (N : ℝ)) ∧
      0 < Real.log (Real.log (Real.log (N : ℝ))) := by
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_logloglog_nat.eventually (eventually_gt_atTop (0 : ℝ))] with N hN h₂ h₃
  exact ⟨by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN), h₂, h₃⟩

theorem eventually_normalizedDeficit_nonneg :
    ∀ᶠ N : ℕ in atTop, 0 ≤ normalizedDeficit N := by
  filter_upwards [eventually_positive_scale] with N hN
  exact div_nonneg (mul_nonneg (deficit_nonneg N) hN.2.1.le)
    (mul_pos hN.1 hN.2.2).le

end Erdos319Sharp
