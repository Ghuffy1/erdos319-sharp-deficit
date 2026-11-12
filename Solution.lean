import Erdos319Sharp
import Submission

/-!
The original fixed-sign maximum and the sharp asymptotic for Erdős 319.
The literal sign condition is defined in Submission.lean. The same sign
function is restricted to every proper nonempty subset.
-/

open Filter
open scoped Topology

namespace Erdos319Jsp

def IsOriginalMaximum (N k : ℕ) : Prop :=
  IsGreatest
    {j : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      Erdos319Submission.LiteralPrimitive A ∧ A.card = j} k

theorem maximum_correspondence (N : ℕ) :
    IsOriginalMaximum N (Erdos319Formal.maxSize N) :=
  Erdos319Submission.literal_maximum N

theorem sharp_asymptotic :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) - Erdos319Formal.maxSize N) * Real.log (Real.log N) /
        ((N : ℝ) * Real.log (Real.log (Real.log N))))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) :=
  Erdos319Sharp.erdos319_sharp_deficit

theorem sharp_asymptotic_ratio :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) - Erdos319Formal.maxSize N) /
        (Real.exp (-Real.eulerMascheroniConstant) * (N : ℝ) *
          Real.log (Real.log (Real.log N)) / Real.log (Real.log N)))
      atTop (𝓝 1) :=
  Erdos319Sharp.erdos319_sharp_deficit_ratio

theorem sharp_for_every_literal_maximum (c : ℕ → ℕ)
    (hc : ∀ N, IsOriginalMaximum N (c N)) :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) - c N) * Real.log (Real.log N) /
        ((N : ℝ) * Real.log (Real.log (Real.log N))))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have heq : c = Erdos319Formal.maxSize := by
    funext N
    exact (hc N).unique (maximum_correspondence N)
  rw [heq]
  exact sharp_asymptotic

theorem full_solution :
    (∀ N, IsOriginalMaximum N (Erdos319Formal.maxSize N)) ∧
    Tendsto (fun N : ℕ =>
      ((N : ℝ) - Erdos319Formal.maxSize N) * Real.log (Real.log N) /
        ((N : ℝ) * Real.log (Real.log (Real.log N))))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) :=
  ⟨maximum_correspondence, sharp_asymptotic⟩

end Erdos319Jsp
