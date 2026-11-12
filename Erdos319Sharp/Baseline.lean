import Erdos319
import Erdos319Sharp.Target

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos319Sharp

theorem reciprocalSum_eq_baseline (A : Finset ℕ) :
    reciprocalSum A = Erdos319Formal.reciprocalSum A := rfl

theorem primitive_iff_baseline (A : Finset ℕ) :
    Primitive A ↔ Erdos319Formal.Primitive A := Iff.rfl

theorem maxSize_eq_baseline (N : ℕ) : maxSize N = Erdos319Formal.maxSize N := rfl

/-- This imports the existing density-one result from the pinned upstream proof. -/
theorem densityOne_existing :
    Tendsto (fun N : ℕ => (maxSize N : ℝ) / N) atTop (𝓝 1) := by
  simpa only [maxSize_eq_baseline] using Erdos319Formal.erdos_problem_319_limit

theorem primitive_union_of_minimalCore {D : ℕ} {E F : Finset ℕ}
    (hcore : Erdos319Formal.MinimalCore D E)
    (hFpos : ∀ n ∈ F, 0 < n)
    (hFcop : ∀ n ∈ F, n.Coprime D)
    (heq : reciprocalSum E = reciprocalSum F) : Primitive (E ∪ F) := by
  exact (primitive_iff_baseline _).mpr
    (Erdos319Formal.primitive_union_of_minimalCore hcore hFpos hFcop heq)

end Erdos319Sharp
