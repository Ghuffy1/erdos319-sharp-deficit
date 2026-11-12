import Erdos319Sharp.QuantitativePath
import Erdos319Sharp.PathError

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem exists_bounded_path_core (k D L M : ℕ) (p : ℕ → ℕ) (hk : 2 ≤ k) (hD : 0 < D) (hL : 0 < L)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬p i ∣ D)
    (hBound : ∀ i < k, (∑ n ∈ D.divisors, D / n) + 1 < p i)
    (hLower : ∀ i < k, L ≤ p i) (hUpper : ∀ i < k, p i ≤ M)
    (hMass : (∑ i ∈ Finset.range k, (1 : ℝ) / p i) ≤ 1 / 2) :
    ∃ E : Finset ℕ, MinimalCore ((Finset.range k).prod p) E ∧
      E ⊆ Finset.Icc 1 (max (M * D) (4 * k * M ^ 4)) ∧
      reciprocalSum D.divisors * (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) ≤ reciprocalSum E ∧
      reciprocalSum E ≤ reciprocalSum D.divisors * (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) +
        (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) / L := by
  obtain ⟨u, hu, hCore⟩ := exists_quantitative_path_core k D p hk hD hPrime hInjective hAvoidD hBound hMass
  have hUPositive : ∀ i < k - 1, 0 < u i := fun i hi => (hu i hi).1
  have hUBound : ∀ i < k - 1, u i ≤ 4 * k * p i * p (i + 1) := fun i hi => (hu i hi).2.1.le
  have hAvoidU : ∀ i < k - 1, ∀ j < k, ¬p j ∣ u i := fun i hi => (hu i hi).2.2
  obtain ⟨hMassLower, hMassUpper⟩ := pathSupport_mass_bounds k D L p u hL hPrime hInjective hAvoidD hAvoidU hLower hUPositive
  refine ⟨pathSupport k D p u, hCore, ?_, hMassLower, hMassUpper⟩
  intro n hn
  exact Finset.mem_Icc.mpr ⟨(hCore.1 n hn).1,
    pathSupport_denominator_bound k D M p u hD hUpper hUBound n hn⟩

end Erdos319Sharp
