import Erdos319Sharp.PathMass

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem pathEdge_reciprocal_sum_le (k L : ℕ) (p u : ℕ → ℕ) (hL : 0 < L)
    (hPrime : ∀ i < k, (p i).Prime) (hLower : ∀ i < k, L ≤ p i)
    (hU : ∀ i < k - 1, 0 < u i) :
    (∑ i ∈ Finset.range (k - 1), (pathEdge p u i : ℚ)⁻¹) ≤
      (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) / L := by
  have hLQ : (0 : ℚ) < L := by exact_mod_cast hL
  have hTerm : ∀ i ∈ Finset.range (k - 1), (pathEdge p u i : ℚ)⁻¹ ≤ (p i : ℚ)⁻¹ / L := by
    intro i hi
    have hiEdge := Finset.mem_range.mp hi
    have hiVertex : i < k := by omega
    have hiNext : i + 1 < k := by omega
    have hpQ : (0 : ℚ) < p i := by exact_mod_cast (hPrime i hiVertex).pos
    have hProduct : p i * L ≤ pathEdge p u i := by
      calc
        p i * L ≤ p i * p (i + 1) := Nat.mul_le_mul_left _ (hLower (i + 1) hiNext)
        _ = p i * p (i + 1) * 1 := by simp
        _ ≤ pathEdge p u i := Nat.mul_le_mul_left _ (hU i hiEdge)
    have hProductQ : (p i : ℚ) * L ≤ pathEdge p u i := by exact_mod_cast hProduct
    calc
      (pathEdge p u i : ℚ)⁻¹ ≤ ((p i : ℚ) * L)⁻¹ := inv_anti₀ (mul_pos hpQ hLQ) hProductQ
      _ = (p i : ℚ)⁻¹ / L := by simp only [mul_inv_rev, div_eq_mul_inv]; ring
  have hPrefix : (∑ i ∈ Finset.range (k - 1), (p i : ℚ)⁻¹) ≤
      ∑ i ∈ Finset.range k, (p i : ℚ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => by positivity)
  calc
    _ ≤ ∑ i ∈ Finset.range (k - 1), (p i : ℚ)⁻¹ / L := Finset.sum_le_sum hTerm
    _ = (∑ i ∈ Finset.range (k - 1), (p i : ℚ)⁻¹) / L := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hPrefix hLQ.le

theorem pathSupport_mass_bounds (k D L : ℕ) (p u : ℕ → ℕ) (hL : 0 < L)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬p i ∣ D)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬p j ∣ u i)
    (hLower : ∀ i < k, L ≤ p i) (hU : ∀ i < k - 1, 0 < u i) :
    reciprocalSum D.divisors * (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) ≤
      reciprocalSum (pathSupport k D p u) ∧
    reciprocalSum (pathSupport k D p u) ≤
      reciprocalSum D.divisors * (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) +
        (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) / L := by
  rw [pathSupport_reciprocalSum k D p u hPrime hInjective hAvoidD hAvoidU]
  have hNonneg : (0 : ℚ) ≤ ∑ i ∈ Finset.range (k - 1), (pathEdge p u i : ℚ)⁻¹ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hUpper := pathEdge_reciprocal_sum_le k L p u hL hPrime hLower hU
  constructor <;> linarith

end Erdos319Sharp
