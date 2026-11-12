import Erdos319Sharp.PathSupport
import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem pathSupport_positive_and_not_coprime (k D : ℕ) (p u : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime) (hU : ∀ i < k - 1, 0 < u i) :
    ∀ n ∈ pathSupport k D p u, 0 < n ∧ ¬n.Coprime ((Finset.range k).prod p) := by
  intro n hn
  rcases Finset.mem_union.mp hn with hBlock | hEdge
  · obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hBlock
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hni
    have hp := hPrime i (Finset.mem_range.mp hi)
    exact ⟨Nat.mul_pos hp.pos (Nat.pos_of_mem_divisors hb),
      not_coprime_of_common_prime hp (dvd_mul_right _ _) (Finset.dvd_prod_of_mem p hi)⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hEdge
    have hiEdge := Finset.mem_range.mp hi
    have hiVertex : i < k := by omega
    have hiNext : i + 1 < k := by omega
    have hp := hPrime i hiVertex
    refine ⟨Nat.mul_pos (Nat.mul_pos hp.pos (hPrime (i + 1) hiNext).pos) (hU i hiEdge), ?_⟩
    exact not_coprime_of_common_prime hp
      ((dvd_mul_right (p i) (p (i + 1))).trans (dvd_mul_right _ _))
      (Finset.dvd_prod_of_mem p (Finset.mem_range.mpr hiVertex))

theorem pathSupport_denominator_bound (k D M : ℕ) (p u : ℕ → ℕ) (hD : 0 < D)
    (hPrimeBound : ∀ i < k, p i ≤ M)
    (hU : ∀ i < k - 1, u i ≤ 4 * k * p i * p (i + 1)) :
    ∀ n ∈ pathSupport k D p u, n ≤ max (M * D) (4 * k * M ^ 4) := by
  intro n hn
  rcases Finset.mem_union.mp hn with hBlock | hEdge
  · obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hBlock
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hni
    exact (Nat.mul_le_mul (hPrimeBound i (Finset.mem_range.mp hi))
      (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hb))).trans (le_max_left _ _)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hEdge
    have hiEdge := Finset.mem_range.mp hi
    have hiVertex : i < k := by omega
    have hiNext : i + 1 < k := by omega
    have hPair : p i * p (i + 1) ≤ M * M :=
      Nat.mul_le_mul (hPrimeBound i hiVertex) (hPrimeBound (i + 1) hiNext)
    have hBound : pathEdge p u i ≤ 4 * k * M ^ 4 := by
      calc
        pathEdge p u i ≤ (p i * p (i + 1)) * (4 * k * p i * p (i + 1)) :=
          Nat.mul_le_mul_left _ (hU i hiEdge)
        _ = 4 * k * (p i * p (i + 1)) ^ 2 := by ring
        _ ≤ 4 * k * (M * M) ^ 2 :=
          Nat.mul_le_mul_left _ (pow_le_pow_left₀ (Nat.zero_le _) hPair 2)
        _ = 4 * k * M ^ 4 := by ring
    exact hBound.trans (le_max_right _ _)

end Erdos319Sharp
