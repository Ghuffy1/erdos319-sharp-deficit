import Erdos319Sharp.PathSupport
import Erdos319Sharp.ResidueCorrection

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem pathBlocks_reciprocalSum (k D : ℕ) (p : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ i < k, ¬ p i ∣ D) :
    reciprocalSum (pathBlocks k D p) =
      reciprocalSum D.divisors * ∑ i ∈ Finset.range k, (p i : ℚ)⁻¹ := by
  have hUnion : reciprocalSum (pathBlocks k D p) =
      ∑ i ∈ Finset.range k, reciprocalSum (pathBlock D p i) :=
    Finset.sum_biUnion (pathBlocks_pairwise_disjoint k D p hPrime hInjective hAvoid)
  rw [hUnion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pathBlock, reciprocalSum_mul_image D.divisors (p i) (hPrime i (Finset.mem_range.mp hi)).pos,
    div_eq_mul_inv]

theorem pathEdges_reciprocalSum (k : ℕ) (p u : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ i < k - 1, ∀ j < k, ¬ p j ∣ u i) :
    reciprocalSum (pathEdges k p u) =
      ∑ i ∈ Finset.range (k - 1), (pathEdge p u i : ℚ)⁻¹ := by
  exact Finset.sum_image (pathEdge_injective k p u hPrime hInjective hAvoid)

theorem pathSupport_reciprocalSum (k D : ℕ) (p u : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬ p i ∣ D)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬ p j ∣ u i) :
    reciprocalSum (pathSupport k D p u) =
      reciprocalSum D.divisors * (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) +
        ∑ i ∈ Finset.range (k - 1), (pathEdge p u i : ℚ)⁻¹ := by
  have hUnion : reciprocalSum (pathSupport k D p u) =
      reciprocalSum (pathBlocks k D p) + reciprocalSum (pathEdges k p u) :=
    Finset.sum_union (pathBlocks_disjoint_pathEdges k D p u hPrime hInjective hAvoidD hAvoidU)
  rw [hUnion, pathBlocks_reciprocalSum k D p hPrime hInjective hAvoidD,
    pathEdges_reciprocalSum k p u hPrime hInjective hAvoidU]

end Erdos319Sharp
