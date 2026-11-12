import Erdos319Sharp.PathSelection
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def localInverseTerm (p n : ℕ) : ZMod p :=
  if p ∣ n then ((n / p : ℕ) : ZMod p)⁻¹ else 0

theorem sum_localInverseTerm (p : ℕ) (A : Finset ℕ) :
    (∑ n ∈ A, localInverseTerm p n) =
      ∑ n ∈ A.filter (fun n => p ∣ n), ((n / p : ℕ) : ZMod p)⁻¹ := by
  rw [Finset.sum_filter]
  rfl

theorem pathBlock_local_sum (k D : ℕ) (p : ℕ → ℕ) (C : Finset ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ i < k, ¬ p i ∣ D) {i : ℕ} (hi : i < k) :
    (∑ j ∈ Finset.range k, ∑ b ∈ pathBlockSelection D p j C,
      localInverseTerm (p i) (p j * b)) =
        ∑ b ∈ pathBlockSelection D p i C, (b : ZMod (p i))⁻¹ := by
  classical
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [localInverseTerm, if_pos (dvd_mul_right (p i) b),
      Nat.mul_div_cancel_left b (hPrime i hi).pos]
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro b hb
    have hbD : b ∈ D.divisors := (Finset.mem_filter.mp hb).1
    have hNot : ¬p i ∣ p j * b := by
      intro hDiv
      have hEq := (marked_prime_dvd_block k D p hPrime hInjective hAvoid
        (Finset.mem_range.mp hj) hi hbD).mp hDiv
      exact hji hEq.symm
    simp only [localInverseTerm, if_neg hNot]
  · intro hNot
    exact (hNot (Finset.mem_range.mpr hi)).elim

theorem pathEdges_local_sum (k : ℕ) (p u : ℕ → ℕ) (C : Finset ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ j < k - 1, ∀ i < k, ¬ p i ∣ u j) {i : ℕ} (hi : i < k) :
    (∑ j ∈ pathEdgeSelection k p u C, localInverseTerm (p i) (pathEdge p u j)) =
      (if 0 < i ∧ pathEdge p u (i - 1) ∈ C then
        (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) else 0) +
      (if i + 1 < k ∧ pathEdge p u i ∈ C then
        (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) else 0) := by
  classical
  let S := pathEdgeSelection k p u C
  let v := fun j : ℕ => (((pathEdge p u j / p i : ℕ) : ZMod (p i))⁻¹)
  have hSplit : (∑ j ∈ S, localInverseTerm (p i) (pathEdge p u j)) =
      (∑ j ∈ S, if i = j then v j else 0) + (∑ j ∈ S, if i = j + 1 then v j else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjEdge : j < k - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hCriterion := marked_prime_dvd_edge k p u hPrime hInjective hAvoid hjEdge hi
    by_cases hFirst : i = j
    · have hSecond : i ≠ j + 1 := by omega
      have hDiv := hCriterion.mpr (Or.inl hFirst)
      simp only [localInverseTerm, if_pos hDiv, if_pos hFirst, if_neg hSecond, add_zero, v]
    · by_cases hSecond : i = j + 1
      · have hDiv := hCriterion.mpr (Or.inr hSecond)
        simp only [localInverseTerm, if_pos hDiv, if_neg hFirst, if_pos hSecond, zero_add, v]
      · have hDiv : ¬p i ∣ pathEdge p u j := fun h => (hCriterion.mp h).elim hFirst hSecond
        simp only [localInverseTerm, if_neg hDiv, if_neg hFirst, if_neg hSecond, add_zero]
  have hOutgoing : (∑ j ∈ S, if i = j then v j else 0) =
      if i + 1 < k ∧ pathEdge p u i ∈ C then
        (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) else 0 := by
    rw [Finset.sum_ite_eq]
    have hMember : i ∈ S ↔ i + 1 < k ∧ pathEdge p u i ∈ C := by
      have hIndex : i < k - 1 ↔ i + 1 < k := by omega
      simp only [S, pathEdgeSelection, Finset.mem_filter, Finset.mem_range, hIndex]
    have hValue : v i = (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) := by
      dsimp [v, pathEdge]
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (hPrime i hi).pos]
    simp only [hMember, hValue]
  have hIncoming : (∑ j ∈ S, if i = j + 1 then v j else 0) =
      if 0 < i ∧ pathEdge p u (i - 1) ∈ C then
        (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) else 0 := by
    by_cases hZero : i = 0
    · subst i
      simp
    · have hPositive : 0 < i := by omega
      have hCompare : ∀ j : ℕ, i = j + 1 ↔ i - 1 = j := by omega
      simp_rw [hCompare]
      rw [Finset.sum_ite_eq]
      have hMember : i - 1 ∈ S ↔ pathEdge p u (i - 1) ∈ C := by
        have hRange : i - 1 < k - 1 := by omega
        simp only [S, pathEdgeSelection, Finset.mem_filter, Finset.mem_range, hRange, true_and]
      have hFactor : pathEdge p u (i - 1) = p i * (p (i - 1) * u (i - 1)) := by
        unfold pathEdge
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]
        ring
      have hValue : v (i - 1) = (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) := by
        dsimp [v]
        rw [hFactor, Nat.mul_div_cancel_left _ (hPrime i hi).pos]
      simp only [hMember, hValue, hPositive, true_and]
  rw [hSplit, hOutgoing, hIncoming, add_comm]

theorem pathSubset_local_sum (k D : ℕ) (p u : ℕ → ℕ) (C : Finset ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬ p i ∣ D)
    (hAvoidU : ∀ j < k - 1, ∀ i < k, ¬ p i ∣ u j)
    (hC : C ⊆ pathSupport k D p u) {i : ℕ} (hi : i < k) :
    (∑ n ∈ C.filter (fun n => p i ∣ n), ((n / p i : ℕ) : ZMod (p i))⁻¹) =
      (∑ b ∈ pathBlockSelection D p i C, (b : ZMod (p i))⁻¹) +
      (if 0 < i ∧ pathEdge p u (i - 1) ∈ C then
        (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) else 0) +
      (if i + 1 < k ∧ pathEdge p u i ∈ C then
        (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) else 0) := by
  rw [← sum_localInverseTerm]
  rw [path_subset_sum (localInverseTerm (p i)) k D p u C hPrime hInjective hAvoidD hAvoidU hC,
    pathBlock_local_sum k D p C hPrime hInjective hAvoidD hi,
    pathEdges_local_sum k p u C hPrime hInjective hAvoidU hi, add_assoc]

end Erdos319Sharp
