import Erdos319Sharp.PathIntegral
import Erdos319Sharp.PathLocalSum
import Erdos319Sharp.DivisorBlockResidue

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem pathIncoming_at_vertex (k : ℕ) (p u : ℕ → ℕ)
    (a : (i : ℕ) → (ZMod (p i))ˣ)
    (hIncoming : ∀ j < k - 1, (((p j * u j : ℕ) : ZMod (p (j + 1)))⁻¹) =
      (a (j + 1) : ZMod (p (j + 1))))
    {i : ℕ} (hPositive : 0 < i) (hi : i < k) :
    (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) = (a i : ZMod (p i)) := by
  cases i with
  | zero => omega
  | succ j => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hIncoming j (by omega)

theorem path_integral_subset_dichotomy (k D : ℕ) (p u : ℕ → ℕ)
    (a b : (i : ℕ) → (ZMod (p i))ˣ) (hk : 2 ≤ k) (hD : 0 < D)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬p i ∣ D)
    (hUPositive : ∀ i < k - 1, 0 < u i)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬p j ∣ u i)
    (hBound : ∀ i < k, (∑ n ∈ D.divisors, D / n) + 1 < p i)
    (hFirst : (b 0 : ZMod (p 0)) = -(∑ n ∈ D.divisors, (n : ZMod (p 0))⁻¹))
    (hLast : ∀ i < k, i + 1 = k → (a i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹))
    (hRules : ∀ i, 0 < i → i + 1 < k → ∀ B ⊆ D.divisors, ∀ incoming outgoing : Bool,
      (∑ n ∈ B, (n : ZMod (p i))⁻¹) + (if incoming then (a i : ZMod (p i)) else 0) +
        (if outgoing then (b i : ZMod (p i)) else 0) = 0 →
      incoming = outgoing ∧ B = if incoming then D.divisors else ∅)
    (hOutgoing : ∀ i < k - 1, (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) = (b i : ZMod (p i)))
    (hIncoming : ∀ i < k - 1, (((p i * u i : ℕ) : ZMod (p (i + 1)))⁻¹) = (a (i + 1) : ZMod (p (i + 1))))
    (C : Finset ℕ) (hC : C ⊆ pathSupport k D p u)
    (hIntegral : DIntegral ((Finset.range k).prod p) (reciprocalSum C)) :
    C = ∅ ∨ C = pathSupport k D p u := by
  classical
  let edge := fun i : ℕ => decide (pathEdge p u i ∈ C)
  have hCoprime : ∀ i < k, D.Coprime (p i) := fun i hi =>
    ((hPrime i hi).coprime_iff_not_dvd.mpr (hAvoidD i hi)).symm
  have hZeros := (path_integral_iff k D p u C hD hPrime hInjective hAvoidD hUPositive hAvoidU hC).mp hIntegral
  have hEndpoint : ∀ i < k, ∀ B ⊆ D.divisors, ∀ flag : Bool,
      (∑ n ∈ B, (n : ZMod (p i))⁻¹) +
        (if flag then -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹) else 0) = 0 →
      B = if flag then D.divisors else ∅ := by
    intro i hi B hB flag hSum
    have hSmall : (∑ n ∈ D.divisors, D / n) < p i := by have := hBound i hi; omega
    cases flag with
    | false =>
        change B = ∅
        change (∑ n ∈ B, (n : ZMod (p i))⁻¹) + 0 = 0 at hSum
        have hValue : (∑ n ∈ B, (n : ZMod (p i))⁻¹) = 0 := by simpa using hSum
        exact (divisor_inverse_sum_zero_iff (p i) D B (hPrime i hi).pos hD (hCoprime i hi) hB hSmall).mp hValue
    | true =>
        change B = D.divisors
        change (∑ n ∈ B, (n : ZMod (p i))⁻¹) + -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹) = 0 at hSum
        have hValue : (∑ n ∈ B, (n : ZMod (p i))⁻¹) = (∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹) := by
          apply eq_of_sub_eq_zero
          simpa only [sub_eq_add_neg] using hSum
        exact (divisor_inverse_sum_full_iff (p i) D B (hPrime i hi).pos hD (hCoprime i hi) hB hSmall).mp hValue
  have hInternal : ∀ i, 0 < i → i + 1 < k →
      edge (i - 1) = edge i ∧
        pathBlockSelection D p i C = if edge (i - 1) then D.divisors else ∅ := by
    intro i hPositive hInterior
    have hi : i < k := by omega
    have hPrev : i - 1 < k - 1 := by omega
    have hOut : (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) = (b i : ZMod (p i)) :=
      hOutgoing i (by omega)
    have hIn : (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) = (a i : ZMod (p i)) := by
      exact pathIncoming_at_vertex k p u a hIncoming hPositive hi
    have hRow := hZeros i hi
    rw [pathSubset_local_sum k D p u C hPrime hInjective hAvoidD hAvoidU hC hi] at hRow
    apply hRules i hPositive hInterior (pathBlockSelection D p i C) (Finset.filter_subset _ _)
      (edge (i - 1)) (edge i)
    simpa only [hPositive, hInterior, true_and, hIn, hOut, edge, decide_eq_true_eq] using hRow
  have hStep : ∀ j, j + 1 < k - 1 → edge j = edge (j + 1) := by
    intro j hj
    have h := (hInternal (j + 1) (by omega) (by omega)).1
    simpa only [Nat.add_sub_cancel] using h
  have hConstant := path_edges_constant edge (k - 1) hStep
  have hFirstBlock : pathBlockSelection D p 0 C = if edge 0 then D.divisors else ∅ := by
    have h0 : 0 < k := by omega
    have hOne : 0 + 1 < k := by omega
    have hOut := hOutgoing 0 (by omega)
    have hNotPositive : ¬(0 : ℕ) < 0 := by omega
    have hRow := hZeros 0 h0
    rw [pathSubset_local_sum k D p u C hPrime hInjective hAvoidD hAvoidU hC h0] at hRow
    apply hEndpoint 0 h0 (pathBlockSelection D p 0 C) (Finset.filter_subset _ _) (edge 0)
    simpa only [edge, decide_eq_true_eq, hNotPositive, false_and, ite_false,
      add_zero, hOne, true_and, hOut, hFirst] using hRow
  have hBlocks : ∀ i < k, pathBlockSelection D p i C = if edge 0 then D.divisors else ∅ := by
    intro i hi
    by_cases hZero : i = 0
    · subst i
      exact hFirstBlock
    · have hPositive : 0 < i := by omega
      have hPrev : i - 1 < k - 1 := by omega
      by_cases hEnd : i + 1 = k
      · have hNoOut : ¬i + 1 < k := by omega
        have hIn : (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) = (a i : ZMod (p i)) := by
          exact pathIncoming_at_vertex k p u a hIncoming hPositive hi
        have hRow := hZeros i hi
        rw [pathSubset_local_sum k D p u C hPrime hInjective hAvoidD hAvoidU hC hi] at hRow
        have hChoice : pathBlockSelection D p i C = if edge (i - 1) then D.divisors else ∅ := by
          apply hEndpoint i hi (pathBlockSelection D p i C) (Finset.filter_subset _ _) (edge (i - 1))
          simpa only [edge, decide_eq_true_eq, hPositive, hNoOut, true_and, false_and,
            ite_false, add_zero, hIn, hLast i hi hEnd] using hRow
        simpa only [hConstant (i - 1) hPrev] using hChoice
      · have hInterior : i + 1 < k := by omega
        simpa only [hConstant (i - 1) hPrev] using (hInternal i hPositive hInterior).2
  cases hBit : edge 0 with
  | false =>
      left
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hn⟩
      rcases Finset.mem_union.mp (hC hn) with hBlock | hEdge
      · obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hBlock
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hni
        have hEmpty : pathBlockSelection D p i C = ∅ := by
          simpa only [hBit, Bool.false_eq_true, if_false] using hBlocks i (Finset.mem_range.mp hi)
        have hSelected : b ∈ pathBlockSelection D p i C := Finset.mem_filter.mpr ⟨hb, hn⟩
        rw [hEmpty] at hSelected
        exact Finset.notMem_empty b hSelected
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hEdge
        have hFalse : edge j = false := (hConstant j (Finset.mem_range.mp hj)).trans hBit
        have hAbsent : pathEdge p u j ∉ C := by simpa only [edge, decide_eq_false_iff_not] using hFalse
        exact hAbsent hn
  | true =>
      right
      apply Finset.Subset.antisymm hC
      intro n hn
      rcases Finset.mem_union.mp hn with hBlock | hEdge
      · obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hBlock
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hni
        have hFull : pathBlockSelection D p i C = D.divisors := by
          simpa [hBit] using hBlocks i (Finset.mem_range.mp hi)
        have hSelected : b ∈ pathBlockSelection D p i C := by rw [hFull]; exact hb
        exact (Finset.mem_filter.mp hSelected).2
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hEdge
        have hTrue : edge j = true := (hConstant j (Finset.mem_range.mp hj)).trans hBit
        simpa only [edge, decide_eq_true_eq] using hTrue

end Erdos319Sharp
