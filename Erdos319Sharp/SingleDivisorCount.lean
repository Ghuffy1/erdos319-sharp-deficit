import Erdos319Sharp.DivisorMoments

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def singleDivisorSet (a : ℝ) (N : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  (tailInterval a N).filter (fun n => (Q.filter (fun q => q ∣ n)).card = 1)

theorem divisorIncidence_eq_card (Q : Finset ℕ) (n : ℕ) :
    divisorIncidence Q n = ((Q.filter (fun q => q ∣ n)).card : ℝ) := by
  classical
  calc
    divisorIncidence Q n = ∑ q ∈ Q.filter (fun q => q ∣ n), (1 : ℝ) := by
      rw [Finset.sum_filter]
      rfl
    _ = _ := by simp

theorem single_divisor_indicator_lower (Q : Finset ℕ) (n : ℕ) :
    2 * divisorIncidence Q n - (divisorIncidence Q n) ^ 2 ≤
      if (Q.filter (fun q => q ∣ n)).card = 1 then (1 : ℝ) else 0 := by
  rw [divisorIncidence_eq_card]
  by_cases hOne : (Q.filter (fun q => q ∣ n)).card = 1
  · norm_num [hOne]
  · rw [ite_eq_right hOne]
    by_cases hZero : (Q.filter (fun q => q ∣ n)).card = 0
    · simp [hZero]
    · have hTwo : (2 : ℝ) ≤ (Q.filter (fun q => q ∣ n)).card := by
        exact_mod_cast (show 2 ≤ (Q.filter (fun q => q ∣ n)).card by omega)
      have hProduct := mul_nonneg
        (Nat.cast_nonneg (α := ℝ) (Q.filter (fun q => q ∣ n)).card)
        (show 0 ≤ ((Q.filter (fun q => q ∣ n)).card : ℝ) - 2 by linarith)
      nlinarith only [hProduct]

theorem mem_singleDivisorSet (a : ℝ) (N n : ℕ) (Q : Finset ℕ) :
    n ∈ singleDivisorSet a N Q ↔ n ∈ tailInterval a N ∧
      ∃ q ∈ Q, q ∣ n ∧ ∀ r ∈ Q, r ∣ n → r = q := by
  classical
  simp only [singleDivisorSet, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hCard⟩
    obtain ⟨q, hEqual⟩ := Finset.card_eq_one.mp hCard
    have hq : q ∈ Q.filter (fun r => r ∣ n) := by rw [hEqual]; simp
    refine ⟨hn, q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2, ?_⟩
    intro r hr hrn
    have hMem : r ∈ Q.filter (fun r => r ∣ n) := Finset.mem_filter.mpr ⟨hr, hrn⟩
    rw [hEqual] at hMem
    exact Finset.mem_singleton.mp hMem
  · rintro ⟨hn, q, hq, hqn, hUnique⟩
    have hEqual : Q.filter (fun r => r ∣ n) = {q} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hrn⟩
        exact hUnique r hr hrn
      · rintro rfl
        exact ⟨hq, hqn⟩
    exact ⟨hn, by rw [hEqual]; simp⟩

theorem single_divisor_count_lower (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (Q : Finset ℕ)
    (hPos : ∀ q ∈ Q, 0 < q)
    (hCop : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r) :
    (1 - 2 * a) * (N : ℝ) * (reciprocalSum Q : ℝ) -
      (N : ℝ) * (reciprocalSum Q : ℝ) ^ 2 - 4 * Q.card ≤
        ((singleDivisorSet a N Q).card : ℝ) := by
  classical
  have hFirstTerms : ∀ q ∈ Q, ((1 - a) / q) * N - 2 ≤
      (((tailInterval a N).filter (fun n => q ∣ n)).card : ℝ) := by
    intro q hq
    have h := coprimeWindow_divisor_card_lower 1 q (by norm_num) (hPos q hq) (by simp) a ha N
    simpa only [Nat.cast_one, mul_one, tailInterval] using h
  have hMass : (∑ q ∈ Q, (1 : ℝ) / q) = (reciprocalSum Q : ℝ) := by
    rw [reciprocalSum_eq_baseline, reciprocalSum_real]
  have hFirst : (1 - a) * (N : ℝ) * (reciprocalSum Q : ℝ) - 2 * Q.card ≤
      ∑ n ∈ tailInterval a N, divisorIncidence Q n := by
    rw [sum_divisorIncidence]
    calc
      _ = ∑ q ∈ Q, (((1 - a) / q) * N - 2) := by
        rw [← hMass, Finset.mul_sum, Finset.sum_sub_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro q hq
          ring
        · simp only [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hFirstTerms
  have hSecond : (∑ n ∈ tailInterval a N, (divisorIncidence Q n) ^ 2) ≤
      (N : ℝ) * ((reciprocalSum Q : ℝ) + (reciprocalSum Q : ℝ) ^ 2) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (tailInterval_subset a N)
      (fun n _ _ => sq_nonneg (divisorIncidence Q n))).trans
        (pairwise_coprime_second_moment N Q hPos hCop)
  have hPoint := Finset.sum_le_sum (s := tailInterval a N)
    (fun n _ => single_divisor_indicator_lower Q n)
  have hIndicator : (∑ n ∈ tailInterval a N,
      if (Q.filter (fun q => q ∣ n)).card = 1 then (1 : ℝ) else 0) =
        ((singleDivisorSet a N Q).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [singleDivisorSet]
  rw [hIndicator, Finset.sum_sub_distrib, ← Finset.mul_sum] at hPoint
  nlinarith only [hFirst, hSecond, hPoint]

end Erdos319Sharp
