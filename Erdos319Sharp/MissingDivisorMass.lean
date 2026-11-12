import Erdos319Sharp.DivisorMoments

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem missing_divisor_first_moment (a : ℝ) (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4)
    (N : ℕ) (Q F : Finset ℕ) (hQ : ∀ q ∈ Q, 0 < q ∧ q ≤ N)
    (hMissing : ∀ q ∈ Q, ∀ n ∈ F, ¬ q ∣ n) :
    (N : ℝ) / 4 * (reciprocalSum Q : ℝ) ≤
      ∑ n ∈ tailInterval a N \ F, divisorIncidence Q n := by
  rw [sum_divisorIncidence, reciprocalSum_eq_baseline, Erdos319Formal.reciprocalSum_real]
  apply (tail_divisibility_first_moment_lower a ha haQuarter N Q hQ).trans
  apply Finset.sum_le_sum
  intro q hq
  have hSub : (tailInterval a N).filter (fun n => q ∣ n) ⊆
      (tailInterval a N \ F).filter (fun n => q ∣ n) := by
    intro n hn
    obtain ⟨hnT, hqn⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hnT, fun hnF => hMissing q hq n hnF hqn⟩, hqn⟩
  exact_mod_cast Finset.card_le_card hSub

theorem missing_divisor_mass_bound (a : ℝ) (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4)
    (N : ℕ) (hN : 0 < N) (Q F : Finset ℕ)
    (hQ : ∀ q ∈ Q, 0 < q ∧ q ≤ N)
    (hCop : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r)
    (hMissing : ∀ q ∈ Q, ∀ n ∈ F, ¬ q ∣ n) :
    (N : ℝ) * (reciprocalSum Q : ℝ) ≤
      16 * (tailInterval a N \ F).card * (1 + (reciprocalSum Q : ℝ)) := by
  let E := tailInterval a N \ F
  let ρ : ℝ := reciprocalSum Q
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    rw [reciprocalSum_eq_baseline]
    exact_mod_cast Erdos319Formal.reciprocalSum_nonneg Q
  have hFirst : (N : ℝ) / 4 * ρ ≤ ∑ n ∈ E, divisorIncidence Q n :=
    missing_divisor_first_moment a ha haQuarter N Q F hQ hMissing
  have hSub : E ⊆ Finset.Icc 1 N := Finset.sdiff_subset.trans (tailInterval_subset a N)
  have hSecond : (∑ n ∈ E, (divisorIncidence Q n) ^ 2) ≤ (N : ℝ) * (ρ + ρ ^ 2) := by
    calc
      (∑ n ∈ E, (divisorIncidence Q n) ^ 2) ≤
          ∑ n ∈ Finset.Icc 1 N, (divisorIncidence Q n) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub (fun n hn hnot => sq_nonneg _)
      _ ≤ (N : ℝ) * (ρ + ρ ^ 2) :=
        pairwise_coprime_second_moment N Q (fun q hq => (hQ q hq).1) hCop
  have hCauchy := sq_sum_le_card_mul_sum_sq (s := E) (f := divisorIncidence Q)
  have hSquareUpper : (∑ n ∈ E, divisorIncidence Q n) ^ 2 ≤
      (E.card : ℝ) * ((N : ℝ) * (ρ + ρ ^ 2)) :=
    hCauchy.trans (mul_le_mul_of_nonneg_left hSecond (Nat.cast_nonneg E.card))
  have hSquareLower : ((N : ℝ) / 4 * ρ) ^ 2 ≤ (∑ n ∈ E, divisorIncidence Q n) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) hρ) hFirst 2
  change (N : ℝ) * ρ ≤ 16 * E.card * (1 + ρ)
  by_cases hZero : ρ = 0
  · simp only [hZero, mul_zero, add_zero, mul_one]
    positivity
  · have hρPos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hZero)
    apply (mul_le_mul_iff_of_pos_left (mul_pos hNReal hρPos)).mp
    nlinarith only [hSquareLower, hSquareUpper]

theorem missing_divisor_mass_small (a δ : ℝ) (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4)
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 32) (N : ℕ) (hN : 0 < N) (Q F : Finset ℕ)
    (hQ : ∀ q ∈ Q, 0 < q ∧ q ≤ N)
    (hCop : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r)
    (hMissing : ∀ q ∈ Q, ∀ n ∈ F, ¬ q ∣ n)
    (hLoss : ((tailInterval a N \ F).card : ℝ) ≤ δ * N) :
    (reciprocalSum Q : ℝ) ≤ 32 * δ := by
  let ρ : ℝ := reciprocalSum Q
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    rw [reciprocalSum_eq_baseline]
    exact_mod_cast Erdos319Formal.reciprocalSum_nonneg Q
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hBase := missing_divisor_mass_bound a ha haQuarter N hN Q F hQ hCop hMissing
  change (N : ℝ) * ρ ≤ 16 * (tailInterval a N \ F).card * (1 + ρ) at hBase
  have hProduct := mul_le_mul_of_nonneg_right hLoss (show 0 ≤ 16 * (1 + ρ) by positivity)
  have hReduced : ρ ≤ 16 * δ * (1 + ρ) := by
    apply (mul_le_mul_iff_of_pos_left hNReal).mp
    nlinarith only [hBase, hProduct]
  have hδρ := mul_le_mul_of_nonneg_right hδSmall hρ
  change ρ ≤ 32 * δ
  nlinarith only [hReduced, hδρ]

end Erdos319Sharp
