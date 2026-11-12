import Erdos319Sharp.ExactTarget

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def RegularSet (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
    (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
    (∀ q ∈ divisorPrimePowers N A, 1 / (Real.log (Real.log N)) ^ 2 ≤
      (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ))

/-- Regularization loses an arbitrarily small fraction uniformly over all
sets in a fixed positive-fraction tail of the ambient interval. -/
theorem eventually_regular_subset (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      ∃ F ⊆ A, RegularSet N F ∧ ((A \ F).card : ℝ) ≤ ε * N := by
  classical
  let Eligible := fun N : ℕ => fun A : Finset ℕ =>
    A ⊆ Finset.Icc 1 N ∧ ∀ n ∈ A, c * N ≤ (n : ℝ)
  let Good := fun N : ℕ => fun A : Finset ℕ =>
    ∃ F ⊆ A, RegularSet N F ∧ ((A \ F).card : ℝ) ≤ ε * N
  let A : ℕ → Finset ℕ := fun N =>
    if h : ∃ B : Finset ℕ, Eligible N B ∧ ¬ Good N B then Classical.choose h else ∅
  have hChosen : ∀ N, (∃ B : Finset ℕ, Eligible N B ∧ ¬ Good N B) →
      Eligible N (A N) ∧ ¬ Good N (A N) := by
    intro N h
    dsimp [A]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hEligible : ∀ N, Eligible N (A N) := by
    intro N
    by_cases h : ∃ B : Finset ℕ, Eligible N B ∧ ¬ Good N B
    · exact (hChosen N h).1
    · have hEmpty : A N = ∅ := by simp [A, h]
      rw [hEmpty]
      exact ⟨Finset.empty_subset _, by simp⟩
  have hA : ∀ N, A N ⊆ Finset.Icc 1 N := fun N => (hEligible N).1
  have hMin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ A N, c * N ≤ (n : ℝ) :=
    Filter.Eventually.of_forall (fun N => (hEligible N).2)
  obtain ⟨F, hFA, hSmooth, hMult, hRich, hLoss⟩ :=
    exists_regular_cleaning_sequence A hA c hc hMin 6 (by norm_num)
  have hRegular : ∀ N, RegularSet N (F N) := by
    intro N
    refine ⟨(hFA N).trans (hA N), hSmooth N, hMult N, ?_⟩
    intro q hq
    have hMembership := Finset.mem_filter.mp hq
    have hPrimePower := (Finset.mem_filter.mp hMembership.1).2
    simpa only [one_div, reciprocalSum_eq_baseline] using
      hRich N q hPrimePower hMembership.2
  have hSmall := hLoss.eventually (Iio_mem_nhds hε)
  filter_upwards [hSmall] with N hSmallN B hB hBmin
  change Good N B
  by_contra hBadB
  have hBadExists : ∃ B : Finset ℕ, Eligible N B ∧ ¬ Good N B :=
    ⟨B, ⟨hB, hBmin⟩, hBadB⟩
  apply (hChosen N hBadExists).2
  refine ⟨F N, hFA N, hRegular N, ?_⟩
  have hSplitQ : reciprocalSum (A N \ F N) + reciprocalSum (F N) = reciprocalSum (A N) :=
    Finset.sum_sdiff (hFA N)
  have hSplit : (reciprocalSum (A N \ F N) : ℝ) + (reciprocalSum (F N) : ℝ) =
      (reciprocalSum (A N) : ℝ) := by exact_mod_cast hSplitQ
  have hCard := card_le_N_mul_reciprocalSum
    ((Finset.sdiff_subset : A N \ F N ⊆ A N).trans (hA N))
  rw [← reciprocalSum_eq_baseline] at hCard
  have hSmallOwn : (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ) < ε := by
    simpa only [reciprocalSum_eq_baseline] using hSmallN
  have hRecip : (reciprocalSum (A N \ F N) : ℝ) ≤ ε := by
    linarith only [hSplit, hSmallOwn]
  calc
    ((A N \ F N).card : ℝ) ≤ N * (reciprocalSum (A N \ F N) : ℝ) := hCard
    _ ≤ (N : ℝ) * ε := mul_le_mul_of_nonneg_left hRecip (Nat.cast_nonneg N)
    _ = ε * N := by ring

theorem eventually_dense_regular_subset (c β : ℝ) (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      β * N ≤ (A.card : ℝ) →
      ∃ F ⊆ A, RegularSet N F ∧ (β / 2) * N ≤ (F.card : ℝ) := by
  filter_upwards [eventually_regular_subset c (β / 2) hc (by linarith)] with N hClean
  intro A hA hMin hCard
  obtain ⟨F, hFA, hRegular, hLoss⟩ := hClean A hA hMin
  refine ⟨F, hFA, hRegular, ?_⟩
  have hCount : ((A \ F).card : ℝ) + F.card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hFA
  linarith

end Erdos319Sharp
