import Erdos319Sharp.ProgressionAvoidance

set_option autoImplicit false

open Finset

namespace Erdos319Sharp

theorem exists_subset_sum_window {α : Type*} (P : Finset α) (f : α → ℝ) (target step : ℝ)
    (hTarget : 0 < target) (hSum : target ≤ ∑ x ∈ P, f x)
    (hStep : ∀ x ∈ P, f x ≤ step) :
    ∃ Q ⊆ P, target ≤ (∑ x ∈ Q, f x) ∧ (∑ x ∈ Q, f x) < target + step := by
  classical
  revert hSum hStep
  induction P using Finset.induction_on with
  | empty =>
      intro hSum hStep
      simp only [Finset.sum_empty] at hSum
      linarith
  | @insert x P hx ih =>
      intro hSum hStep
      by_cases hEnough : target ≤ ∑ y ∈ P, f y
      · obtain ⟨Q, hQP, hLower, hUpper⟩ := ih hEnough (fun y hy => hStep y (Finset.mem_insert_of_mem hy))
        exact ⟨Q, hQP.trans (Finset.subset_insert _ _), hLower, hUpper⟩
      · refine ⟨insert x P, Finset.Subset.rfl, hSum, ?_⟩
        rw [Finset.sum_insert hx]
        have hWeight := hStep x (Finset.mem_insert_self _ _)
        linarith

theorem exists_subset_sum_window_card_two {α : Type*} (P : Finset α) (f : α → ℝ) (target step : ℝ)
    (hTarget : 0 < target) (hStrict : step < target) (hSum : target ≤ ∑ x ∈ P, f x)
    (hStep : ∀ x ∈ P, f x ≤ step) :
    ∃ Q ⊆ P, 2 ≤ Q.card ∧ target ≤ (∑ x ∈ Q, f x) ∧ (∑ x ∈ Q, f x) < target + step := by
  classical
  obtain ⟨Q, hQP, hLower, hUpper⟩ := exists_subset_sum_window P f target step hTarget hSum hStep
  refine ⟨Q, hQP, ?_, hLower, hUpper⟩
  by_contra hCard
  have hSmall : Q.card = 0 ∨ Q.card = 1 := by omega
  rcases hSmall with hEmpty | hSingle
  · have hQEmpty := Finset.card_eq_zero.mp hEmpty
    simp only [hQEmpty, Finset.sum_empty] at hLower
    linarith
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hSingle
    have hWeight := hStep x (hQP (Finset.mem_singleton_self _))
    simp only [Finset.sum_singleton] at hLower
    linarith

end Erdos319Sharp
