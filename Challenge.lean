import Solution

/-!
Literal reconstruction of the original question. The sign constraint is
required only on the given support, as in the printed problem. The bridge
extends this signing outside the support when using the library theorem.
-/

open Filter
open scoped Topology

namespace Erdos319Challenge

def Admissible (A : Finset ℕ) : Prop :=
  ∃ δ : ℕ → ℤ,
    (∀ n ∈ A, δ n = 1 ∨ δ n = -1) ∧
    (∑ n ∈ A, (δ n : ℚ) / n) = 0 ∧
    ∀ B : Finset ℕ, B ⊂ A → B.Nonempty →
      (∑ n ∈ B, (δ n : ℚ) / n) ≠ 0

theorem admissible_iff (A : Finset ℕ) :
    Admissible A ↔ Erdos319Submission.LiteralPrimitive A := by
  classical
  constructor
  · rintro ⟨δ, hsign, hsum, hproper⟩
    let ε : ℕ → ℤ := fun n => if n ∈ A then δ n else 1
    have hε : ∀ n, ε n = 1 ∨ ε n = -1 := by
      intro n
      by_cases hn : n ∈ A
      · simpa [ε, hn] using hsign n hn
      · simp [ε, hn]
    have sums (B : Finset ℕ) (hB : B ⊆ A) :
        (∑ n ∈ B, (ε n : ℚ) / n) = ∑ n ∈ B, (δ n : ℚ) / n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [ε, hB hn]
    refine ⟨ε, hε, ?_, ?_⟩
    · simpa only [sums A (Finset.Subset.refl A)] using hsum
    · intro B hBA hB
      rw [sums B (Finset.ssubset_iff_subset_ne.mp hBA).1]
      exact hproper B hBA hB
  · rintro ⟨δ, hsign, hsum, hproper⟩
    exact ⟨δ, fun n _ => hsign n, hsum, hproper⟩

theorem original_maximum (N : ℕ) :
    IsGreatest
      {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        Admissible A ∧ A.card = k}
      (Erdos319Formal.maxSize N) := by
  simpa only [admissible_iff] using Erdos319Submission.literal_maximum N

theorem original_sharp :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) - Erdos319Formal.maxSize N) * Real.log (Real.log N) /
        ((N : ℝ) * Real.log (Real.log (Real.log N))))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) :=
  Erdos319Jsp.sharp_asymptotic

end Erdos319Challenge
