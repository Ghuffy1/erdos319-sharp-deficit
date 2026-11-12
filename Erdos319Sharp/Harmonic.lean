import Erdos319Sharp.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max
import Mathlib.NumberTheory.Harmonic.Defs

set_option autoImplicit false

namespace Erdos319Sharp

theorem reciprocalSum_Icc (N : ℕ) : reciprocalSum (Finset.Icc 1 N) = harmonic N := by
  induction N with
  | zero => simp [reciprocalSum]
  | succ N ih =>
      change (∑ n ∈ Finset.Icc 1 (N + 1), (n : ℚ)⁻¹) = harmonic (N + 1)
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le N)), harmonic_succ]
      exact congrArg (fun x : ℚ => x + ((N + 1 : ℕ) : ℚ)⁻¹) ih

/-- Among equally sized positive-integer sets, an initial interval has the largest mass. -/
theorem reciprocalSum_le_harmonic_card (A : Finset ℕ)
    (hpos : ∀ n ∈ A, 0 < n) : reciprocalSum A ≤ harmonic A.card := by
  classical
  revert hpos
  refine Finset.strongInductionOn A ?_
  intro A ih hpos
  by_cases hempty : A = ∅
  · simp [hempty, reciprocalSum]
  have hne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let a := A.max' hne
  have ha : a ∈ A := Finset.max'_mem A hne
  have hbound : A.card ≤ a := by
    have hsub : A ⊆ Finset.Icc 1 a := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨hpos n hn, Finset.le_max' A n hn⟩
    simpa using Finset.card_le_card hsub
  have hcardpos : 0 < A.card := Finset.card_pos.mpr hne
  have htail := ih (A.erase a) (Finset.erase_ssubset ha)
    (fun n hn => hpos n (Finset.mem_of_mem_erase hn))
  have hinv : (a : ℚ)⁻¹ ≤ (A.card : ℚ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast hcardpos) (by exact_mod_cast hbound)
  have hsum : reciprocalSum (A.erase a) + (a : ℚ)⁻¹ = reciprocalSum A :=
    Finset.sum_erase_add A (fun n => (n : ℚ)⁻¹) ha
  have hcard : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one ha
  calc
    reciprocalSum A = reciprocalSum (A.erase a) + (a : ℚ)⁻¹ := hsum.symm
    _ ≤ harmonic (A.erase a).card + (A.card : ℚ)⁻¹ := add_le_add htail hinv
    _ = harmonic A.card := by rw [← hcard, harmonic_succ]

/-- A dense arbitrary subset has at least the mass of the final interval of the same size. -/
theorem harmonic_omission_lower_bound {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    harmonic N - harmonic (N - A.card) ≤ reciprocalSum A := by
  let B := Finset.Icc 1 N \ A
  have hpos : ∀ n ∈ B, 0 < n := by
    intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1
  have hmass := reciprocalSum_le_harmonic_card B hpos
  have hcard : B.card = N - A.card := by
    dsimp [B]
    rw [Finset.card_sdiff_of_subset hA]
    simp
  rw [hcard] at hmass
  have hsum := Finset.sum_sdiff hA (f := fun n : ℕ => (n : ℚ)⁻¹)
  change reciprocalSum B + reciprocalSum A = reciprocalSum (Finset.Icc 1 N) at hsum
  rw [reciprocalSum_Icc] at hsum
  linarith

end Erdos319Sharp
