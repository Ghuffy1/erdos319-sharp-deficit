import Erdos319Sharp.ExcessGroups
import Erdos319Sharp.ExcessWeights
import Erdos319Sharp.InverseHarmonic
import Erdos319Sharp.Harmonic
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem inverse_free_mass_le_one_add_log (b : ℕ) (hb : 0 < b) (M : Finset ℕ)
    (hPos : ∀ m ∈ M, 0 < m) (hFree : InverseZeroSumFree b M) :
    (reciprocalSum M : ℝ) ≤ 1 + Real.log b := by
  classical
  by_cases hEmpty : M = ∅
  · have hLog : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
    simp only [hEmpty, reciprocalSum, Finset.sum_empty, Rat.cast_zero]
    linarith
  have hCard : 0 < M.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
  have hCardB := (hFree.card_lt hb hPos).le
  have hMass : (reciprocalSum M : ℝ) ≤ (harmonic M.card : ℝ) :=
    by exact_mod_cast reciprocalSum_le_harmonic_card M hPos
  have hLog : Real.log (M.card : ℝ) ≤ Real.log b :=
    Real.log_le_log (by exact_mod_cast hCard) (by exact_mod_cast hCardB)
  calc
    (reciprocalSum M : ℝ) ≤ (harmonic M.card : ℝ) := hMass
    _ ≤ 1 + Real.log M.card := harmonic_le_one_add_log M.card
    _ ≤ 1 + Real.log b := by linarith

theorem excessGroup_mass_eq_weight (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hb : 0 < b) (hPos : ∀ n ∈ A, 0 < n) :
    (reciprocalSum (excessGroup D b A) : ℝ) =
      (reciprocalSum (excessCofactors D b A) : ℝ) * excessWeight D b := by
  rw [excessGroup_reciprocalSum D b A hD hb hPos]
  push_cast
  rfl

theorem excessGroup_mass_crude (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0) (hb : 0 < b)
    (hPos : ∀ n ∈ A, 0 < n) (hFree : InverseZeroSumFree b (excessCofactors D b A)) :
    (reciprocalSum (excessGroup D b A) : ℝ) ≤ (1 + Real.log b) * excessWeight D b := by
  rw [excessGroup_mass_eq_weight D b A hD hb hPos]
  exact mul_le_mul_of_nonneg_right
    (inverse_free_mass_le_one_add_log b hb _ (excessCofactors_positive D b A hD hPos) hFree)
    (excessWeight_nonneg D b)

theorem eventually_excessGroup_mass_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ b₀ : ℕ, 3 ≤ b₀ ∧ ∀ (D N b : ℕ) (A : Finset ℕ),
      D ≠ 0 → b₀ ≤ b → b ≤ N → (∀ n ∈ A, 0 < n) →
      InverseZeroSumFree b (excessCofactors D b A) →
      (reciprocalSum (excessGroup D b A) : ℝ) ≤
        (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log N) * excessWeight D b := by
  obtain ⟨b₁, hBound⟩ := eventually_atTop.mp (eventually_inverse_zero_free_harmonic_bound ε hε)
  refine ⟨max b₁ 3, le_max_right _ _, ?_⟩
  intro D N b A hD hb hBN hPos hFree
  have hbOne : 1 < b := by have := (le_max_right b₁ 3).trans hb; omega
  have hbPos : 0 < b := by omega
  have hbLog : 0 < Real.log b := Real.log_pos (by exact_mod_cast hbOne)
  have hLogs : Real.log (Real.log b) ≤ Real.log (Real.log N) :=
    Real.log_le_log hbLog (Real.log_le_log (by exact_mod_cast hbPos)
      (by exact_mod_cast hBN))
  have hMass := hBound b ((le_max_left _ _).trans hb) (excessCofactors D b A)
    (excessCofactors_positive D b A hD hPos) (excessCofactors_coprime D b A hD hPos) hFree
  rw [excessGroup_mass_eq_weight D b A hD hbPos hPos]
  exact mul_le_mul_of_nonneg_right
    (hMass.trans (mul_le_mul_of_nonneg_left hLogs (by positivity))) (excessWeight_nonneg D b)

theorem one_add_log_mul_inv_le_rpow (b : ℕ) (hb : 0 < b) :
    (1 + Real.log b) * (b : ℝ)⁻¹ ≤ 3 * (b : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hbOne : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbPos : (0 : ℝ) < b := by exact_mod_cast hb
  have hRoot : 1 ≤ (b : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hbOne (by norm_num)
  have hLog := Real.log_le_rpow_div hbPos.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hBound : 1 + Real.log b ≤ 3 * (b : ℝ) ^ (1 / 2 : ℝ) := by
    norm_num at hLog
    nlinarith
  calc
    (1 + Real.log b) * (b : ℝ)⁻¹ ≤ 3 * (b : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hBound (inv_nonneg.mpr hbPos.le)
    _ = 3 * (b : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [mul_assoc, ← div_eq_mul_inv, ← Real.rpow_sub_one hbPos.ne']
      norm_num

theorem small_prime_excess_mass_bound (D : ℕ) (A B P : Finset ℕ) (hD : D ≠ 0)
    (hPos : ∀ n ∈ A, 0 < n) (hP : ∀ p ∈ P, p.Prime)
    (hB : ∀ b ∈ B, b ∈ Nat.factoredNumbers P)
    (hFree : ∀ b ∈ B, InverseZeroSumFree b (excessCofactors D b A)) :
    (∑ b ∈ B, (reciprocalSum (excessGroup D b A) : ℝ)) ≤ 3 * weightedPrimeProduct P (1 / 2) := by
  have hbPos : ∀ b ∈ B, 0 < b := fun b hb => Nat.pos_of_ne_zero (hB b hb).1
  calc
    (∑ b ∈ B, (reciprocalSum (excessGroup D b A) : ℝ)) ≤
        ∑ b ∈ B, (1 + Real.log b) * excessWeight D b :=
      Finset.sum_le_sum (fun b hb => excessGroup_mass_crude D b A hD (hbPos b hb) hPos (hFree b hb))
    _ ≤ ∑ b ∈ B, (1 + Real.log b) * (b : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_left (excessWeight_le_inv D b hD)
      have hLog : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hbPos b hb)
      linarith
    _ ≤ ∑ b ∈ B, 3 * (b : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun b hb => one_add_log_mul_inv_le_rpow b (hbPos b hb))
    _ = 3 * ∑ b ∈ B, (b : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 3 * weightedPrimeProduct P (1 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      convert weighted_factored_sum_le B P (1 / 2) hP (by norm_num) hB using 1 <;> norm_num

end Erdos319Sharp
