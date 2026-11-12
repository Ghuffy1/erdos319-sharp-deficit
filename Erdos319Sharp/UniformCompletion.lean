import Erdos319Sharp.FiniteDescent
import Erdos319Sharp.TerminalReservoir

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem exists_uniform_rational_completion (η : ℝ) (hη : 0 < η) :
    ∃ C : ℕ, ∀ (r : ℚ) (G : ℕ), η ≤ (r : ℝ) → (r : ℝ) ≤ 2 → r.den.Coprime G →
      (∀ p : ℕ, p.Prime → p ∣ G →
        max C (⌊Real.log (primaryHeight r.den)⌋₊ ^ 13) < p) →
      ∃ A : Finset ℕ, reciprocalSum A = r ∧
        ∀ n ∈ A, 0 < n ∧ n.Coprime G ∧
          n ≤ max C (primaryHeight r.den * ⌊Real.log (primaryHeight r.den)⌋₊ ^ 13) := by
  classical
  obtain ⟨L, hL, hDescent⟩ := exists_small_denominator_remainder (η / 2) (by linarith)
  let D := (Finset.Icc 1 L).lcm id
  have hD : 0 < D := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (by
    intro n hn
    exact (show 0 < n from (Finset.mem_Icc.mp hn).1).ne'))
  obtain ⟨R, hR, hReservoir⟩ := exists_terminal_reservoir D 0 hD
  let C := R.sup id
  refine ⟨C, ?_⟩
  intro r G hrLower hrUpper hrCop hPrimes
  obtain ⟨T, hDen, hCost, hTerms, hAvoid⟩ := hDescent r
  have hRationalNonneg : (0 : ℚ) ≤ reciprocalSum T := Finset.sum_nonneg (fun n _ => by positivity)
  have hRealNonneg : (0 : ℝ) ≤ (reciprocalSum T : ℝ) := by exact_mod_cast hRationalNonneg
  have hResidualNonneg : (0 : ℚ) ≤ r - reciprocalSum T := by
    have h : (0 : ℝ) ≤ (r : ℝ) - (reciprocalSum T : ℝ) := by linarith
    exact_mod_cast h
  have hResidualUpper : r - reciprocalSum T ≤ (2 : ℚ) := by
    have h : (r : ℝ) - (reciprocalSum T : ℝ) ≤ 2 := by linarith
    exact_mod_cast h
  obtain ⟨U, hUR, hSum⟩ := hReservoir (r - reciprocalSum T) hResidualNonneg hResidualUpper hDen
  have hDisjoint : Disjoint T U := Finset.disjoint_left.mpr (by
    intro n hnT hnU
    exact (hTerms n hnT).2.1 (hR n (hUR hnU)).2.1)
  have hTCop : ∀ n ∈ T, n.Coprime G := (hAvoid G hrCop (by
    intro p hp hpG
    exact (le_max_right C _).trans_lt (hPrimes p hp hpG))).2
  have hRCop : ∀ n ∈ R, n.Coprime G := by
    intro n hn
    apply Nat.coprime_of_dvd
    intro p hp hpn hpG
    have hpLe : p ≤ C := (Nat.le_of_dvd (hR n hn).1 hpn).trans (Finset.le_sup (f := id) hn)
    have hpGt : C < p := (le_max_left _ _).trans_lt (hPrimes p hp hpG)
    omega
  refine ⟨T ∪ U, ?_, ?_⟩
  · have hUnion : reciprocalSum (T ∪ U) = reciprocalSum T + reciprocalSum U := Finset.sum_union hDisjoint
    rw [hUnion, hSum]
    ring
  · intro n hn
    rcases Finset.mem_union.mp hn with hnT | hnU
    · exact ⟨(hTerms n hnT).1, hTCop n hnT, (hTerms n hnT).2.2.trans (le_max_right _ _)⟩
    · have hnR := hUR hnU
      exact ⟨(hR n hnR).1, hRCop n hnR, (Finset.le_sup (f := id) hnR).trans (le_max_left _ _)⟩

end Erdos319Sharp
