import Erdos319Sharp.DenominatorDescent
import Erdos319Sharp.CoprimeArithmetic

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem exists_finite_denominator_descent :
    ∃ L₀ : ℕ, 2 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ r : ℚ,
      ∃ T Q : Finset ℕ,
        (∀ q ∈ Q, L < q ∧ q ≤ primaryHeight r.den) ∧
        primaryHeight (r - reciprocalSum T).den ≤ L ∧
        (reciprocalSum T : ℝ) ≤ ∑ q ∈ Q, logarithmicCorrectionCost q ∧
        (∀ n ∈ T, 0 < n ∧ ¬ 30 ∣ n ∧ ∃ q ∈ Q, primaryHeight n = q ∧
          ∃ b : ℕ, b.Prime ∧ n = q * b ∧ b ≤ ⌊Real.log q⌋₊ ^ 13) ∧
        ∀ G : ℕ, r.den.Coprime G →
          (∀ p : ℕ, p.Prime → p ∣ G → ⌊Real.log (primaryHeight r.den)⌋₊ ^ 13 < p) →
          (r - reciprocalSum T).den.Coprime G ∧ ∀ n ∈ T, n.Coprime G := by
  classical
  obtain ⟨L₀, hL₀, hStep⟩ := exists_denominator_descent_threshold
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL r
  generalize hHeight : primaryHeight r.den = H
  induction H using Nat.strong_induction_on generalizing r with
  | h H ih =>
      by_cases hSmall : H ≤ L
      · refine ⟨∅, ∅, by simp, ?_, by simp [reciprocalSum], by simp, ?_⟩
        · simpa only [reciprocalSum, Finset.sum_empty, sub_zero, hHeight] using hSmall
        · intro G hCop hLarge
          simpa [reciprocalSum] using And.intro hCop (show ∀ n ∈ (∅ : Finset ℕ), n.Coprime G by simp)
      · have hLarge : L₀ ≤ primaryHeight r.den := by omega
        obtain ⟨T₀, hDrop, hCost₀, hTerms₀⟩ := hStep r hLarge
        let r₁ := r - reciprocalSum T₀
        have hLess : primaryHeight r₁.den < H := by simpa only [r₁, hHeight] using hDrop
        obtain ⟨T₁, Q₁, hQ₁, hFinish, hCost₁, hTerms₁, hAvoid₁⟩ := ih (primaryHeight r₁.den) hLess r₁ rfl
        have hDisjoint : Disjoint T₀ T₁ := Finset.disjoint_left.mpr (by
          intro n hn₀ hn₁
          have hAt₀ := (hTerms₀ n hn₀).2.1
          obtain ⟨q, hq, hAt₁, _⟩ := (hTerms₁ n hn₁).2.2
          have hqSmall := (hQ₁ q hq).2
          omega)
        have hNot : H ∉ Q₁ := by
          intro hMem
          have hBound := (hQ₁ H hMem).2
          omega
        have hUnion : reciprocalSum (T₀ ∪ T₁) = reciprocalSum T₀ + reciprocalSum T₁ :=
          Finset.sum_union hDisjoint
        refine ⟨T₀ ∪ T₁, insert H Q₁, ?_, ?_, ?_, ?_, ?_⟩
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact ⟨by omega, le_rfl⟩
          · have h := hQ₁ q hq
            exact ⟨h.1, by omega⟩
        · have hResidual : r - reciprocalSum (T₀ ∪ T₁) = r₁ - reciprocalSum T₁ := by
            rw [hUnion]
            dsimp [r₁]
            ring
          rw [hResidual]
          exact hFinish
        · have hUnionReal : (reciprocalSum (T₀ ∪ T₁) : ℝ) =
              (reciprocalSum T₀ : ℝ) + (reciprocalSum T₁ : ℝ) := by exact_mod_cast hUnion
          rw [hUnionReal, Finset.sum_insert hNot]
          have hCost₀' : (reciprocalSum T₀ : ℝ) ≤ logarithmicCorrectionCost H := by
            simpa only [hHeight] using hCost₀
          exact add_le_add hCost₀' hCost₁
        · intro n hn
          rcases Finset.mem_union.mp hn with hn₀ | hn₁
          · obtain ⟨hPos, hAt₀, hThirty, b, hb, hEq, hB⟩ := hTerms₀ n hn₀
            have hAt : primaryHeight n = H := by simpa only [hHeight] using hAt₀
            refine ⟨hPos, hThirty, H, Finset.mem_insert_self _ _, hAt, b, hb, ?_, ?_⟩
            · simpa only [hHeight] using hEq
            · simpa only [hHeight] using hB
          · obtain ⟨hPos, hThirty, q, hq, hAt, b, hb, hEq, hB⟩ := hTerms₁ n hn₁
            exact ⟨hPos, hThirty, q, Finset.mem_insert_of_mem hq, hAt, b, hb, hEq, hB⟩
        · intro G hrCop hLargePrimes
          have hHCop : H.Coprime G := by
            rw [← hHeight]
            exact Nat.Coprime.of_dvd_left (primaryHeight_dvd r.den) hrCop
          have hT₀Cop : ∀ n ∈ T₀, n.Coprime G := by
            intro n hn
            obtain ⟨_, _, _, b, hb, hEq, hB⟩ := hTerms₀ n hn
            have hbCop := small_prime_coprime b G (⌊Real.log H⌋₊ ^ 13) hb
              (by simpa only [hHeight] using hB) (by simpa only [hHeight] using hLargePrimes)
            rw [hEq, hHeight]
            exact hHCop.mul_left hbCop
          have hr₁Cop : r₁.den.Coprime G :=
            sub_den_coprime r (reciprocalSum T₀) G hrCop (reciprocalSum_den_coprime T₀ G hT₀Cop)
          have hCap : ⌊Real.log (primaryHeight r₁.den)⌋₊ ^ 13 ≤ ⌊Real.log H⌋₊ ^ 13 := by
            have hHeightPos : 0 < primaryHeight r₁.den := one_le_primaryHeight r₁.den
            have hHeightLe : (primaryHeight r₁.den : ℝ) ≤ H := by exact_mod_cast hLess.le
            have hLog := Real.log_le_log
              (by exact_mod_cast hHeightPos : (0 : ℝ) < primaryHeight r₁.den)
              hHeightLe
            exact pow_le_pow_left₀ (Nat.zero_le _) (Nat.floor_mono hLog) 13
          obtain ⟨hFinalCop, hT₁Cop⟩ := hAvoid₁ G hr₁Cop (by
            intro p hp hpG
            exact hCap.trans_lt (by simpa only [hHeight] using hLargePrimes p hp hpG))
          refine ⟨?_, ?_⟩
          · have hResidual : r - reciprocalSum (T₀ ∪ T₁) = r₁ - reciprocalSum T₁ := by
              rw [hUnion]
              dsimp [r₁]
              ring
            rw [hResidual]
            exact hFinalCop
          · intro n hn
            exact (Finset.mem_union.mp hn).elim (hT₀Cop n) (hT₁Cop n)

theorem exists_small_denominator_remainder (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ r : ℚ, ∃ T : Finset ℕ,
      (r - reciprocalSum T).den ∣ (Finset.Icc 1 L).lcm id ∧
      (reciprocalSum T : ℝ) < ε ∧
      (∀ n ∈ T, 0 < n ∧ ¬ 30 ∣ n ∧
        n ≤ primaryHeight r.den * ⌊Real.log (primaryHeight r.den)⌋₊ ^ 13) ∧
      ∀ G : ℕ, r.den.Coprime G →
        (∀ p : ℕ, p.Prime → p ∣ G → ⌊Real.log (primaryHeight r.den)⌋₊ ^ 13 < p) →
        (r - reciprocalSum T).den.Coprime G ∧ ∀ n ∈ T, n.Coprime G := by
  obtain ⟨L₀, hL₀, hDescent⟩ := exists_finite_denominator_descent
  obtain ⟨L₁, hTail⟩ := exists_small_correction_tail ε hε
  let L := max L₀ L₁
  refine ⟨L, hL₀.trans (le_max_left _ _), ?_⟩
  intro r
  obtain ⟨T, Q, hQ, hFinish, hMass, hTerms, hAvoid⟩ := hDescent L (le_max_left _ _) r
  refine ⟨T, dvd_initial_lcm_of_primaryHeight_le _ L (r - reciprocalSum T).den_ne_zero hFinish,
    hMass.trans_lt (hTail Q ?_), ?_, hAvoid⟩
  · intro q hq
    exact (le_max_right L₀ L₁).trans (hQ q hq).1.le
  · intro n hn
    obtain ⟨hPos, hThirty, q, hq, hAt, b, hb, hEq, hB⟩ := hTerms n hn
    have hqPos : 0 < q := by have := (hQ q hq).1; omega
    have hLog : Real.log q ≤ Real.log (primaryHeight r.den) :=
      Real.log_le_log (by exact_mod_cast hqPos) (by exact_mod_cast (hQ q hq).2)
    have hFloor := Nat.floor_mono hLog
    have hPower := pow_le_pow_left₀ (Nat.zero_le _) hFloor 13
    refine ⟨hPos, hThirty, ?_⟩
    rw [hEq]
    exact Nat.mul_le_mul (hQ q hq).2 (hB.trans hPower)

end Erdos319Sharp
