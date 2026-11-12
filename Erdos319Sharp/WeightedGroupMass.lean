import Erdos319Sharp.PrimeWeightCover
import Erdos319Sharp.WeightSupport
import Erdos319Sharp.GroupHarmonic

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_weighted_excess_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ Y₀ : ℕ, 3 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y → ∀ᶠ N : ℕ in atTop,
      ∀ (D : ℕ) (A : Finset ℕ), D ≠ 0 → A ⊆ Finset.Icc 1 N →
        (∀ b : ℕ, 0 < b → InverseZeroSumFree b (excessCofactors D b A)) →
        (reciprocalSum A : ℝ) ≤ 3 * weightedPrimeProduct Y.primesLE (1 / 2) +
          (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log N) *
            (1 - (Y : ℝ)⁻¹)⁻¹ *
            Real.exp (2 * (reciprocalSum (firstMissingPowers D N) : ℝ)) *
            (reciprocalSum (firstMissingPowers D N) : ℝ) := by
  classical
  obtain ⟨Y₀, hY₀, hSharp⟩ := eventually_excessGroup_mass_sharp ε hε
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y hY
  filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ))]
    with N hLogLog
  intro D A hD hA hFree
  let B := activeExcesses D A
  let P := missingPrimeBases D N
  let Q := Y.primesLE
  let Small := B.filter (fun b => b ∈ Nat.factoredNumbers Q)
  let Large := B.filter (fun b => ¬b ∈ Nat.factoredNumbers Q)
  let H := P.filter (fun p => Y < p)
  let ρ : ℝ := (reciprocalSum (firstMissingPowers D N) : ℝ)
  let gap : ℝ := (1 - (Y : ℝ)⁻¹)⁻¹
  let C : ℝ := (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log N)
  have hPos : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  have hBounds : B ⊆ Finset.Icc 1 N := activeExcesses_bounds D N A hA
  have hFactored : ∀ b ∈ B, b ∈ Nat.factoredNumbers P := activeExcesses_factored D N A hD hA
  have hP : ∀ p ∈ P, p.Prime := fun p hp => missingPrimeBases_prime D N p hp
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hHP : H ⊆ P := Finset.filter_subset _ _
  have hYTwo : 2 ≤ Y := by omega
  have hYOne : (1 : ℝ) < Y := by exact_mod_cast (by omega : 1 < Y)
  have hGap : 0 ≤ gap := inv_nonneg.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hYOne)).le
  have hC : 0 ≤ C := mul_nonneg (by positivity) hLogLog
  have hRho : ρ = ∑ p ∈ P, (firstMissingPower D p : ℝ)⁻¹ := missingPrimeBases_mass D N
  have hSmall : (∑ b ∈ Small, (reciprocalSum (excessGroup D b A) : ℝ)) ≤
      3 * weightedPrimeProduct Q (1 / 2) :=
    small_prime_excess_mass_bound D A Small Q hD hPos hQ
      (fun b hb => (Finset.mem_filter.mp hb).2)
      (fun b hb => hFree b (Finset.mem_Icc.mp (hBounds (Finset.mem_filter.mp hb).1)).1)
  have hCover : ∀ b ∈ Large, ∃ p ∈ H, p ∣ b := by
    intro b hb
    obtain ⟨hbB, hbNot⟩ := Finset.mem_filter.mp hb
    have hbPos : 0 < b := (Finset.mem_Icc.mp (hBounds hbB)).1
    have hExists : ∃ p ∈ b.primeFactors, p ∉ Q := by
      by_contra hNone
      apply hbNot
      apply Nat.mem_factoredNumbers_of_primeFactors_subset hbPos.ne'
      intro p hp
      by_contra hpNot
      exact hNone ⟨p, hp, hpNot⟩
    obtain ⟨p, hpb, hpNot⟩ := hExists
    have hpPrime := Nat.prime_of_mem_primeFactors hpb
    have hpP : p ∈ P := Nat.primeFactors_subset_of_mem_factoredNumbers (hFactored b hbB) hpb
    have hYp : Y < p := by
      by_contra h
      exact hpNot (Nat.mem_primesLE.mpr ⟨le_of_not_gt h, hpPrime⟩)
    exact ⟨p, Finset.mem_filter.mpr ⟨hpP, hYp⟩, Nat.dvd_of_mem_primeFactors hpb⟩
  have hSigma : (∑ p ∈ H, primeExcessMass D p) ≤ gap * ρ := by
    calc
      (∑ p ∈ H, primeExcessMass D p) ≤ ∑ p ∈ H, gap * (firstMissingPower D p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        exact primeExcessMass_le_cutoff D p Y hYTwo (Finset.mem_filter.mp hp).2.le
      _ = gap * ∑ p ∈ H, (firstMissingPower D p : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ gap * ∑ p ∈ P, (firstMissingPower D p : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hHP (fun _ _ _ => by positivity)) hGap
      _ = gap * ρ := by rw [hRho]
  have hWeight : (∑ b ∈ Large, excessWeight D b) ≤ (gap * ρ) * Real.exp (2 * ρ) := by
    have h := prime_cover_excess_sum_le D Large P H hD hP hHP
      (fun b hb => hFactored b (Finset.mem_filter.mp hb).1) hCover
    rw [← hRho] at h
    exact h.trans (mul_le_mul_of_nonneg_right hSigma (Real.exp_nonneg _))
  have hLarge : (∑ b ∈ Large, (reciprocalSum (excessGroup D b A) : ℝ)) ≤
      C * gap * Real.exp (2 * ρ) * ρ := by
    calc
      (∑ b ∈ Large, (reciprocalSum (excessGroup D b A) : ℝ)) ≤ ∑ b ∈ Large, C * excessWeight D b := by
        apply Finset.sum_le_sum
        intro b hb
        have hbB := (Finset.mem_filter.mp hb).1
        have hbPos : 0 < b := (Finset.mem_Icc.mp (hBounds hbB)).1
        obtain ⟨p, hpH, hpb⟩ := hCover b hb
        have hYb : Y ≤ b := (Finset.mem_filter.mp hpH).2.le.trans (Nat.le_of_dvd hbPos hpb)
        exact hSharp D N b A hD (hY.trans hYb) (Finset.mem_Icc.mp (hBounds hbB)).2 hPos (hFree b hbPos)
      _ = C * ∑ b ∈ Large, excessWeight D b := (Finset.mul_sum _ _ _).symm
      _ ≤ C * ((gap * ρ) * Real.exp (2 * ρ)) := mul_le_mul_of_nonneg_left hWeight hC
      _ = C * gap * Real.exp (2 * ρ) * ρ := by ring
  have hPartition : (∑ b ∈ Small, (reciprocalSum (excessGroup D b A) : ℝ)) +
      (∑ b ∈ Large, (reciprocalSum (excessGroup D b A) : ℝ)) =
      ∑ b ∈ B, (reciprocalSum (excessGroup D b A) : ℝ) := Finset.sum_filter_add_sum_filter_not _ _ _
  have hWhole : (∑ b ∈ B, (reciprocalSum (excessGroup D b A) : ℝ)) = (reciprocalSum A : ℝ) := by
    simpa only [B, Rat.cast_sum] using congrArg (fun r : ℚ => (r : ℝ)) (reciprocalSum_activeExcesses D A)
  change (reciprocalSum A : ℝ) ≤ 3 * weightedPrimeProduct Q (1 / 2) + C * gap * Real.exp (2 * ρ) * ρ
  rw [← hWhole, ← hPartition]
  exact add_le_add hSmall hLarge

end Erdos319Sharp
