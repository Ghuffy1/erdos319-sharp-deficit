import Erdos319Sharp.SingleDivisorCount
import Erdos319Sharp.ExcessCounting
import Erdos319Sharp.SmoothTailRate

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology
open scoped Classical

noncomputable section

namespace Erdos319Sharp

def smallMissingPowers (D N : ℕ) (S : ℝ) : Finset ℕ :=
  (firstMissingPowers D N).filter (fun q => (q : ℝ) ≤ S)

theorem firstMissingPower_isPrimePow (D p : ℕ) (hp : p.Prime) :
    IsPrimePow (firstMissingPower D p) :=
  (isPrimePow_nat_iff _).mpr ⟨p, D.factorization p + 1, hp, by omega, rfl⟩

theorem smallMissingPowers_subset (D N : ℕ) (S : ℝ) :
    smallMissingPowers D N S ⊆ firstMissingPowers D N := Finset.filter_subset _ _

theorem smallMissingPowers_card_le (D N : ℕ) (S : ℝ) (hD : D ≠ 0) (hS : 0 ≤ S) :
    ((smallMissingPowers D N S).card : ℝ) ≤ S := by
  have hSubset : smallMissingPowers D N S ⊆ Finset.Icc 1 ⌊S⌋₊ := by
    intro q hq
    obtain ⟨hqFirst, hqSmall⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(firstMissingPowers_conditions hD q hqFirst).1, Nat.le_floor hqSmall⟩
  have hCard : (smallMissingPowers D N S).card ≤ ⌊S⌋₊ := by
    simpa using Finset.card_le_card hSubset
  exact (by exact_mod_cast hCard : ((smallMissingPowers D N S).card : ℝ) ≤ (⌊S⌋₊ : ℝ)).trans
    (Nat.floor_le hS)

theorem smallMissingPowers_mass_error (D N : ℕ) (S : ℝ) (hD : D ≠ 0) :
    (reciprocalSum (firstMissingPowers D N) : ℝ) ≤
      (reciprocalSum (smallMissingPowers D N S) : ℝ) + primePowerTail N S := by
  classical
  let Tail : Finset ℕ := (firstMissingPowers D N).filter (fun q => ¬ (q : ℝ) ≤ S)
  have hSubset : Tail ⊆ (Finset.Icc 1 N).filter (fun q : ℕ => IsPrimePow q ∧ S < (q : ℝ)) := by
    intro q hq
    obtain ⟨hqFirst, hqLarge⟩ := Finset.mem_filter.mp hq
    obtain ⟨p, hp, _, _, rfl⟩ := mem_firstMissingPowers.mp hqFirst
    have hBounds := firstMissingPowers_conditions hD (firstMissingPower D p) hqFirst
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hBounds.1, hBounds.2.1⟩,
      firstMissingPower_isPrimePow D p hp, lt_of_not_ge hqLarge⟩
  have hTail : (reciprocalSum Tail : ℝ) ≤ primePowerTail N S := by
    rw [reciprocalSum_eq_baseline, reciprocalSum_real, primePowerTail]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun q _ _ => by positivity)
  have hSplitQ : reciprocalSum (smallMissingPowers D N S) + reciprocalSum Tail =
      reciprocalSum (firstMissingPowers D N) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hSplit : (reciprocalSum (smallMissingPowers D N S) : ℝ) + (reciprocalSum Tail : ℝ) =
      (reciprocalSum (firstMissingPowers D N) : ℝ) := by exact_mod_cast hSplitQ
  linarith only [hSplit, hTail]

theorem single_small_missing_smooth_scale (D N n : ℕ) (a S : ℝ) (ha : 0 ≤ a)
    (hD : D ≠ 0) (hSingle : n ∈ singleDivisorSet a N (smallMissingPowers D N S))
    (hSmooth : PrimePowerSmooth S n) :
    ¬ n ∣ D ∧ (excessScale D (denominatorExcess D n) : ℝ) ≤ S := by
  obtain ⟨hnTail, q, hq, hqn, hUnique⟩ := (mem_singleDivisorSet a N n _).mp hSingle
  have hnBounds := (mem_tailInterval a ha N n).mp hnTail
  have hn : 0 < n := hnBounds.1
  obtain ⟨hqFirst, _⟩ := Finset.mem_filter.mp hq
  have hNot : ¬ n ∣ D := by
    intro hnD
    exact (firstMissingPowers_conditions hD q hqFirst).2.2 (hqn.trans hnD)
  obtain ⟨p, hp, _, _, hPowerEq⟩ := mem_firstMissingPowers.mp hqFirst
  have hqn' : firstMissingPower D p ∣ n := hPowerEq ▸ hqn
  let b := denominatorExcess D n
  have hbPos : 0 < b := denominatorExcess_pos D n hn
  have hbNe : b ≠ 1 := fun h => hNot (dvd_of_denominatorExcess_eq_one D n h)
  have hOnly : ∀ {r : ℕ}, r.Prime → r ∣ b → r = p := by
    intro r hr hrb
    have hDiv := firstMissingPower_dvd_of_prime_dvd_excess D n r hD hn hr hrb
    have hPowerN : firstMissingPower D r ≤ N :=
      (Nat.le_of_dvd hn hDiv).trans hnBounds.2.1
    have hSmall : (firstMissingPower D r : ℝ) ≤ S :=
      hSmooth _ (firstMissingPower_isPrimePow D r hr) hDiv
    have hMem : firstMissingPower D r ∈ smallMissingPowers D N S :=
      Finset.mem_filter.mpr ⟨firstMissingPower_mem hr hPowerN, hSmall⟩
    have hEqual : firstMissingPower D r = firstMissingPower D p :=
      (hUnique _ hMem hDiv).trans hPowerEq.symm
    exact firstMissingPower_injective hr hp hEqual
  let k := b.primeFactorsList.length
  have hbPow : b = p ^ k := Nat.eq_prime_pow_of_unique_prime_dvd hbPos.ne' hOnly
  have hk : 0 < k := by
    by_contra hNotPos
    have hkZero : k = 0 := by omega
    rw [hkZero, pow_zero] at hbPow
    exact hbNe hbPow
  have hValuation := excess_prime_pow_valuation D n p k hD hn.ne' hp hk hbPow
  have hExpPos : 0 < n.factorization p := by omega
  have hPowerDiv : p ^ n.factorization p ∣ n :=
    (hp.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
  have hPowerSmooth : (p ^ n.factorization p : ℕ) ≤ S :=
    hSmooth _ ((isPrimePow_nat_iff _).mpr ⟨p, n.factorization p, hp, hExpPos, rfl⟩) hPowerDiv
  refine ⟨hNot, ?_⟩
  change (excessScale D b : ℝ) ≤ S
  rw [hbPow, excessScale_prime_pow D p k hD hp hk, ← hValuation]
  exact hPowerSmooth

theorem smooth_single_missing_count_lower (a S : ℝ) (D N : ℕ)
    (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4) (hS : 0 ≤ S) (hD : D ≠ 0) :
    (1 - 2 * a) * (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) -
      (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) ^ 2 -
        4 * S - 2 * (N : ℝ) * primePowerTail N S ≤
          (((singleDivisorSet a N (smallMissingPowers D N S)).filter
            (fun n => PrimePowerSmooth S n)).card : ℝ) := by
  classical
  let Q := smallMissingPowers D N S
  let A := singleDivisorSet a N Q
  have hQSubset := smallMissingPowers_subset D N S
  have hCount := single_divisor_count_lower a ha N Q
    (fun q hq => (firstMissingPowers_conditions hD q (hQSubset hq)).1)
    (fun q hq r hr hNe => firstMissingPowers_pairwise_coprime D N q (hQSubset hq) r (hQSubset hr) hNe)
  have hQCard := smallMissingPowers_card_le D N S hD hS
  have hPrefix : A ⊆ Finset.Icc 1 N := by
    intro n hn
    exact tailInterval_subset a N ((Finset.mem_filter.mp hn).1)
  have hLoss := nonsmooth_card_bound A hPrefix S
  have hSplit : (((A.filter (fun n => PrimePowerSmooth S n)).card : ℝ)) +
      (A.filter (fun n => ¬ PrimePowerSmooth S n)).card = A.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (fun n => PrimePowerSmooth S n)
  have hSmallNonneg : (0 : ℝ) ≤ reciprocalSum Q := by
    have h : (0 : ℚ) ≤ reciprocalSum Q := Finset.sum_nonneg (fun n _ => by positivity)
    exact_mod_cast h
  have hMassLe : (reciprocalSum Q : ℝ) ≤ reciprocalSum (firstMissingPowers D N) := by
    have h : reciprocalSum Q ≤ reciprocalSum (firstMissingPowers D N) :=
      Finset.sum_le_sum_of_subset_of_nonneg hQSubset (fun n _ _ => by positivity)
    exact_mod_cast h
  have hMassError := smallMissingPowers_mass_error D N S hD
  have hCoefNonneg : 0 ≤ 1 - 2 * a := by linarith
  have hWeighted := mul_le_mul_of_nonneg_left hMassError
    (mul_nonneg hCoefNonneg (Nat.cast_nonneg N))
  have hSquare := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hSmallNonneg hMassLe 2) (Nat.cast_nonneg N)
  have hTailNonneg : 0 ≤ primePowerTail N S := Finset.sum_nonneg (fun n _ => by positivity)
  have hTailWeight := mul_le_mul_of_nonneg_right
    (show 1 - 2 * a ≤ (1 : ℝ) by linarith) (mul_nonneg (Nat.cast_nonneg N) hTailNonneg)
  change (1 - 2 * a) * (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) -
    (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) ^ 2 -
      4 * S - 2 * (N : ℝ) * primePowerTail N S ≤ _
  dsimp only [Q] at hCount
  nlinarith only [hCount, hQCard, hLoss, hSplit, hWeighted, hSquare, hTailWeight]

end Erdos319Sharp
