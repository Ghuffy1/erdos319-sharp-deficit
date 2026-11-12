import Erdos319Sharp.ConstructionSelection
import Erdos319Sharp.PrimeSetPath

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def constructionSupportCap (P : Finset ℕ) (N : ℕ) : ℕ :=
  max (constructionPrimeBase N ^ 2 * constructionModulus N)
    (4 * P.card * (constructionPrimeBase N ^ 2) ^ 4)

theorem constructionPrimeBase_sq_le_power (N : ℕ) :
    ((constructionPrimeBase N ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
  calc
    ((constructionPrimeBase N ^ 2 : ℕ) : ℝ) = (constructionPrimeBase N : ℝ) ^ 2 := by norm_cast
    _ ≤ ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (constructionPrimeBase_le_power N) _
    _ = (N : ℝ) ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num

theorem eventually_constructionSupportCap_bound :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ, P ⊆ constructionPrimeBand N →
      (constructionSupportCap P N : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
  have hGrowth := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hGrowth, eventually_ge_atTop (1 : ℕ)] with N hGrowthN hN P hP
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hSquare := constructionPrimeBase_sq_le_power N
  have hCard : (P.card : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    have h : P.card ≤ constructionPrimeBase N ^ 2 :=
      (Finset.card_le_card hP).trans (constructionPrimeBand_card_le N)
    exact (show (P.card : ℝ) ≤ ((constructionPrimeBase N ^ 2 : ℕ) : ℝ) by exact_mod_cast h).trans hSquare
  have hFirst : ((constructionPrimeBase N ^ 2 * constructionModulus N : ℕ) : ℝ) ≤
      (N : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ = ((constructionPrimeBase N ^ 2 : ℕ) : ℝ) * constructionModulus N := by norm_cast
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ) :=
        mul_le_mul hSquare (constructionModulus_power_bound N hN) (Nat.cast_nonneg _) (by positivity)
      _ = (N : ℝ) ^ (11 / 100 : ℝ) := by rw [← Real.rpow_add hNPos]; norm_num
      _ ≤ (N : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNOne (by norm_num)
  have hSecond : ((4 * P.card * (constructionPrimeBase N ^ 2) ^ 4 : ℕ) : ℝ) ≤
      (N : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ = 4 * (P.card : ℝ) * (((constructionPrimeBase N ^ 2 : ℕ) : ℝ) ^ 4) := by norm_cast
      _ ≤ 4 * (N : ℝ) ^ (1 / 10 : ℝ) * ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 4 := by
        gcongr
      _ = 4 * ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 5 := by ring
      _ = 4 * (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
        norm_num
      _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hGrowthN (by positivity)
      _ = (N : ℝ) ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hNPos]; norm_num
  simpa only [constructionSupportCap, Nat.cast_max] using max_le hFirst hSecond

theorem eventually_exists_constructionCore (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∃ P E : Finset ℕ,
      P ⊆ constructionPrimeBand N ∧ 2 ≤ P.card ∧
      constructionTarget η N ≤ (∑ p ∈ P, (1 : ℝ) / p) ∧
      (∑ p ∈ P, (1 : ℝ) / p) < constructionTarget η N + 1 / constructionPrimeBase N ∧
      MinimalCore (P.prod id) E ∧ E ⊆ Icc 1 N ∧
      (∀ n ∈ E, (n : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ)) ∧
      constructionMass N * (∑ p ∈ P, (1 : ℝ) / p) ≤ (reciprocalSum E : ℝ) ∧
      (reciprocalSum E : ℝ) ≤ constructionMass N * (∑ p ∈ P, (1 : ℝ) / p) +
        (∑ p ∈ P, (1 : ℝ) / p) / constructionPrimeBase N := by
  filter_upwards [eventually_exists_constructionPrimes η hη,
    eventually_constructionPrimeBand_avoids_modulus, eventually_constructionSupportCap_bound,
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ)),
    eventually_ge_atTop (1 : ℕ)] with N hSelect hAvoid hCap hBase hN
  obtain ⟨P, hP, hCard, hLower, hUpper, hMass⟩ := hSelect
  have hPrime : ∀ p ∈ P, p.Prime := fun p hp => (mem_constructionPrimeBand.mp (hP hp)).1
  obtain ⟨E, hCore, hE, hELower, hEUpper⟩ := exists_prime_set_path_core P (constructionModulus N)
    (constructionPrimeBase N) (constructionPrimeBase N ^ 2) hCard (constructionModulus_pos N)
    (by omega) hPrime (fun p hp => (hAvoid p (hP hp)).1)
    (fun p hp => (hAvoid p (hP hp)).2)
    (fun p hp => (mem_constructionPrimeBand.mp (hP hp)).2.1.le)
    (fun p hp => (mem_constructionPrimeBand.mp (hP hp)).2.2) hMass
  have hCapBound := hCap P hP
  have hSmall : ∀ n ∈ E, (n : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
    intro n hn
    have hLe : n ≤ constructionSupportCap P N := (Finset.mem_Icc.mp (hE hn)).2
    exact (show (n : ℝ) ≤ constructionSupportCap P N by exact_mod_cast hLe).trans hCapBound
  have hInside : E ⊆ Icc 1 N := by
    intro n hn
    have hPower : (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ N by exact_mod_cast hN) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    have hLe : n ≤ N := by exact_mod_cast (hSmall n hn).trans hPower
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hE hn)).1, hLe⟩
  have hPMass : (reciprocalSum P : ℝ) = ∑ p ∈ P, (1 : ℝ) / p := by
    exact Erdos319Formal.reciprocalSum_real P
  have hELowerReal : constructionMass N * (reciprocalSum P : ℝ) ≤ (reciprocalSum E : ℝ) := by
    change (reciprocalSum (constructionModulus N).divisors : ℝ) * (reciprocalSum P : ℝ) ≤ _
    exact_mod_cast hELower
  have hEUpperReal : (reciprocalSum E : ℝ) ≤ constructionMass N * (reciprocalSum P : ℝ) +
      (reciprocalSum P : ℝ) / constructionPrimeBase N := by
    change (reciprocalSum E : ℝ) ≤
      (reciprocalSum (constructionModulus N).divisors : ℝ) * (reciprocalSum P : ℝ) + _
    exact_mod_cast hEUpper
  exact ⟨P, E, hP, hCard, hLower, hUpper, hCore, hInside, hSmall,
    by simpa only [hPMass] using hELowerReal, by simpa only [hPMass] using hEUpperReal⟩

end Erdos319Sharp
