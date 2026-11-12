import Erdos319Sharp.ConstructionGrowth
import Erdos319Sharp.FiniteSelection

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def constructionTarget (η : ℝ) (N : ℕ) : ℝ :=
  (Real.log (constructionMass N) + η) / constructionMass N

theorem tendsto_constructionTarget (η : ℝ) :
    Tendsto (constructionTarget η) atTop (𝓝 0) := by
  have hLog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_constructionMass
  have hEta : Tendsto (fun N : ℕ => η / constructionMass N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_constructionMass) :
        Tendsto (fun N : ℕ => η * (constructionMass N)⁻¹) atTop (𝓝 (η * 0)))
  change Tendsto (fun N : ℕ =>
    (Real.log (constructionMass N) + η) / constructionMass N) atTop (𝓝 0)
  simpa only [Function.comp_def, id_eq, add_div, zero_add] using hLog.add hEta

theorem constructionTarget_pos (η : ℝ) (hη : 0 < η) (N : ℕ) :
    0 < constructionTarget η N := by
  have hMass := constructionMass_one_le N
  have hLog := Real.log_nonneg hMass
  exact div_pos (by linarith) (by linarith)

theorem eventually_exists_constructionPrimes (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∃ P : Finset ℕ,
      P ⊆ constructionPrimeBand N ∧ 2 ≤ P.card ∧
      constructionTarget η N ≤ (∑ p ∈ P, (1 : ℝ) / p) ∧
      (∑ p ∈ P, (1 : ℝ) / p) < constructionTarget η N + 1 / constructionPrimeBase N ∧
      (∑ p ∈ P, (1 : ℝ) / p) ≤ 1 / 2 := by
  let δ : ℝ := Real.log 2 / 2
  have hLogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδUpper : δ < Real.log 2 := by dsimp [δ]; linarith
  have hInverse : Tendsto (fun N : ℕ => (1 : ℝ) / constructionPrimeBase N) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_constructionPrimeBase)
  have hSpace := ((tendsto_constructionTarget η).add hInverse).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1 / 2))
  filter_upwards [hSpace,
    (tendsto_constructionTarget η).eventually (Iio_mem_nhds hδ),
    tendsto_constructionPrimeBand_mass.eventually (Ioi_mem_nhds hδUpper),
    tendsto_constructionMass_div_primeBase.eventually (Iio_mem_nhds hη),
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))]
    with N hSpace hTarget hBand hStepMass hBase
  have hBasePos : (0 : ℝ) < constructionPrimeBase N := by
    exact_mod_cast (by omega : 0 < constructionPrimeBase N)
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  have hStrict : 1 / (constructionPrimeBase N : ℝ) < constructionTarget η N := by
    apply (lt_div_iff₀ hMassPos).mpr
    have hLog := Real.log_nonneg (constructionMass_one_le N)
    change (1 / (constructionPrimeBase N : ℝ)) * constructionMass N <
      Real.log (constructionMass N) + η
    have hRearrange : (1 / (constructionPrimeBase N : ℝ)) * constructionMass N =
        constructionMass N / constructionPrimeBase N := by ring
    rw [hRearrange]
    linarith
  obtain ⟨P, hP, hCard, hLower, hUpper⟩ := exists_subset_sum_window_card_two
    (constructionPrimeBand N) (fun p : ℕ => (1 : ℝ) / p)
    (constructionTarget η N) (1 / constructionPrimeBase N)
    (constructionTarget_pos η hη N) hStrict (hTarget.le.trans hBand.le)
    (fun p hp => one_div_le_one_div_of_le hBasePos
      (by exact_mod_cast (mem_constructionPrimeBand.mp hp).2.1.le))
  exact ⟨P, hP, hCard, hLower, hUpper, hUpper.le.trans hSpace.le⟩

theorem constructionModulus_le_divisor_sum (N : ℕ) :
    constructionModulus N ≤
      ∑ n ∈ (constructionModulus N).divisors, constructionModulus N / n := by
  have h : (constructionModulus N : ℝ) ≤ (constructionModulus N : ℝ) * constructionMass N := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (constructionMass_one_le N)
      (show (0 : ℝ) ≤ constructionModulus N from Nat.cast_nonneg _)
  rw [← construction_divisor_sum N] at h
  exact_mod_cast h

theorem eventually_constructionPrimeBand_avoids_modulus :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ constructionPrimeBand N,
      ¬p ∣ constructionModulus N ∧
        (∑ n ∈ (constructionModulus N).divisors, constructionModulus N / n) + 1 < p := by
  filter_upwards [eventually_construction_divisor_sum_lt_primeBase] with N hN p hp
  have hPrime := mem_constructionPrimeBand.mp hp
  have hBound := hN.trans hPrime.2.1
  refine ⟨?_, hBound⟩
  intro hDiv
  have hLe := Nat.le_of_dvd (constructionModulus_pos N) hDiv
  have hSum := constructionModulus_le_divisor_sum N
  omega

end Erdos319Sharp
