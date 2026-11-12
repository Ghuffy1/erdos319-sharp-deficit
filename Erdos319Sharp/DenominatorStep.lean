import Erdos319Sharp.CorrectionCost
import Erdos319Sharp.ResidueCorrection
import Erdos319Sharp.Uniform

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_logarithmic_power_below_modulus :
    ∀ᶠ q : ℕ in atTop, ⌊Real.log q⌋₊ ^ 13 < q := by
  have hLimit := (tendsto_log_pow_div_nat_rpow 13 1 (by norm_num)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hLimit, tendsto_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with q hSmall hLog hq
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [Real.rpow_one] at hSmall
  have hPower : (Real.log q) ^ 13 < (q : ℝ) := by
    simpa only [Real.rpow_one, one_mul] using (div_lt_iff₀ hqReal).mp hSmall
  have hFloorPower : ((⌊Real.log q⌋₊ : ℝ) ^ 13) ≤ (Real.log q) ^ 13 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hLog) 13
  exact_mod_cast hFloorPower.trans_lt hPower

/-- One correction removes the chosen modulus from a rational denominator.
The introduced primes are smaller, and its reciprocal cost is summable. -/
theorem eventually_logarithmic_denominator_step :
    ∀ᶠ q : ℕ in atTop, ∀ (v : ℕ) (r : ℚ),
      0 < v → v.Coprime q → r.den ∣ q * v →
      ∃ (M K : Finset ℕ), K ⊆ M ∧ M.card = ⌊Real.log q⌋₊ ^ 10 ∧
        (∀ p ∈ M, p.Prime ∧ ⌊Real.log q⌋₊ ^ 12 < p ∧
          p ≤ ⌊Real.log q⌋₊ ^ 13 ∧ p < q ∧ ¬ p ∣ q) ∧
        (r - reciprocalSum (K.image (fun p => q * p))).den ∣ v.lcm (M.prod id) ∧
        (reciprocalSum (K.image (fun p => q * p)) : ℝ) ≤ logarithmicCorrectionCost q := by
  filter_upwards [eventually_logarithmic_prime_inverse_subset_sum,
    eventually_logarithmic_power_below_modulus,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with q hPool hBelow hLog hq
  intro v r hv hCoprime hDen
  obtain ⟨M, hCard, hPrimes, hCover⟩ := hPool
  let D := v.lcm (M.prod id)
  have hProduct : M.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
    intro p hp
    exact (hPrimes p hp).1.ne_zero)
  have hD : D ≠ 0 := Nat.lcm_ne_zero hv.ne' hProduct
  have hProductCop : (M.prod id).Coprime q := Nat.coprime_prod_left_iff.mpr (by
    intro p hp
    exact (hPrimes p hp).1.coprime_iff_not_dvd.mpr (hPrimes p hp).2.2.2)
  have hDCop : D.Coprime q :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul v (M.prod id)) (hCoprime.mul_left hProductCop)
  have hVDiv : v ∣ D := Nat.dvd_lcm_left _ _
  have hDenD : r.den ∣ q * D := hDen.trans (Nat.mul_dvd_mul_left q hVDiv)
  obtain ⟨z, hz⟩ := exists_integer_numerator_over_common r (q * D)
    (Nat.mul_ne_zero hq.ne' hD) hDenD
  obtain ⟨K, hKM, hKCard, hKSum⟩ := hCover ((D : ZMod q)⁻¹ * (z : ZMod q))
  have hKDiv : ∀ p ∈ K, p ∣ D := by
    intro p hp
    exact (Finset.dvd_prod_of_mem id (hKM hp)).trans (Nat.dvd_lcm_right v (M.prod id))
  have hResidue : (D : ZMod q) * (∑ p ∈ K, (p : ZMod q)⁻¹) = (z : ZMod q) := by
    rw [hKSum, ← mul_assoc, ZMod.coe_mul_inv_eq_one D hDCop, one_mul]
  have hResidual := cancel_modular_denominator K D q z hD hq hDCop hKDiv hResidue
  have hResidual' : (r - reciprocalSum (K.image (fun p => q * p))).den ∣ D := by
    rw [hz]
    simpa only [Nat.cast_mul] using hResidual
  have hm : 0 < ⌊Real.log q⌋₊ := Nat.floor_pos.mpr hLog
  have hCost := logarithmic_pool_reciprocal_cost hq hm K hKCard
    (fun p hp => (hPrimes p (hKM hp)).2.1.le)
  have hMass : (reciprocalSum (K.image (fun p => q * p)) : ℝ) ≤ logarithmicCorrectionCost q := by
    rw [reciprocalSum_eq_baseline, reciprocalSum_real,
      Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hq h)]
    simpa only [Nat.cast_mul, logarithmicCorrectionCost] using hCost
  refine ⟨M, K, hKM, hCard, ?_, hResidual', hMass⟩
  intro p hp
  have h := hPrimes p hp
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.1.trans_lt hBelow, h.2.2.2⟩

end Erdos319Sharp
