import Erdos319Sharp.DenominatorStep
import Erdos319Sharp.PrimaryProducts

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem exists_denominator_descent_threshold :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ r : ℚ, L ≤ primaryHeight r.den →
      ∃ T : Finset ℕ,
        primaryHeight (r - reciprocalSum T).den < primaryHeight r.den ∧
        (reciprocalSum T : ℝ) ≤ logarithmicCorrectionCost (primaryHeight r.den) ∧
        ∀ n ∈ T, 0 < n ∧ primaryHeight n = primaryHeight r.den ∧ ¬ 30 ∣ n ∧
          ∃ b : ℕ, b.Prime ∧ n = primaryHeight r.den * b ∧
            b ≤ ⌊Real.log (primaryHeight r.den)⌋₊ ^ 13 := by
  obtain ⟨L₀, hStep⟩ := Filter.eventually_atTop.mp eventually_logarithmic_denominator_step
  refine ⟨max L₀ 2, le_max_right _ _, ?_⟩
  intro r hLarge
  let q := primaryHeight r.den
  have hqTwo : 2 ≤ q := (le_max_right L₀ 2).trans hLarge
  have hq : 0 < q := by omega
  obtain ⟨p, hp, hExponent, hHeight⟩ := exists_prime_at_primaryHeight r.den (by omega)
  let v := ordCompl[p] r.den
  have hv : 0 < v := Nat.ordCompl_pos p r.den_ne_zero
  have hFactor : q * v = r.den := by
    dsimp [q, v]
    rw [hHeight]
    exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hvCop : v.Coprime q := by
    dsimp [q]
    rw [hHeight]
    exact (Nat.coprime_ordCompl hp r.den_ne_zero).symm.pow_right _
  have hvHeight : primaryHeight v < q := primaryHeight_ordCompl_lt r.den p r.den_ne_zero hp hExponent hHeight
  obtain ⟨M, K, hKM, hCard, hPrimes, hResidual, hCost⟩ :=
    hStep q ((le_max_left L₀ 2).trans hLarge) v r hv hvCop (by rw [hFactor])
  let T := K.image (fun b => q * b)
  have hProduct : M.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun b hb => (hPrimes b hb).1.ne_zero)
  have hD : v.lcm (M.prod id) ≠ 0 := Nat.lcm_ne_zero hv.ne' hProduct
  have hHeightNew : primaryHeight (r - reciprocalSum T).den < q :=
    (primaryHeight_mono_dvd _ _ (r - reciprocalSum T).den_ne_zero hD hResidual).trans_lt
      (primaryHeight_lcm_prime_product_lt v q M hv.ne' hvHeight
        (fun b hb => (hPrimes b hb).1) (fun b hb => (hPrimes b hb).2.2.2.1))
  refine ⟨T, hHeightNew, hCost, ?_⟩
  intro n hn
  obtain ⟨b, hbK, rfl⟩ := Finset.mem_image.mp hn
  have hB := hPrimes b (hKM hbK)
  have hPrimeHeight : primaryHeight (q * b) = q := by
    dsimp [q]
    rw [hHeight]
    exact primaryHeight_prime_power_mul_prime p _ b hp hB.1 (hHeight ▸ hB.2.2.2.2)
      (hHeight ▸ hB.2.2.2.1)
  have hThirty : ¬ 30 ∣ q * b := by
    dsimp [q]
    rw [hHeight]
    exact not_thirty_dvd_prime_power_mul_prime p _ b hp hB.1
  exact ⟨Nat.mul_pos hq hB.1.pos, hPrimeHeight, hThirty, b, hB.1, rfl, hB.2.2.1⟩

end Erdos319Sharp
