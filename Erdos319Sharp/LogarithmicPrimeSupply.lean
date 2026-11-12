import Erdos319Sharp.PrimePool
import Erdos319Sharp.ModularInverse

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem logarithmic_pool_martin_bounds (q m : ℕ) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hLog : Real.log q ≤ 2 * (m : ℝ))
    (hLL : 1 ≤ Real.log (Real.log q))
    (hLarge : 800 < Real.log (Real.log q) ^ (2 / 3 : ℝ)) :
    1 / Real.log (Real.log q) ^ (1 / 2 : ℝ) < 2 * (m : ℝ) ^ 13 ∧
      200 * ((2 * (m : ℝ) ^ 13) ^ (2 / 3 : ℝ) * Real.log q /
        Real.log (Real.log q) ^ (2 / 3 : ℝ)) < (m : ℝ) ^ 10 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hL0 : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hOne : (1 : ℝ) ≤ Real.log (Real.log q) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hLL (by norm_num)
  constructor
  · have hRec : 1 / Real.log (Real.log q) ^ (1 / 2 : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).mpr hOne
    have hPower : (1 : ℝ) ≤ (m : ℝ) ^ 13 := one_le_pow₀ hmR
    linarith
  · have hTwo : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (2 / 3 : ℝ) ≤ 1)
    have hPower : ((m : ℝ) ^ 13) ^ (2 / 3 : ℝ) = (m : ℝ) ^ (26 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
      norm_num
    have hExponent : (m : ℝ) ^ (26 / 3 : ℝ) ≤ (m : ℝ) ^ 9 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hmR (by norm_num : (26 / 3 : ℝ) ≤ 9)
    have hB : (2 * (m : ℝ) ^ 13) ^ (2 / 3 : ℝ) ≤ 2 * (m : ℝ) ^ 9 := by
      rw [Real.mul_rpow (by norm_num) (by positivity), hPower]
      exact mul_le_mul hTwo hExponent (by positivity) (by norm_num)
    have hNumerator : 200 * ((2 * (m : ℝ) ^ 13) ^ (2 / 3 : ℝ) * Real.log q) ≤
        800 * (m : ℝ) ^ 10 := by
      calc
        200 * ((2 * (m : ℝ) ^ 13) ^ (2 / 3 : ℝ) * Real.log q) ≤
            200 * ((2 * (m : ℝ) ^ 9) * (2 * m)) := by
          gcongr
        _ = 800 * (m : ℝ) ^ 10 := by ring
    have hDen : 0 < Real.log (Real.log q) ^ (2 / 3 : ℝ) := by linarith
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hDen).mpr
    exact hNumerator.trans_lt (by
      have h := mul_lt_mul_of_pos_right hLarge (pow_pos hm0 10)
      simpa only [mul_comm] using h)

/-- Every residue has an inverse-sum representation using a thinned prime
pool whose endpoints are powers of the integer part of the logarithm. -/
theorem eventually_logarithmic_prime_inverse_subset_sum :
    ∀ᶠ q : ℕ in atTop,
      ∃ M : Finset ℕ, M.card = ⌊Real.log q⌋₊ ^ 10 ∧
        (∀ p ∈ M, p.Prime ∧ ⌊Real.log q⌋₊ ^ 12 < p ∧
          p ≤ ⌊Real.log q⌋₊ ^ 13 ∧ ¬ p ∣ q) ∧
        ∀ a : ZMod q, ∃ K ⊆ M, K.card ≤ ⌊Real.log q⌋₊ ^ 10 ∧
          K.sum (fun p => ((p : ZMod q)⁻¹)) = a := by
  have hL : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL := Real.tendsto_log_atTop.comp hL
  have hFloor : Tendsto (fun q : ℕ => ⌊Real.log q⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hL
  have hPower := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hLL
  filter_upwards [eventually_prime_inverse_subset_sum,
    hFloor.eventually eventually_prime_pool_for_log_bound,
    hFloor.eventually (eventually_ge_atTop (1 : ℕ)),
    hLL.eventually (eventually_ge_atTop (1 : ℝ)),
    hPower.eventually (eventually_gt_atTop (800 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with q hMartin hPool hm hLLq hLarge hq
  let m : ℕ := ⌊Real.log q⌋₊
  have hLog : Real.log q ≤ (m : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  obtain ⟨M, hCard, hPrimes⟩ := hPool q (by omega) hLog
  have hLog' : Real.log q ≤ 2 * (m : ℝ) := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨hSmall, hLarge'⟩ := logarithmic_pool_martin_bounds q m hm hq hLog' hLLq hLarge
  refine ⟨M, hCard, hPrimes, ?_⟩
  apply hMartin (m ^ 10) (2 * (m : ℝ) ^ 13) M hCard.le (by positivity) hSmall
  · simpa only [hCard, Nat.cast_pow] using hLarge'
  · intro p hp
    obtain ⟨hPrime, hLower, hUpper, hAway⟩ := hPrimes p hp
    refine ⟨?_, hPrime, hAway⟩
    have hUpperR : (p : ℝ) ≤ (m : ℝ) ^ 13 := by exact_mod_cast hUpper
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hPositive := pow_pos hm0 13
    linarith

theorem logarithmic_pool_reciprocal_cost {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (E : Finset ℕ) (hCard : E.card ≤ m ^ 10)
    (hLower : ∀ p ∈ E, m ^ 12 ≤ p) :
    (∑ p ∈ E, (1 : ℝ) / ((q : ℝ) * p)) ≤ 1 / ((q : ℝ) * (m : ℝ) ^ 2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    (∑ p ∈ E, (1 : ℝ) / ((q : ℝ) * p)) ≤
        ∑ _p ∈ E, (1 : ℝ) / ((q : ℝ) * (m : ℝ) ^ 12) := by
      apply Finset.sum_le_sum
      intro p hp
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hLower p hp) hqR.le
    _ = (E.card : ℝ) / ((q : ℝ) * (m : ℝ) ^ 12) := by simp [div_eq_mul_inv]
    _ ≤ (m : ℝ) ^ 10 / ((q : ℝ) * (m : ℝ) ^ 12) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hCard) (by positivity)
    _ = 1 / ((q : ℝ) * (m : ℝ) ^ 2) := by
      field_simp [hqR.ne', hmR.ne']

end Erdos319Sharp
