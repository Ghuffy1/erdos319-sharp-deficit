import Erdos319Sharp.PrimeBand

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem primeFactors_card_log_bound {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have hProduct : 2 ^ q.primeFactors.card ≤ q.primeFactors.prod id :=
    Finset.pow_card_le_prod q.primeFactors id 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hBound : 2 ^ q.primeFactors.card ≤ q :=
    hProduct.trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
  have hBoundR : (2 : ℝ) ^ q.primeFactors.card ≤ q := by exact_mod_cast hBound
  have hLog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ q.primeFactors.card) hBoundR
  simpa only [Real.log_pow] using hLog

/-- There are enough primes for the correction pool after every prime factor
of the modulus has been excluded. -/
theorem eventually_prime_pool_for_log_bound :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℕ, 0 < q → Real.log q ≤ (m : ℝ) + 1 →
      ∃ M : Finset ℕ, M.card = m ^ 10 ∧
        ∀ p ∈ M, p.Prime ∧ m ^ 12 < p ∧ p ≤ m ^ 13 ∧ ¬ p ∣ q := by
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hSize : ∀ᶠ m : ℕ in atTop, 2 / Real.log 2 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 / Real.log 2))
  filter_upwards [eventually_primeInterval_thinning, hSize, eventually_ge_atTop (1 : ℕ)]
    with m hThin hm hm1 q hq hLogq
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hTwo : 2 ≤ (m : ℝ) * Real.log 2 := (div_le_iff₀ hLogTwo).mp hm
  have hMul := mul_le_mul_of_nonneg_left hTwo (by positivity : (0 : ℝ) ≤ m)
  have hCardProduct : (q.primeFactors.card : ℝ) * Real.log 2 ≤
      (m : ℝ) ^ 2 * Real.log 2 := by
    calc
      (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := primeFactors_card_log_bound hq
      _ ≤ (m : ℝ) + 1 := hLogq
      _ ≤ 2 * m := by linarith
      _ ≤ (m : ℝ) ^ 2 * Real.log 2 := by nlinarith only [hMul]
  have hCardR : (q.primeFactors.card : ℝ) ≤ (m : ℝ) ^ 2 :=
    (mul_le_mul_iff_left₀ hLogTwo).mp (by simpa only [mul_comm] using hCardProduct)
  have hCard : q.primeFactors.card ≤ m ^ 11 := by
    have hPower : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 11 := pow_le_pow_right₀ hmR (by norm_num)
    exact_mod_cast hCardR.trans hPower
  obtain ⟨M, hM, hSizeM, hDisjoint⟩ := hThin q.primeFactors hCard
  refine ⟨M, hSizeM, ?_⟩
  intro p hp
  obtain ⟨hPrime, hLower, hUpper⟩ := mem_primeInterval.mp (hM hp)
  refine ⟨hPrime, hLower, hUpper, ?_⟩
  intro hDiv
  exact Finset.disjoint_left.mp hDisjoint hp (hPrime.mem_primeFactors hDiv hq.ne')

end Erdos319Sharp
