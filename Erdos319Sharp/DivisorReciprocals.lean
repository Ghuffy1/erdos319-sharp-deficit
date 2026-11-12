import Erdos319Sharp.Baseline
import Erdos319Sharp.Mertens
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Field.GeomSum

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def divisorReciprocalMass (D : ℕ) : ℝ := (reciprocalSum D.divisors : ℝ)

theorem divisorReciprocalMass_mul (D : ℕ) (hD : D ≠ 0) :
    divisorReciprocalMass D * D = ∑ d ∈ D.divisors, (d : ℝ) := by
  unfold divisorReciprocalMass
  rw [reciprocalSum_eq_baseline, Erdos319Formal.reciprocalSum_real, Finset.sum_mul]
  calc
    (∑ d ∈ D.divisors, (1 / (d : ℝ)) * D) =
        ∑ d ∈ D.divisors, ((D / d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div_charZero (Nat.mem_divisors.mp hd).1]
      ring
    _ = ∑ d ∈ D.divisors, (d : ℝ) := Nat.sum_div_divisors D (fun d => (d : ℝ))

theorem geometric_divisor_factor (p k : ℕ) (hp : 1 < p) :
    (∑ i ∈ Finset.range (k + 1), (p : ℝ) ^ i) / (p : ℝ) ^ k =
      (1 - 1 / (p : ℝ) ^ (k + 1)) / (1 - 1 / (p : ℝ)) := by
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp
  have hpZero : (p : ℝ) ≠ 0 := (zero_lt_one.trans hpReal).ne'
  have hpOne : (p : ℝ) ≠ 1 := hpReal.ne'
  rw [geom_sum_eq hpOne (k + 1), pow_succ]
  field_simp [hpZero, hpOne, pow_ne_zero k hpZero]

theorem divisorReciprocalMass_product (D : ℕ) (hD : D ≠ 0) :
    divisorReciprocalMass D = ∏ p ∈ D.primeFactors,
      (1 - 1 / (p : ℝ) ^ (D.factorization p + 1)) / (1 - 1 / (p : ℝ)) := by
  have hDReal : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hNumerator : (∑ d ∈ D.divisors, (d : ℝ)) =
      ∏ p ∈ D.primeFactors, ∑ i ∈ Finset.range (D.factorization p + 1), (p : ℝ) ^ i := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.sum_divisors hD)
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using h
  have hDenominator : (D : ℝ) = ∏ p ∈ D.primeFactors, (p : ℝ) ^ D.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hD
  calc
    divisorReciprocalMass D = (∑ d ∈ D.divisors, (d : ℝ)) / D :=
      (eq_div_iff hDReal).mpr (divisorReciprocalMass_mul D hD)
    _ = ∏ p ∈ D.primeFactors,
        (∑ i ∈ Finset.range (D.factorization p + 1), (p : ℝ) ^ i) /
          (p : ℝ) ^ D.factorization p := by
      rw [hNumerator, hDenominator, Finset.prod_div_distrib]
    _ = _ := Finset.prod_congr rfl (fun p hp =>
      geometric_divisor_factor p (D.factorization p) (Nat.prime_of_mem_primeFactors hp).one_lt)

theorem lcm_divisorReciprocalMass_product (s : ℕ) :
    divisorReciprocalMass (Nat.lcmUpto s) =
      (∏ p ∈ s.primesLE, (1 - 1 / (p : ℝ) ^ (p.log s + 1))) * inversePrimeProduct s := by
  rw [divisorReciprocalMass_product _ (Nat.lcmUpto_ne_zero s), Nat.primeFactors_lcmUpto]
  have hFactor : ∀ p ∈ s.primesLE,
      (Nat.lcmUpto s).factorization p = p.log s :=
    fun p hp => Nat.factorization_lcmUpto s (Nat.prime_of_mem_primesLE hp)
  trans ∏ p ∈ s.primesLE, (1 - 1 / (p : ℝ) ^ (p.log s + 1)) / (1 - 1 / (p : ℝ))
  · exact Finset.prod_congr rfl (fun p hp => by rw [hFactor p hp])
  rw [Finset.prod_div_distrib]
  have hPrimes : s.primesLE = (Finset.range (s + 1)).filter Nat.Prime :=
    Nat.primesLE_eq_filter_range s
  rw [hPrimes]
  rfl

end Erdos319Sharp
