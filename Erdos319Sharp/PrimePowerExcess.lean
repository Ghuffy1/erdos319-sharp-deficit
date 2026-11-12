import Erdos319Sharp.DenominatorExcess

set_option autoImplicit false

noncomputable section

namespace Erdos319Sharp

theorem excessScale_prime_pow (D p k : ℕ) (hD : D ≠ 0) (hp : p.Prime) (hk : 0 < k) :
    excessScale D (p ^ k) = p ^ (D.factorization p + k) := by
  apply Nat.eq_of_factorization_eq
    (excessScale_ne_zero D (p ^ k) hD (pow_ne_zero k hp.ne_zero))
    (pow_ne_zero _ hp.ne_zero)
  intro q
  rw [excessScale_factorization D (p ^ k) q hD (pow_ne_zero k hp.ne_zero)]
  by_cases hqp : q = p
  · subst q
    simp only [hp.factorization_pow, Finsupp.single_eq_same,
      dvd_pow_self p hk.ne', ite_true]
    omega
  · by_cases hq : q.Prime
    · have hNotDiv : ¬q ∣ p ^ k := by
        intro hDiv
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hDiv))
      simp [hp.factorization_pow, Finsupp.single_eq_of_ne hqp, hNotDiv]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

theorem excess_prime_pow_valuation (D n p k : ℕ) (hD : D ≠ 0) (hn : n ≠ 0)
    (hp : p.Prime) (hk : 0 < k) (hExcess : denominatorExcess D n = p ^ k) :
    n.factorization p = D.factorization p + k := by
  simpa only [hp.factorization_pow, Finsupp.single_eq_same] using
    factorization_eq_add_of_dvd_excess D n (p ^ k) p hD hn hExcess hp (dvd_pow_self p hk.ne')

theorem excess_prime_pow_other_valuation (D n p q k : ℕ) (hD : D ≠ 0) (hn : n ≠ 0)
    (hp : p.Prime) (hqp : q ≠ p) (hExcess : denominatorExcess D n = p ^ k) :
    n.factorization q ≤ D.factorization q := by
  have hExponent := congrArg (fun f : ℕ →₀ ℕ => f q) (denominatorExcess_factorization D n hD hn)
  rw [hExcess, hp.factorization_pow, Finsupp.single_eq_of_ne hqp] at hExponent
  change 0 = n.factorization q - D.factorization q at hExponent
  omega

end Erdos319Sharp
