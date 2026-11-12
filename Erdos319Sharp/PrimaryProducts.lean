import Erdos319Sharp.PrimaryHeight

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem primaryHeight_dvd (d : ℕ) : primaryHeight d ∣ d := by
  by_cases hSmall : primaryHeight d ≤ 1
  · have hOne : primaryHeight d = 1 := by have := one_le_primaryHeight d; omega
    rw [hOne]
    exact one_dvd d
  · obtain ⟨p, hp, hExponent, hHeight⟩ := exists_prime_at_primaryHeight d (by omega)
    rw [hHeight]
    exact Nat.ordProj_dvd d p

theorem primaryHeight_le_self (d : ℕ) (hd : d ≠ 0) : primaryHeight d ≤ d := by
  apply max_le (Nat.one_le_iff_ne_zero.mpr hd)
  exact Finset.sup_le (fun p _ => Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.ordProj_dvd d p))

theorem primaryHeight_prime_pow (p k : ℕ) (hp : p.Prime) : primaryHeight (p ^ k) = p ^ k := by
  apply le_antisymm (primaryHeight_le_self _ (pow_ne_zero _ hp.ne_zero))
  have h := primary_power_le_height (p ^ k) p
  simpa only [hp.factorization_pow, Finsupp.single_eq_same] using h

theorem primaryHeight_lcm (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    primaryHeight (a.lcm b) = max (primaryHeight a) (primaryHeight b) := by
  apply le_antisymm
  · apply max_le (by have := one_le_primaryHeight a; omega)
    apply Finset.sup_le
    intro p hp
    have hFactor : (a.lcm b).factorization p = max (a.factorization p) (b.factorization p) := by
      rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply]
    rw [hFactor]
    rcases le_total (a.factorization p) (b.factorization p) with h | h
    · rw [max_eq_right h]
      exact (primary_power_le_height b p).trans (le_max_right _ _)
    · rw [max_eq_left h]
      exact (primary_power_le_height a p).trans (le_max_left _ _)
  · apply max_le
    · exact primaryHeight_mono_dvd a (a.lcm b) ha (Nat.lcm_ne_zero ha hb) (Nat.dvd_lcm_left _ _)
    · exact primaryHeight_mono_dvd b (a.lcm b) hb (Nat.lcm_ne_zero ha hb) (Nat.dvd_lcm_right _ _)

theorem primaryHeight_coprime_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hCop : a.Coprime b) :
    primaryHeight (a * b) = max (primaryHeight a) (primaryHeight b) := by
  rw [← hCop.lcm_eq_mul, primaryHeight_lcm a b ha hb]

theorem primaryHeight_prime_power_mul_prime (p k b : ℕ) (hp : p.Prime) (hb : b.Prime)
    (hNot : ¬ b ∣ p ^ k) (hSmall : b < p ^ k) :
    primaryHeight (p ^ k * b) = p ^ k := by
  have hCop : (p ^ k).Coprime b := (hb.coprime_iff_not_dvd.mpr hNot).symm
  rw [primaryHeight_coprime_mul _ _ (pow_ne_zero _ hp.ne_zero) hb.ne_zero hCop,
    primaryHeight_prime_pow p k hp]
  have hB : primaryHeight b = b := by simpa using primaryHeight_prime_pow b 1 hb
  rw [hB, max_eq_left hSmall.le]

theorem not_thirty_dvd_prime_power_mul_prime (p k b : ℕ) (hp : p.Prime) (hb : b.Prime) :
    ¬ 30 ∣ p ^ k * b := by
  intro hDiv
  have hPrime : ∀ r : ℕ, r.Prime → r ∣ 30 → r = p ∨ r = b := by
    intro r hr hrThirty
    rcases hr.dvd_mul.mp (hrThirty.trans hDiv) with hPower | hB
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hPower))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hb).mp hB)
  have hTwo := hPrime 2 (by norm_num) (by norm_num)
  have hThree := hPrime 3 (by norm_num) (by norm_num)
  have hFive := hPrime 5 (by norm_num) (by norm_num)
  omega

end Erdos319Sharp
