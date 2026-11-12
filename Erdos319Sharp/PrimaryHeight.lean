import Erdos319Sharp.ExcessWeights

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def primaryHeight (d : ℕ) : ℕ :=
  max 1 (d.factorization.support.sup (fun p => p ^ d.factorization p))

theorem one_le_primaryHeight (d : ℕ) : 1 ≤ primaryHeight d := le_max_left _ _

theorem primary_power_le_height (d p : ℕ) : p ^ d.factorization p ≤ primaryHeight d := by
  by_cases hZero : d.factorization p = 0
  · simpa only [hZero, pow_zero] using one_le_primaryHeight d
  · exact (Finset.le_sup (f := fun r => r ^ d.factorization r)
      (Finsupp.mem_support_iff.mpr hZero)).trans (le_max_right _ _)

theorem primaryHeight_mono_dvd (d D : ℕ) (hd : d ≠ 0) (hD : D ≠ 0) (hDiv : d ∣ D) :
    primaryHeight d ≤ primaryHeight D := by
  have hFactor := (Nat.factorization_le_iff_dvd hd hD).mpr hDiv
  apply max_le (one_le_primaryHeight D)
  apply Finset.sup_le
  intro p hp
  have hpPrime : p.Prime := by
    by_contra hNot
    exact (Finsupp.mem_support_iff.mp hp) (Nat.factorization_eq_zero_of_not_prime d hNot)
  exact (Nat.pow_le_pow_right hpPrime.one_le (hFactor p)).trans (primary_power_le_height D p)

theorem dvd_initial_lcm_of_primaryHeight_le (d L : ℕ) (hd : d ≠ 0)
    (hBound : primaryHeight d ≤ L) : d ∣ (Finset.Icc 1 L).lcm id := by
  have hLcm : (Finset.Icc 1 L).lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by
    intro n hn
    exact (show 0 < n from (Finset.mem_Icc.mp hn).1).ne')
  apply (Nat.factorization_le_iff_dvd hd hLcm).mp
  intro p
  by_cases hZero : d.factorization p = 0
  · simp [hZero]
  · have hp : p.Prime := by
      by_contra hNot
      exact hZero (Nat.factorization_eq_zero_of_not_prime d hNot)
    have hMem : p ^ d.factorization p ∈ Finset.Icc 1 L :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero),
        (primary_power_le_height d p).trans hBound⟩
    exact (hp.pow_dvd_iff_le_factorization hLcm).mp (Finset.dvd_lcm hMem)

theorem exists_prime_at_primaryHeight (d : ℕ) (hHeight : 1 < primaryHeight d) :
    ∃ p : ℕ, p.Prime ∧ 0 < d.factorization p ∧ primaryHeight d = p ^ d.factorization p := by
  have hSupport : d.factorization.support.Nonempty := by
    by_contra hEmpty
    have hEq : d.factorization.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    change 1 < max 1 (d.factorization.support.sup (fun p => p ^ d.factorization p)) at hHeight
    rw [hEq] at hHeight
    simp at hHeight
  obtain ⟨p, hp, hMax⟩ := Finset.exists_mem_eq_sup d.factorization.support hSupport
    (fun p => p ^ d.factorization p)
  have hpNonzero := Finsupp.mem_support_iff.mp hp
  have hpPrime : p.Prime := by
    by_contra hNot
    exact hpNonzero (Nat.factorization_eq_zero_of_not_prime d hNot)
  refine ⟨p, hpPrime, Nat.pos_of_ne_zero hpNonzero, ?_⟩
  unfold primaryHeight
  rw [hMax, max_eq_right]
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hpPrime.ne_zero)

theorem primaryHeight_ordCompl_lt (d p : ℕ) (hd : d ≠ 0) (hp : p.Prime)
    (hExponent : 0 < d.factorization p) (hMax : primaryHeight d = p ^ d.factorization p) :
    primaryHeight (ordCompl[p] d) < primaryHeight d := by
  have hTwo : 2 ≤ primaryHeight d := by
    rw [hMax]
    have hPow : p ^ 1 ≤ p ^ d.factorization p :=
      Nat.pow_le_pow_right hp.pos hExponent
    exact hp.two_le.trans (by simpa only [pow_one] using hPow)
  have hBound : primaryHeight (ordCompl[p] d) ≤ primaryHeight d - 1 := by
    apply max_le (by omega)
    apply Finset.sup_le
    intro r hr
    have hrPositive : 0 < (ordCompl[p] d).factorization r :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
    have hFactor := Nat.factorization_ordCompl d p
    have hrp : r ≠ p := by
      intro hEq
      subst r
      have hZero : (ordCompl[p] d).factorization p = 0 := by rw [hFactor]; simp
      omega
    have hAtR : (ordCompl[p] d).factorization r = d.factorization r := by
      rw [hFactor, Finsupp.erase_ne hrp]
    have hrPrime : r.Prime := by
      by_contra hNot
      have hZero := Nat.factorization_eq_zero_of_not_prime (ordCompl[p] d) hNot
      omega
    have hLe : r ^ (ordCompl[p] d).factorization r ≤ primaryHeight d := by
      rw [hAtR]
      exact primary_power_le_height d r
    have hNe : r ^ (ordCompl[p] d).factorization r ≠ primaryHeight d := by
      intro hEq
      have hDiv : r ∣ p ^ d.factorization p := by
        rw [← hMax, ← hEq]
        exact dvd_pow_self r hrPositive.ne'
      exact hrp ((Nat.prime_dvd_prime_iff_eq hrPrime hp).mp (hrPrime.dvd_of_dvd_pow hDiv))
    omega
  omega

theorem prime_product_factorization (M : Finset ℕ) (hPrime : ∀ p ∈ M, p.Prime) (r : ℕ) :
    (M.prod id).factorization r = if r ∈ M then 1 else 0 := by
  classical
  revert hPrime
  induction M using Finset.induction_on with
  | empty => intro hPrime; simp
  | @insert p M hpM ih =>
      intro hPrime
      have hp := hPrime p (Finset.mem_insert_self _ _)
      have hRest : ∀ q ∈ M, q.Prime := fun q hq => hPrime q (Finset.mem_insert_of_mem hq)
      have hNonzero : M.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr
        (fun q hq => (hRest q hq).ne_zero)
      rw [Finset.prod_insert hpM, id_eq, Nat.factorization_mul hp.ne_zero hNonzero,
        Finsupp.add_apply, hp.factorization, Finsupp.single_apply, ih hRest]
      by_cases hEq : r = p
      · subst r
        simp [hpM]
      · simp [hEq, Ne.symm hEq]

theorem primaryHeight_lcm_prime_product_lt (v q : ℕ) (M : Finset ℕ) (hv : v ≠ 0)
    (hHeight : primaryHeight v < q) (hPrime : ∀ p ∈ M, p.Prime)
    (hSmall : ∀ p ∈ M, p < q) : primaryHeight (v.lcm (M.prod id)) < q := by
  classical
  have hq : 2 ≤ q := by have := one_le_primaryHeight v; omega
  have hProduct : M.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p hp => (hPrime p hp).ne_zero)
  have hBound : primaryHeight (v.lcm (M.prod id)) ≤ q - 1 := by
    apply max_le (by omega)
    apply Finset.sup_le
    intro p hp
    have hFactor : (v.lcm (M.prod id)).factorization p =
        max (v.factorization p) (if p ∈ M then 1 else 0) := by
      rw [Nat.factorization_lcm hv hProduct, Finsupp.sup_apply, prime_product_factorization M hPrime]
    have hPower : p ^ (v.lcm (M.prod id)).factorization p < q := by
      rw [hFactor]
      by_cases hpM : p ∈ M
      · rw [if_pos hpM]
        by_cases hZero : v.factorization p = 0
        · simpa only [hZero, max_eq_right (by norm_num : (0 : ℕ) ≤ 1), pow_one] using hSmall p hpM
        · rw [max_eq_left (Nat.one_le_iff_ne_zero.mpr hZero)]
          exact (primary_power_le_height v p).trans_lt hHeight
      · rw [if_neg hpM, max_eq_left (Nat.zero_le _)]
        exact (primary_power_le_height v p).trans_lt hHeight
    omega
  omega

end Erdos319Sharp
