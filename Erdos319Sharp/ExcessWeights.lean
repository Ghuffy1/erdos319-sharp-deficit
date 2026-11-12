import Erdos319Sharp.PrimePowerExcess
import Erdos319Sharp.MissingCofactors

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def excessWeight (D b : ℕ) : ℝ := (excessScale D b : ℝ)⁻¹

theorem excessScale_one (D : ℕ) (hD : D ≠ 0) : excessScale D 1 = 1 := by
  apply Nat.eq_of_factorization_eq (excessScale_ne_zero D 1 hD one_ne_zero) one_ne_zero
  intro p
  rw [excessScale_factorization D 1 p hD one_ne_zero]
  by_cases hp : p ∣ 1
  · have hpOne : p = 1 := Nat.dvd_one.mp hp
    simp [hpOne]
  · simp [hp]

theorem excessScale_ge (D b : ℕ) (hD : D ≠ 0) : b ≤ excessScale D b := by
  have hQuotient : 0 < D / coprimeCore D b :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (coprimeCore_dvd D b))
      (Nat.pos_of_ne_zero (coprimeCore_ne_zero D b hD))
  exact Nat.le_mul_of_pos_right b hQuotient

theorem excessScale_mul (D m n : ℕ) (hD : D ≠ 0) (hCop : m.Coprime n) :
    excessScale D (m * n) = excessScale D m * excessScale D n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [excessScale]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [excessScale]
  apply Nat.eq_of_factorization_eq (excessScale_ne_zero D (m * n) hD (Nat.mul_ne_zero hm hn))
    (Nat.mul_ne_zero (excessScale_ne_zero D m hD hm) (excessScale_ne_zero D n hD hn))
  intro p
  rw [excessScale_factorization D (m * n) p hD (Nat.mul_ne_zero hm hn),
    Nat.factorization_mul (excessScale_ne_zero D m hD hm) (excessScale_ne_zero D n hD hn)]
  change (m * n).factorization p + (if p ∣ m * n then D.factorization p else 0) =
    (excessScale D m).factorization p + (excessScale D n).factorization p
  rw [excessScale_factorization D m p hD hm, excessScale_factorization D n p hD hn,
    Nat.factorization_mul hm hn]
  change m.factorization p + n.factorization p + (if p ∣ m * n then D.factorization p else 0) = _
  by_cases hp : p.Prime
  · by_cases hpm : p ∣ m
    · have hpn : ¬p ∣ n := hp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpm hCop)
      simp only [hp.dvd_mul, hpm, true_or, ite_true, hpn, ite_false]
      omega
    · by_cases hpn : p ∣ n
      · simp only [hp.dvd_mul, hpm, false_or, hpn, ite_true, ite_false]
        omega
      · simp only [hp.dvd_mul, hpm, false_or, hpn, ite_false]
        omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem excessWeight_zero (D : ℕ) : excessWeight D 0 = 0 := by
  simp [excessWeight, excessScale]

theorem excessWeight_one (D : ℕ) (hD : D ≠ 0) : excessWeight D 1 = 1 := by
  simp [excessWeight, excessScale_one D hD]

theorem excessWeight_nonneg (D b : ℕ) : 0 ≤ excessWeight D b :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

theorem excessWeight_le_inv (D b : ℕ) (hD : D ≠ 0) : excessWeight D b ≤ (b : ℝ)⁻¹ := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [excessWeight_zero]
  exact inv_anti₀ (by exact_mod_cast Nat.pos_of_ne_zero hb)
    (by exact_mod_cast excessScale_ge D b hD)

theorem excessWeight_mul (D m n : ℕ) (hD : D ≠ 0) (hCop : m.Coprime n) :
    excessWeight D (m * n) = excessWeight D m * excessWeight D n := by
  unfold excessWeight
  rw [excessScale_mul D m n hD hCop, Nat.cast_mul, mul_inv_rev]
  ring

theorem excessWeight_prime_pow_succ (D p k : ℕ) (hD : D ≠ 0) (hp : p.Prime) :
    excessWeight D (p ^ (k + 1)) =
      (firstMissingPower D p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ k := by
  rw [excessWeight, excessScale_prime_pow D p (k + 1) hD hp (Nat.succ_pos k)]
  rw [show D.factorization p + (k + 1) = (D.factorization p + 1) + k by omega, pow_add]
  simp only [Nat.cast_mul, Nat.cast_pow, mul_inv_rev, inv_pow, firstMissingPower]
  ring

end Erdos319Sharp
