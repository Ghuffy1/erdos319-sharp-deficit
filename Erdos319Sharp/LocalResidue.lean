import Erdos319Sharp.ReciprocalResidues

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem cofactor_cast_eq_local_inverse (p D n : ℕ) (hp : p.Prime)
    (hCoprime : D.Coprime p) (hDiv : n ∣ p * D) :
    (((p * D) / n : ℕ) : ZMod p) =
      if p ∣ n then (D : ZMod p) * ((n / p : ℕ) : ZMod p)⁻¹ else 0 := by
  classical
  by_cases hpn : p ∣ n
  · obtain ⟨v, rfl⟩ := hpn
    have hvDiv : v ∣ D := (Nat.mul_dvd_mul_iff_left hp.pos).mp hDiv
    have hScaled := scaled_inverse_sum ({v} : Finset ℕ) D p hCoprime (by
      intro x hx
      rcases Finset.mem_singleton.mp hx with rfl
      exact hvDiv)
    rw [if_pos (dvd_mul_right p v), Nat.mul_div_mul_left D v hp.pos,
      Nat.mul_div_cancel_left v hp.pos]
    simpa only [Finset.sum_singleton] using hScaled.symm
  · have hnCop : n.Coprime p := (hp.coprime_iff_not_dvd.mpr hpn).symm
    have hnD : n ∣ D := hnCop.dvd_mul_left.mp hDiv
    rw [if_neg hpn, Nat.mul_div_assoc p hnD, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem cofactor_sum_eq_local_inverse_sum (A : Finset ℕ) (p D : ℕ) (hp : p.Prime)
    (hCoprime : D.Coprime p) (hDiv : ∀ n ∈ A, n ∣ p * D) :
    ((∑ n ∈ A, (p * D) / n : ℕ) : ZMod p) =
      (D : ZMod p) * ∑ n ∈ A.filter (fun n => p ∣ n), ((n / p : ℕ) : ZMod p)⁻¹ := by
  rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun n hn => cofactor_cast_eq_local_inverse p D n hp hCoprime (hDiv n hn))

theorem local_inverse_sum_zero_of_integral (A : Finset ℕ) (G p D : ℕ) (hp : p.Prime)
    (hpG : p ∣ G) (hCoprime : D.Coprime p) (hDiv : ∀ n ∈ A, n ∣ p * D)
    (hIntegral : DIntegral G (reciprocalSum A)) :
    (∑ n ∈ A.filter (fun n => p ∣ n), ((n / p : ℕ) : ZMod p)⁻¹) = 0 := by
  have hClear : ((p * D : ℕ) : ℚ) * reciprocalSum A = ((∑ n ∈ A, (p * D) / n : ℕ) : ℚ) :=
    (sum_cofactor_eq_scaled_reciprocal A (p * D) hDiv).symm
  have hDivSum := dvd_cleared_numerator hpG (dvd_mul_right p D) hIntegral hClear
  have hZero : ((∑ n ∈ A, (p * D) / n : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hDivSum
  rw [cofactor_sum_eq_local_inverse_sum A p D hp hCoprime hDiv] at hZero
  have hCancel := congrArg (fun x : ZMod p => (D : ZMod p)⁻¹ * x) hZero
  have hUnit : (D : ZMod p)⁻¹ * D = 1 := by
    rw [mul_comm, ZMod.coe_mul_inv_eq_one D hCoprime]
  simpa only [← mul_assoc, hUnit, one_mul, mul_zero] using hCancel

theorem integral_of_cofactor_divisibility (A : Finset ℕ) (G D : ℕ)
    (hG : 0 < G) (hD : 0 < D) (hCoprime : D.Coprime G)
    (hDiv : ∀ n ∈ A, n ∣ G * D) (hTotal : G ∣ ∑ n ∈ A, (G * D) / n) :
    DIntegral G (reciprocalSum A) := by
  obtain ⟨z, hz⟩ := hTotal
  have hGQ : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne'
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hClear := sum_cofactor_eq_scaled_reciprocal A (G * D) hDiv
  have hFraction : reciprocalSum A = ((∑ n ∈ A, (G * D) / n : ℕ) : ℚ) / (G * D) := by
    apply (eq_div_iff (mul_ne_zero hGQ hDQ)).mpr
    simpa only [Nat.cast_mul, mul_comm] using hClear.symm
  rw [hFraction, hz, Nat.cast_mul]
  have hCancel : ((G : ℚ) * z) / ((G : ℚ) * D) = (z : ℚ) / D := by field_simp
  rw [hCancel]
  exact dIntegral_div_nat hCoprime

end Erdos319Sharp
