import Erdos319Sharp.ZeroSum
import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem sum_cofactor_eq_scaled_reciprocal (A : Finset ℕ) (D : ℕ)
    (hDiv : ∀ n ∈ A, n ∣ D) :
    ((∑ n ∈ A, D / n : ℕ) : ℚ) = (D : ℚ) * reciprocalSum A := by
  rw [Nat.cast_sum, reciprocalSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.cast_div_charZero (hDiv n hn), div_eq_mul_inv]

theorem sum_cofactor_eq_numerator (A : Finset ℕ) (D x : ℕ) (hD : 0 < D)
    (hDiv : ∀ n ∈ A, n ∣ D) (hSum : reciprocalSum A = (x : ℚ) / D) :
    (∑ n ∈ A, D / n) = x := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have h := sum_cofactor_eq_scaled_reciprocal A D hDiv
  rw [hSum] at h
  have hCancel : (D : ℚ) * ((x : ℚ) / D) = x := by field_simp [hDq]
  rw [hCancel] at h
  exact_mod_cast h

theorem scaled_inverse_sum (A : Finset ℕ) (D q : ℕ) (hCop : D.Coprime q)
    (hDiv : ∀ n ∈ A, n ∣ D) :
    (D : ZMod q) * (∑ n ∈ A, (n : ZMod q)⁻¹) = ((∑ n ∈ A, D / n : ℕ) : ZMod q) := by
  rw [Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnCop : n.Coprime q := Nat.Coprime.of_dvd_left (hDiv n hn) hCop
  have hFactor : ((D / n : ℕ) : ZMod q) * (n : ZMod q) = (D : ZMod q) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun k : ℕ => (k : ZMod q)) (Nat.div_mul_cancel (hDiv n hn))
  calc
    (D : ZMod q) * (n : ZMod q)⁻¹ =
        (((D / n : ℕ) : ZMod q) * (n : ZMod q)) * (n : ZMod q)⁻¹ := by rw [hFactor]
    _ = ((D / n : ℕ) : ZMod q) * ((n : ZMod q) * (n : ZMod q)⁻¹) := mul_assoc _ _ _
    _ = ((D / n : ℕ) : ZMod q) := by rw [ZMod.coe_mul_inv_eq_one n hnCop, mul_one]

theorem inverse_sum_zero_of_rational_target (A : Finset ℕ) (D q x : ℕ)
    (hD : 0 < D) (hCop : D.Coprime q) (hDiv : ∀ n ∈ A, n ∣ D)
    (hSum : reciprocalSum A = (x : ℚ) / D) (hqx : q ∣ x) :
    (∑ n ∈ A, (n : ZMod q)⁻¹) = 0 := by
  have hScaled := scaled_inverse_sum A D q hCop hDiv
  rw [sum_cofactor_eq_numerator A D x hD hDiv hSum,
    (ZMod.natCast_eq_zero_iff x q).mpr hqx] at hScaled
  have hUnit : (D : ZMod q)⁻¹ * (D : ZMod q) = 1 := by
    simpa only [mul_comm] using ZMod.coe_mul_inv_eq_one D hCop
  calc
    (∑ n ∈ A, (n : ZMod q)⁻¹) = 1 * (∑ n ∈ A, (n : ZMod q)⁻¹) := (one_mul _).symm
    _ = ((D : ZMod q)⁻¹ * (D : ZMod q)) * (∑ n ∈ A, (n : ZMod q)⁻¹) := by rw [hUnit]
    _ = (D : ZMod q)⁻¹ * ((D : ZMod q) * (∑ n ∈ A, (n : ZMod q)⁻¹)) := mul_assoc _ _ _
    _ = 0 := by rw [hScaled, mul_zero]

theorem lcm_coprime_of_members (A : Finset ℕ) (q : ℕ)
    (hCop : ∀ n ∈ A, n.Coprime q) : (A.lcm id).Coprime q := by
  apply Nat.Coprime.of_dvd_left (Finset.lcm_dvd_prod A id)
  exact Nat.coprime_prod_left_iff.mpr hCop

theorem InverseZeroSumFree.no_rational_target {A F : Finset ℕ} {q D x : ℕ}
    (hFree : InverseZeroSumFree q A) (hF : F ⊆ A) (hFne : F.Nonempty)
    (hD : 0 < D) (hCop : D.Coprime q) (hDiv : ∀ n ∈ F, n ∣ D)
    (hSum : reciprocalSum F = (x : ℚ) / D) (hqx : q ∣ x) : False :=
  hFree F hF hFne (inverse_sum_zero_of_rational_target F D q x hD hCop hDiv hSum hqx)

end Erdos319Sharp
