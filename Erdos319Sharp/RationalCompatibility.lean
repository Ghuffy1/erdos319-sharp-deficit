import Erdos319Sharp.ResidueCorrection

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem den_dvd_iff_scaled_den_one (r : ℚ) (D : ℕ) (hD : D ≠ 0) :
    r.den ∣ D ↔ ((D : ℚ) * r).den = 1 := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  constructor
  · intro hDen
    obtain ⟨z, hz⟩ := exists_integer_numerator_over_common r D hD hDen
    rw [hz]
    have hCancel : (D : ℚ) * ((z : ℚ) / D) = (z : ℚ) := by field_simp
    rw [hCancel]
    simp
  · intro hOne
    have hNum := ((D : ℚ) * r).num_div_den
    rw [hOne, Nat.cast_one, div_one] at hNum
    have hr : r = ((((D : ℚ) * r).num : ℤ) : ℚ) / D := by
      apply (eq_div_iff hDq).mpr
      simpa only [mul_comm] using hNum.symm
    rw [hr]
    exact int_quotient_den_dvd _ D

theorem reciprocal_empty_den_dvd (D : ℕ) : (reciprocalSum ∅).den ∣ D := by
  simp [reciprocalSum]

theorem reciprocal_union_den_dvd (A B : Finset ℕ) (D : ℕ) (hDisjoint : Disjoint A B)
    (hA : (reciprocalSum A).den ∣ D) (hB : (reciprocalSum B).den ∣ D) :
    (reciprocalSum (A ∪ B)).den ∣ D := by
  have hSum : reciprocalSum (A ∪ B) = reciprocalSum A + reciprocalSum B :=
    Finset.sum_union hDisjoint
  rw [hSum]
  exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd hA hB)

theorem inverse_sum_zero_iff_cofactor_sum_dvd (M : Finset ℕ) (D b : ℕ)
    (hCop : D.Coprime b) (hDiv : ∀ m ∈ M, m ∣ D) :
    (∑ m ∈ M, (m : ZMod b)⁻¹) = 0 ↔ b ∣ ∑ m ∈ M, D / m := by
  have hScaled := scaled_inverse_sum M D b hCop hDiv
  rw [← ZMod.natCast_eq_zero_iff]
  constructor
  · intro hZero
    rw [← hScaled, hZero, mul_zero]
  · intro hZero
    have h := congrArg (fun z : ZMod b => (D : ZMod b)⁻¹ * z) hScaled
    rw [hZero, mul_zero] at h
    have hUnit : (D : ZMod b)⁻¹ * D = 1 := by
      rw [mul_comm, ZMod.coe_mul_inv_eq_one D hCop]
    simpa only [← mul_assoc, hUnit, one_mul] using h

theorem scaled_cofactor_compatibility_iff (M : Finset ℕ) (s D b : ℕ)
    (hs : 0 < s) (hD : D ≠ 0) (hb : 0 < b) (hCop : D.Coprime b)
    (hDiv : ∀ m ∈ M, m ∣ D) :
    (reciprocalSum (M.image (fun m => (b * s) * m))).den ∣ s * D ↔
      (∑ m ∈ M, (m : ZMod b)⁻¹) = 0 := by
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hScaled : ((s * D : ℕ) : ℚ) * reciprocalSum (M.image (fun m => (b * s) * m)) =
      ((∑ m ∈ M, D / m : ℕ) : ℚ) / b := by
    rw [reciprocalSum_mul_image M (b * s) (Nat.mul_pos hb hs)]
    calc
      _ = (D : ℚ) * reciprocalSum M / b := by
        push_cast
        field_simp [hsQ, hbQ] <;> ring
      _ = ((∑ m ∈ M, D / m : ℕ) : ℚ) / b := by
        rw [← sum_cofactor_eq_scaled_reciprocal M D hDiv]
  rw [den_dvd_iff_scaled_den_one _ (s * D) (Nat.mul_ne_zero hs.ne' hD), hScaled,
    Rat.den_div_natCast_eq_one_iff _ b hb.ne']
  exact (inverse_sum_zero_iff_cofactor_sum_dvd M D b hCop hDiv).symm

end Erdos319Sharp
