import Erdos319Sharp.PrimeFiber

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem int_quotient_den_dvd (z : ℤ) (D : ℕ) : ((z : ℚ) / D).den ∣ D := by
  have h := Rat.den_dvd z (D : ℤ)
  simp only [Rat.divInt_eq_div, Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

theorem exists_integer_numerator_over_common (r : ℚ) (D : ℕ) (hD : D ≠ 0)
    (hDen : r.den ∣ D) : ∃ z : ℤ, r = (z : ℚ) / D := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  refine ⟨r.num * (D / r.den : ℕ), ?_⟩
  calc
    r = (r.num : ℚ) / r.den := r.num_div_den.symm
    _ = ((r.num * (D / r.den : ℕ) : ℤ) : ℚ) / D := by
      simp only [Int.cast_mul, Int.cast_natCast]
      rw [Nat.cast_div_charZero hDen]
      field_simp [hDq, hden]

theorem reciprocalSum_mul_image (B : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    reciprocalSum (B.image (fun n => p * n)) = reciprocalSum B / p := by
  classical
  unfold reciprocalSum
  rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp hab),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.cast_mul, div_eq_mul_inv, one_mul, mul_inv_rev]

theorem cancel_modular_denominator (B : Finset ℕ) (D p : ℕ) (z : ℤ)
    (hD : D ≠ 0) (hp : 0 < p) (hCop : D.Coprime p)
    (hDiv : ∀ n ∈ B, n ∣ D)
    (hResidue : (D : ZMod p) * (∑ n ∈ B, (n : ZMod p)⁻¹) = (z : ZMod p)) :
    (((z : ℚ) / (p * D) - reciprocalSum (B.image (fun n => p * n)))).den ∣ D := by
  let s : ℕ := ∑ n ∈ B, D / n
  have hScaled : (D : ZMod p) * (∑ n ∈ B, (n : ZMod p)⁻¹) = (s : ZMod p) :=
    scaled_inverse_sum B D p hCop hDiv
  have hZero : ((z - (s : ℤ) : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [← hScaled, hResidue, sub_self]
  obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - (s : ℤ)) p).mp hZero
  have hwq : (z : ℚ) - s = (p : ℚ) * w := by exact_mod_cast hw
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hSum : reciprocalSum B = (s : ℚ) / D := by
    apply (eq_div_iff hDq).mpr
    simpa only [mul_comm] using (sum_cofactor_eq_scaled_reciprocal B D hDiv).symm
  have hEquality : (z : ℚ) / (p * D) - reciprocalSum (B.image (fun n => p * n)) =
      (w : ℚ) / D := by
    rw [reciprocalSum_mul_image B p hp, hSum]
    calc
      _ = ((z : ℚ) - s) / ((p : ℚ) * D) := by field_simp
      _ = (w : ℚ) / D := by rw [hwq]; field_simp [hpq, hDq]
  rw [hEquality]
  exact int_quotient_den_dvd w D

theorem exists_modular_correction (A M : Finset ℕ) (D p u bound : ℕ)
    (hD : D ≠ 0) (hp : 0 < p) (hCop : D.Coprime p)
    (hu : 0 < u) (huCop : u.Coprime p)
    (hM : ∀ q ∈ M, p * (u * q) ∈ A ∧ u * q ∣ D)
    (hCover : ∀ x : ZMod p, ∃ K ⊆ M, K.card ≤ bound ∧ ∑ q ∈ K, (q : ZMod p)⁻¹ = x)
    (r : ℚ) (hDen : r.den ∣ p * D) :
    ∃ T ⊆ A, T.card ≤ bound ∧ (∀ n ∈ T, p ∣ n) ∧ (r - reciprocalSum T).den ∣ D := by
  classical
  obtain ⟨z, hz⟩ := exists_integer_numerator_over_common r (p * D)
    (Nat.mul_ne_zero hp.ne' hD) hDen
  obtain ⟨K, hKM, hKCard, hKSum⟩ := hCover ((u : ZMod p) * (D : ZMod p)⁻¹ * z)
  let B := K.image (fun q => u * q)
  let T := B.image (fun n => p * n)
  have hBDiv : ∀ n ∈ B, n ∣ D := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    exact (hM q (hKM hq)).2
  have hQCoprime : ∀ q ∈ K, q.Coprime p := by
    intro q hq
    exact Nat.Coprime.of_dvd_left
      ((dvd_mul_left q u).trans (hM q (hKM hq)).2) hCop
  have hInv : (∑ n ∈ B, (n : ZMod p)⁻¹) = (D : ZMod p)⁻¹ * z := by
    calc
      _ = (u : ZMod p)⁻¹ * ∑ q ∈ K, (q : ZMod p)⁻¹ := by
        rw [Finset.mul_sum]
        dsimp [B]
        rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hu hab)]
        exact Finset.sum_congr rfl (fun q hq =>
          inverse_nat_mul_of_coprime u q p huCop (hQCoprime q hq))
      _ = (u : ZMod p)⁻¹ * ((u : ZMod p) * (D : ZMod p)⁻¹ * z) := by rw [hKSum]
      _ = ((u : ZMod p)⁻¹ * u) * ((D : ZMod p)⁻¹ * z) := by ring
      _ = (D : ZMod p)⁻¹ * z := by
        rw [mul_comm (u : ZMod p)⁻¹ (u : ZMod p), ZMod.coe_mul_inv_eq_one u huCop, one_mul]
  have hResidue : (D : ZMod p) * (∑ n ∈ B, (n : ZMod p)⁻¹) = (z : ZMod p) := by
    rw [hInv, ← mul_assoc, ZMod.coe_mul_inv_eq_one D hCop, one_mul]
  refine ⟨T, ?_, (Finset.card_image_le.trans Finset.card_image_le).trans hKCard, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    exact (hM q (hKM hq)).1
  · intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact dvd_mul_right p m
  · rw [hz]
    simpa only [Nat.cast_mul] using
      cancel_modular_denominator B D p z hD hp hCop hBDiv hResidue

end Erdos319Sharp
