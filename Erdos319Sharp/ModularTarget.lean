import Erdos319Sharp.ReciprocalResidues

set_option autoImplicit false

noncomputable section

namespace Erdos319Sharp

theorem nat_quotient_den_dvd (x D : ℕ) : ((x : ℚ) / D).den ∣ D := by
  have h := Rat.den_dvd (x : ℤ) (D : ℤ)
  simp only [Rat.divInt_eq_div, Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

/-- A sufficiently fine rational lattice meets the exact-target interval. -/
theorem exists_positive_modular_target (q D : ℕ) (β : ℝ)
    (hq : 0 < q) (hD : 0 < D) (hβ : 0 < β)
    (hMesh : (q : ℝ) / D ≤ β / 8) :
    ∃ x : ℕ, 0 < x ∧ q ∣ x ∧ β / 8 ≤ (((x : ℚ) / D : ℚ) : ℝ) ∧
      (((x : ℚ) / D : ℚ) : ℝ) ≤ β / 4 := by
  let δ : ℝ := (q : ℝ) / D
  have hδ : 0 < δ := div_pos (by exact_mod_cast hq) (by exact_mod_cast hD)
  let k : ℕ := ⌈(β / 8) / δ⌉₊
  have ht : 0 < (β / 8) / δ := div_pos (by positivity) hδ
  have hkPos : 0 < k := Nat.one_le_ceil_iff.mpr ht
  have hkLo : (β / 8) / δ ≤ (k : ℝ) := Nat.le_ceil _
  have hkHi : (k : ℝ) < (β / 8) / δ + 1 := Nat.ceil_lt_add_one ht.le
  have hLo : β / 8 ≤ (k : ℝ) * δ := (div_le_iff₀ hδ).mp hkLo
  have hHi : (k : ℝ) * δ < β / 8 + δ := by
    have h := mul_lt_mul_of_pos_right hkHi hδ
    simpa only [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] using h
  have hCast : ((((q * k : ℕ) : ℚ) / D : ℚ) : ℝ) = (k : ℝ) * δ := by
    push_cast
    dsimp [δ]
    ring
  refine ⟨q * k, Nat.mul_pos hq hkPos, dvd_mul_right q k, ?_, ?_⟩
  · rwa [hCast]
  · rw [hCast]
    change δ ≤ β / 8 at hMesh
    linarith

end Erdos319Sharp
