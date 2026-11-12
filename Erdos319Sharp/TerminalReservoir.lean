import Erdos319Sharp.UnitReservoir

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem exists_nat_numerator_of_den_dvd (r : ℚ) (D : ℕ) (hD : 0 < D)
    (hDen : r.den ∣ D) (hr : 0 ≤ r) : ∃ m : ℕ, r = (m : ℚ) / D := by
  obtain ⟨z, hz⟩ := exists_integer_numerator_over_common r D hD.ne' hDen
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hzQ : (0 : ℚ) ≤ z := by
    have h := mul_nonneg hr hDQ.le
    rw [hz, div_mul_cancel₀ _ hDQ.ne'] at h
    exact h
  have hzNonneg : 0 ≤ z := by exact_mod_cast hzQ
  have hCast : (z.toNat : ℚ) = z := by exact_mod_cast Int.toNat_of_nonneg hzNonneg
  exact ⟨z.toNat, by rw [hCast]; exact hz⟩

theorem exists_terminal_reservoir (D L : ℕ) (hD : 0 < D) :
    ∃ R : Finset ℕ, (∀ n ∈ R, L < n ∧ 30 ∣ n ∧ D ∣ n) ∧
      ∀ r : ℚ, 0 ≤ r → r ≤ 2 → r.den ∣ D → ∃ A ⊆ R, reciprocalSum A = r := by
  obtain ⟨R, hR, hRepresent⟩ := exists_bounded_fraction_reservoir D 30 (2 * D) L hD (by norm_num)
  refine ⟨R, hR, ?_⟩
  intro r hr hrTwo hDen
  obtain ⟨m, hm⟩ := exists_nat_numerator_of_den_dvd r D hD hDen hr
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hmBound : m ≤ 2 * D := by
    have h : (m : ℚ) ≤ 2 * D := (div_le_iff₀ hDQ).mp (hm ▸ hrTwo)
    exact_mod_cast h
  obtain ⟨A, hAR, hSum⟩ := hRepresent m hmBound
  exact ⟨A, hAR, hSum.trans hm.symm⟩

end Erdos319Sharp
