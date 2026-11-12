import Erdos319Sharp.RationalCompatibility
import Erdos319Sharp.ZeroSumBlocks
import Erdos319Sharp.Peeling
import Erdos319Sharp.OppositeSignTarget

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem small_inverse_zero_compatible_block (M : Finset ℕ) (s D b : ℕ)
    (hs : 0 < s) (hD : D ≠ 0) (hb : 0 < b) (hCop : D.Coprime b)
    (hDiv : ∀ m ∈ M, m ∣ D) (hNotFree : ¬InverseZeroSumFree b M) :
    ∃ K ⊆ M, K.Nonempty ∧ K.card ≤ b ∧
      (reciprocalSum (K.image (fun m => (b * s) * m))).den ∣ s * D ∧
      reciprocalSum (K.image (fun m => (b * s) * m)) ≤ 1 := by
  classical
  have hPos : ∀ m ∈ M, 0 < m := by
    intro m hm
    apply Nat.pos_of_ne_zero
    intro hZero
    have h := hDiv m hm
    rw [hZero, zero_dvd_iff] at h
    exact hD h
  obtain ⟨K, hKM, hKne, hKSum, hKCard⟩ :=
    exists_small_zero_subset_of_not_free b hb M (fun m => (m : ZMod b)⁻¹) hPos hNotFree
  have hMass : reciprocalSum K ≤ (K.card : ℚ) := by
    calc
      reciprocalSum K ≤ ∑ _m ∈ K, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro m hm
        simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℚ) < 1)
          (by exact_mod_cast hPos m (hKM hm) : (1 : ℚ) ≤ m)
      _ = (K.card : ℚ) := by simp
  have hQ : (0 : ℚ) < (b * s : ℕ) := by exact_mod_cast Nat.mul_pos hb hs
  have hKQ : (K.card : ℚ) ≤ (b * s : ℕ) := by
    exact_mod_cast hKCard.trans (Nat.le_mul_of_pos_right b hs)
  refine ⟨K, hKM, hKne, hKCard,
    (scaled_cofactor_compatibility_iff K s D b hs hD hb hCop (fun m hm => hDiv m (hKM hm))).mpr hKSum, ?_⟩
  rw [reciprocalSum_mul_image K (b * s) (Nat.mul_pos hb hs)]
  exact (div_le_div_of_nonneg_right hMass hQ.le).trans ((div_le_one hQ).mpr hKQ)

theorem IsPrimitiveSigning.exists_compatible_removal {A : Finset ℕ} {δ : ℕ → ℤˣ}
    (hPrimitive : IsPrimitiveSigning A δ) (D : ℕ) (η : ℝ) (hη : 0 < η)
    (hMass : η + 1 ≤ (reciprocalSum (positivePart A δ) : ℝ))
    (hRepresent : ∀ r : ℚ, r.den ∣ D → η ≤ (r : ℝ) → (r : ℝ) < η + 1 →
      ∃ U ⊆ negativePart A δ, reciprocalSum U = r) :
    ∃ P ⊆ positivePart A δ, (reciprocalSum P).den ∣ D ∧ (reciprocalSum P : ℝ) < η ∧
      ∀ T ⊆ positivePart A δ \ P, T.Nonempty → (reciprocalSum T).den ∣ D →
        1 < (reciprocalSum T : ℝ) := by
  classical
  have hCast (T : Finset ℕ) : (reciprocalSum T : ℝ) = ∑ n ∈ T, (n : ℝ)⁻¹ := by
    simp [reciprocalSum]
  rcases compatible_removal_or_bounded_subset (positivePart A δ)
      (fun T => (reciprocalSum T).den ∣ D) (reciprocal_empty_den_dvd D)
      (fun hDisjoint hU hV => reciprocal_union_den_dvd _ _ D hDisjoint hU hV)
      (fun n => (n : ℝ)⁻¹) η 1 hη with hRemoved | hCrossed
  · obtain ⟨P, hPA, hPCompatible, hPMass, hRemaining⟩ := hRemoved
    rw [← hCast P] at hPMass
    refine ⟨P, hPA, hPCompatible, hPMass, ?_⟩
    intro T hT hTne hTCompatible
    simpa only [← hCast T] using hRemaining T hT hTne hTCompatible
  · obtain ⟨T, hTA, hTCompatible, hTLower, hTUpper⟩ := hCrossed
    rw [← hCast T] at hTLower hTUpper
    have hTne : T.Nonempty := by
      by_contra hEmpty
      have h := Finset.not_nonempty_iff_eq_empty.mp hEmpty
      simp only [h, reciprocalSum, Finset.sum_empty, Rat.cast_zero] at hTLower
      linarith
    have hProper : T ≠ positivePart A δ := by
      intro hEqual
      rw [hEqual] at hTUpper
      linarith
    obtain ⟨U, hU, hValue⟩ := hRepresent (reciprocalSum T) hTCompatible hTLower hTUpper
    exact (hPrimitive.no_equal_opposite_subsums hTA hU hTne hProper hValue.symm).elim

theorem reciprocal_mass_controls_card (P : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hP : P ⊆ Finset.Icc 1 N) (η : ℝ) (hMass : (reciprocalSum P : ℝ) < η) :
    (P.card : ℝ) < (N : ℝ) * η := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLower : (P.card : ℝ) * (N : ℝ)⁻¹ ≤ (reciprocalSum P : ℝ) := by
    calc
      (P.card : ℝ) * (N : ℝ)⁻¹ = ∑ _n ∈ P, (N : ℝ)⁻¹ := by simp
      _ ≤ ∑ n ∈ P, (n : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnOne, hnN⟩ := Finset.mem_Icc.mp (hP hn)
        exact inv_anti₀ (by exact_mod_cast hnOne : (0 : ℝ) < n) (by exact_mod_cast hnN)
      _ = (reciprocalSum P : ℝ) := by simp [reciprocalSum]
  have h := mul_lt_mul_of_pos_right (hLower.trans_lt hMass) hNR
  have hCancel : (P.card : ℝ) * (N : ℝ)⁻¹ * N = P.card := by field_simp
  rw [hCancel] at h
  simpa only [mul_comm] using h

end Erdos319Sharp
