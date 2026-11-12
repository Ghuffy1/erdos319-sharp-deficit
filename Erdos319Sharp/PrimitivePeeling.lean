import Erdos319Sharp.ExcessGroups

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem IsPrimitiveSigning.exists_peeled_inverse_free_groups
    {A : Finset ℕ} {δ : ℕ → ℤˣ} (hPrimitive : IsPrimitiveSigning A δ)
    (N D : ℕ) (hN : 0 < N) (hD : D ≠ 0) (hA : A ⊆ Finset.Icc 1 N)
    (η : ℝ) (hη : 0 < η)
    (hMass : η + 1 ≤ (reciprocalSum (positivePart A δ) : ℝ))
    (hRepresent : ∀ r : ℚ, r.den ∣ D → η ≤ (r : ℝ) → (r : ℝ) < η + 1 →
      ∃ U ⊆ negativePart A δ, reciprocalSum U = r) :
    ∃ P ⊆ positivePart A δ, (reciprocalSum P).den ∣ D ∧ (reciprocalSum P : ℝ) < η ∧
      (P.card : ℝ) < (N : ℝ) * η ∧
      ∀ b : ℕ, 0 < b → InverseZeroSumFree b (excessCofactors D b (positivePart A δ \ P)) := by
  obtain ⟨P, hP, hCompatible, hPMass, hNoSmall⟩ :=
    hPrimitive.exists_compatible_removal D η hη hMass hRepresent
  have hPositivePrefix : positivePart A δ ⊆ Finset.Icc 1 N :=
    (Finset.filter_subset _ _).trans hA
  have hPCard := reciprocal_mass_controls_card P N hN (hP.trans hPositivePrefix) η hPMass
  refine ⟨P, hP, hCompatible, hPMass, hPCard, ?_⟩
  intro b hb
  apply excessCofactors_inverse_free D b (positivePart A δ \ P) hD hb
  · intro n hn
    exact (Finset.mem_Icc.mp (hPositivePrefix (Finset.mem_sdiff.mp hn).1)).1
  · intro T hT hTne hTCompatible
    exact_mod_cast hNoSmall T hT hTne hTCompatible

end Erdos319Sharp
