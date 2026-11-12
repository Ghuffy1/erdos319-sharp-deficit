import Erdos319Sharp.ReciprocalTails
import Erdos319Sharp.LcmLowerBound
import Erdos319Sharp.Imported.UnitFractions.AuxiliaryLemmas

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem primeProduct_nonCoprime_cover (P : Finset ℕ) (n : ℕ)
    (hPrime : ∀ p ∈ P, p.Prime) (hNot : ¬n.Coprime (P.prod id)) :
    ∃ p ∈ P, p ∣ n := by
  classical
  by_contra hNo
  push_neg at hNo
  apply hNot
  exact Nat.coprime_prod_right_iff.mpr (fun p hp =>
    ((hPrime p hp).coprime_iff_not_dvd.mpr (hNo p hp)).symm)

theorem prime_covered_tail_mass (b N : ℕ) (P A : Finset ℕ)
    (hbN : b ≤ N) (hPrime : ∀ p ∈ P, p.Prime) (hSmall : ∀ p ∈ P, p ≤ b)
    (hA : A ⊆ integerTail b N) (hCover : ∀ n ∈ A, ∃ p ∈ P, p ∣ n) :
    (reciprocalSum A : ℝ) ≤
      (1 + Real.log (2 * (N : ℝ) / b)) * (∑ p ∈ P, (1 : ℝ) / p) := by
  classical
  let U := P.biUnion (fun p => (integerTail b N).filter (fun n => p ∣ n))
  have hSub : A ⊆ U := by
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hCover n hn
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hA hn, hpn⟩⟩
  calc
    (reciprocalSum A : ℝ) = ∑ n ∈ A, (1 : ℝ) / n := Erdos319Formal.reciprocalSum_real A
    _ ≤ ∑ n ∈ U, (1 : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => by positivity)
    _ ≤ ∑ p ∈ P, ∑ n ∈ (integerTail b N).filter (fun n => p ∣ n), (1 : ℝ) / n :=
      Erdos319Imported.UnitFractions.sum_bUnion_le_sum_of_nonneg (fun _ _ => by positivity)
    _ = ∑ p ∈ P, (reciprocalSum ((integerTail b N).filter (fun n => p ∣ n)) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Erdos319Formal.reciprocalSum_real _).symm
    _ ≤ ∑ p ∈ P, (1 + Real.log (2 * (N : ℝ) / b)) / p := by
      apply Finset.sum_le_sum
      intro p hp
      exact reciprocalSum_divisibleTail_upper b N p (hPrime p hp).pos (hSmall p hp) hbN
    _ = (1 + Real.log (2 * (N : ℝ) / b)) * (∑ p ∈ P, (1 : ℝ) / p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end Erdos319Sharp
