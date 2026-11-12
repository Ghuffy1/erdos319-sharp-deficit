import Erdos319Sharp.ReciprocalResidues
import Erdos319Sharp.WeightedResidues
import Erdos319Sharp.PathResidues

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def divisorResidues (p D : ℕ) : Finset (ZMod p) :=
  D.divisors.powerset.image (fun B : Finset ℕ => ∑ n ∈ B, (n : ZMod p)⁻¹)

theorem inverse_residue_multiplier_coprime (D p : ℕ) (hCoprime : D.Coprime p) :
    ((D : ZMod p)⁻¹).val.Coprime p := by
  have h := ZMod.val_coe_unit_coprime ((ZMod.unitOfCoprime D hCoprime)⁻¹)
  simpa only [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime] using h

theorem inverse_subsum_eq_weighted (p D : ℕ) (B : Finset ℕ) (hp : 0 < p)
    (hCoprime : D.Coprime p) (hDiv : ∀ n ∈ B, n ∣ D) :
    (∑ n ∈ B, (n : ZMod p)⁻¹) =
      (((D : ZMod p)⁻¹).val : ZMod p) * ((∑ n ∈ B, D / n : ℕ) : ZMod p) := by
  letI : NeZero p := ⟨hp.ne'⟩
  rw [ZMod.natCast_zmod_val]
  have hScaled := scaled_inverse_sum B D p hCoprime hDiv
  have hUnit : (D : ZMod p)⁻¹ * D = 1 := by
    rw [mul_comm, ZMod.coe_mul_inv_eq_one D hCoprime]
  calc
    (∑ n ∈ B, (n : ZMod p)⁻¹) = 1 * (∑ n ∈ B, (n : ZMod p)⁻¹) := (one_mul _).symm
    _ = ((D : ZMod p)⁻¹ * D) * (∑ n ∈ B, (n : ZMod p)⁻¹) := by rw [hUnit]
    _ = (D : ZMod p)⁻¹ * ((D : ZMod p) * (∑ n ∈ B, (n : ZMod p)⁻¹)) := mul_assoc _ _ _
    _ = _ := by rw [hScaled]

theorem divisorResidues_eq_weighted (p D : ℕ) (hp : 0 < p) (hCoprime : D.Coprime p) :
    divisorResidues p D = weightedResidues p D.divisors (fun n => D / n) ((D : ZMod p)⁻¹).val := by
  classical
  unfold divisorResidues weightedResidues
  apply Finset.image_congr
  intro B hB
  exact inverse_subsum_eq_weighted p D B hp hCoprime (fun n hn =>
    Nat.dvd_of_mem_divisors (Finset.mem_powerset.mp hB hn))

theorem divisorResidues_card_le (p D : ℕ) (hp : 0 < p) (hCoprime : D.Coprime p) :
    (divisorResidues p D).card ≤ (∑ n ∈ D.divisors, D / n) + 1 := by
  rw [divisorResidues_eq_weighted p D hp hCoprime]
  exact weightedResidues_card_le p D.divisors (fun n => D / n) _

theorem divisorResidues_complement (p D : ℕ) (hp : 0 < p) (hCoprime : D.Coprime p) :
    ∀ x ∈ divisorResidues p D, (∑ n ∈ D.divisors, (n : ZMod p)⁻¹) - x ∈ divisorResidues p D := by
  rw [divisorResidues_eq_weighted p D hp hCoprime,
    inverse_subsum_eq_weighted p D D.divisors hp hCoprime (fun _ hn => Nat.dvd_of_mem_divisors hn)]
  exact weightedResidues_complement p D.divisors (fun n => D / n) _

theorem divisor_inverse_sum_zero_iff (p D : ℕ) (B : Finset ℕ) (hp : 0 < p)
    (hD : 0 < D) (hCoprime : D.Coprime p) (hB : B ⊆ D.divisors)
    (hBound : (∑ n ∈ D.divisors, D / n) < p) :
    (∑ n ∈ B, (n : ZMod p)⁻¹) = 0 ↔ B = ∅ := by
  rw [inverse_subsum_eq_weighted p D B hp hCoprime
    (fun n hn => Nat.dvd_of_mem_divisors (hB hn))]
  apply weightedResidue_eq_zero_iff p D.divisors B (fun n => D / n) _ hB
  · intro n hn
    exact Nat.div_pos (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hn)) (Nat.pos_of_mem_divisors hn)
  · exact hBound
  · exact (inverse_residue_multiplier_coprime D p hCoprime).symm

theorem divisor_inverse_sum_full_iff (p D : ℕ) (B : Finset ℕ) (hp : 0 < p)
    (hD : 0 < D) (hCoprime : D.Coprime p) (hB : B ⊆ D.divisors)
    (hBound : (∑ n ∈ D.divisors, D / n) < p) :
    (∑ n ∈ B, (n : ZMod p)⁻¹) = (∑ n ∈ D.divisors, (n : ZMod p)⁻¹) ↔ B = D.divisors := by
  rw [inverse_subsum_eq_weighted p D B hp hCoprime
      (fun n hn => Nat.dvd_of_mem_divisors (hB hn)),
    inverse_subsum_eq_weighted p D D.divisors hp hCoprime (fun _ hn => Nat.dvd_of_mem_divisors hn)]
  apply weightedResidue_eq_full_iff p D.divisors B (fun n => D / n) _ hB
  · intro n hn
    exact Nat.div_pos (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hn)) (Nat.pos_of_mem_divisors hn)
  · exact hBound
  · exact (inverse_residue_multiplier_coprime D p hCoprime).symm

theorem divisor_inverse_sum_ne_zero (p D : ℕ) (hp : 0 < p) (hD : 0 < D)
    (hCoprime : D.Coprime p) (hBound : (∑ n ∈ D.divisors, D / n) < p) :
    (∑ n ∈ D.divisors, (n : ZMod p)⁻¹) ≠ 0 := by
  intro hZero
  have hEmpty := (divisor_inverse_sum_zero_iff p D D.divisors hp hD hCoprime Finset.Subset.rfl hBound).mp hZero
  have hOne : 1 ∈ D.divisors := Nat.one_mem_divisors.mpr hD.ne'
  rw [hEmpty] at hOne
  exact Finset.notMem_empty 1 hOne

theorem exists_divisor_block_path_residues (p D : ℕ) (hp : p.Prime) (hD : 0 < D)
    (hCoprime : D.Coprime p) (hBound : (∑ n ∈ D.divisors, D / n) + 1 < p) :
    ∃ a b : (ZMod p)ˣ,
      (b : ZMod p) = -(∑ n ∈ D.divisors, (n : ZMod p)⁻¹) - (a : ZMod p) ∧
      ∀ B ⊆ D.divisors, ∀ incoming outgoing : Bool,
        (∑ n ∈ B, (n : ZMod p)⁻¹) + (if incoming then (a : ZMod p) else 0) +
          (if outgoing then (b : ZMod p) else 0) = 0 →
        incoming = outgoing ∧ B = if incoming then D.divisors else ∅ := by
  classical
  have hZero : 0 ∈ divisorResidues p D := by
    exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩
  have hFull : (∑ n ∈ D.divisors, (n : ZMod p)⁻¹) ∈ divisorResidues p D := by
    exact Finset.mem_image.mpr ⟨D.divisors, Finset.mem_powerset.mpr Finset.Subset.rfl, rfl⟩
  obtain ⟨a, b, hb, hLocal⟩ := exists_internal_path_residues p hp (divisorResidues p D)
    (∑ n ∈ D.divisors, (n : ZMod p)⁻¹) hZero hFull
    (divisorResidues_complement p D hp.pos hCoprime)
    ((divisorResidues_card_le p D hp.pos hCoprime).trans_lt hBound)
  refine ⟨a, b, hb, ?_⟩
  intro B hB incoming outgoing hSum
  have hMem : (∑ n ∈ B, (n : ZMod p)⁻¹) ∈ divisorResidues p D :=
    Finset.mem_image.mpr ⟨B, Finset.mem_powerset.mpr hB, rfl⟩
  obtain ⟨hFlags, hValue⟩ := hLocal _ hMem incoming outgoing hSum
  refine ⟨hFlags, ?_⟩
  have hSmall : (∑ n ∈ D.divisors, D / n) < p := by omega
  cases incoming with
  | false =>
      change B = ∅
      change (∑ n ∈ B, (n : ZMod p)⁻¹) = 0 at hValue
      exact (divisor_inverse_sum_zero_iff p D B hp.pos hD hCoprime hB hSmall).mp hValue
  | true =>
      change B = D.divisors
      change (∑ n ∈ B, (n : ZMod p)⁻¹) = (∑ n ∈ D.divisors, (n : ZMod p)⁻¹) at hValue
      exact (divisor_inverse_sum_full_iff p D B hp.pos hD hCoprime hB hSmall).mp hValue

end Erdos319Sharp
