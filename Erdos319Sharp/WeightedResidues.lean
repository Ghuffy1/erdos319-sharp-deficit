import Erdos319Sharp.Baseline
import Erdos319Sharp.Residue

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

def weightedResidues (p : ℕ) (A : Finset ℕ) (w : ℕ → ℕ) (a : ℕ) : Finset (ZMod p) :=
  A.powerset.image (fun B => (a : ZMod p) * ((∑ n ∈ B, w n : ℕ) : ZMod p))

theorem zero_mem_weightedResidues (p : ℕ) (A : Finset ℕ) (w : ℕ → ℕ) (a : ℕ) :
    0 ∈ weightedResidues p A w a := by
  classical
  exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩

theorem full_mem_weightedResidues (p : ℕ) (A : Finset ℕ) (w : ℕ → ℕ) (a : ℕ) :
    (a : ZMod p) * ((∑ n ∈ A, w n : ℕ) : ZMod p) ∈ weightedResidues p A w a := by
  classical
  exact Finset.mem_image.mpr ⟨A, Finset.mem_powerset.mpr Finset.Subset.rfl, rfl⟩

theorem weightedResidues_card_le (p : ℕ) (A : Finset ℕ) (w : ℕ → ℕ) (a : ℕ) :
    (weightedResidues p A w a).card ≤ (∑ n ∈ A, w n) + 1 := by
  classical
  let R := (Finset.range ((∑ n ∈ A, w n) + 1)).image
    (fun z : ℕ => (a : ZMod p) * (z : ZMod p))
  have hSub : weightedResidues p A w a ⊆ R := by
    intro x hx
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hx
    have hBA := Finset.mem_powerset.mp hB
    have hSum : (∑ n ∈ B, w n) ≤ ∑ n ∈ A, w n :=
      Finset.sum_le_sum_of_subset_of_nonneg hBA (fun _ _ _ => Nat.zero_le _)
    exact Finset.mem_image.mpr ⟨∑ n ∈ B, w n, Finset.mem_range.mpr (by omega),
      by simp only [Nat.cast_sum]⟩
  exact (Finset.card_le_card hSub).trans (Finset.card_image_le.trans (by simp))

theorem weightedResidues_complement (p : ℕ) (A : Finset ℕ) (w : ℕ → ℕ) (a : ℕ) :
    ∀ x ∈ weightedResidues p A w a,
      (a : ZMod p) * ((∑ n ∈ A, w n : ℕ) : ZMod p) - x ∈ weightedResidues p A w a := by
  classical
  intro x hx
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hx
  have hBA := Finset.mem_powerset.mp hB
  have hSum : (∑ n ∈ A \ B, w n) + (∑ n ∈ B, w n) = ∑ n ∈ A, w n :=
    Finset.sum_sdiff hBA
  have hCast : ((∑ n ∈ A \ B, w n : ℕ) : ZMod p) + ((∑ n ∈ B, w n : ℕ) : ZMod p) =
      ((∑ n ∈ A, w n : ℕ) : ZMod p) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod p)) hSum
  refine Finset.mem_image.mpr ⟨A \ B, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
  rw [← hCast]
  ring

theorem weightedResidue_eq_zero_iff (p : ℕ) (A B : Finset ℕ) (w : ℕ → ℕ) (a : ℕ)
    (hBA : B ⊆ A) (hPositive : ∀ n ∈ A, 0 < w n)
    (hBound : (∑ n ∈ A, w n) < p) (hCoprime : p.Coprime a) :
    (a : ZMod p) * ((∑ n ∈ B, w n : ℕ) : ZMod p) = 0 ↔ B = ∅ := by
  constructor
  · intro hZero
    have hCongruence : a * (∑ n ∈ B, w n) ≡ 0 [MOD p] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa only [Nat.cast_mul] using hZero
    have hSumBound : (∑ n ∈ B, w n) ≤ ∑ n ∈ A, w n :=
      Finset.sum_le_sum_of_subset_of_nonneg hBA (fun _ _ _ => Nat.zero_le _)
    have hSumZero := bounded_weight_zero hSumBound hBound hCoprime hCongruence
    exact (nat_weight_sum_zero_iff (fun n hn => hPositive n (hBA hn))).mp hSumZero
  · rintro rfl
    simp

theorem weightedResidue_eq_full_iff (p : ℕ) (A B : Finset ℕ) (w : ℕ → ℕ) (a : ℕ)
    (hBA : B ⊆ A) (hPositive : ∀ n ∈ A, 0 < w n)
    (hBound : (∑ n ∈ A, w n) < p) (hCoprime : p.Coprime a) :
    (a : ZMod p) * ((∑ n ∈ B, w n : ℕ) : ZMod p) =
      (a : ZMod p) * ((∑ n ∈ A, w n : ℕ) : ZMod p) ↔ B = A := by
  constructor
  · intro hEqual
    have hCongruence : a * (∑ n ∈ B, w n) ≡ a * (∑ n ∈ A, w n) [MOD p] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      simpa only [Nat.cast_mul] using hEqual
    have hSumBound : (∑ n ∈ B, w n) < p :=
      (Finset.sum_le_sum_of_subset_of_nonneg hBA (fun _ _ _ => Nat.zero_le _)).trans_lt hBound
    have hSumEqual := (Nat.ModEq.cancel_left_of_coprime hCoprime hCongruence).eq_of_lt_of_lt
      hSumBound hBound
    exact nat_weight_sum_eq_of_subset hBA hPositive hSumEqual
  · rintro rfl
    rfl

end Erdos319Sharp
