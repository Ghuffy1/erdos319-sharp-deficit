import Erdos319Sharp.ZeroSum
import Mathlib.Order.Minimal

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem exists_small_zero_subset (q : ℕ) (hq : 0 < q) (A : Finset ℕ)
    (f : ℕ → ZMod q) (hPos : ∀ n ∈ A, 0 < n)
    (hZero : ∃ T ⊆ A, T.Nonempty ∧ (∑ n ∈ T, f n) = 0) :
    ∃ T ⊆ A, T.Nonempty ∧ (∑ n ∈ T, f n) = 0 ∧ T.card ≤ q := by
  classical
  let P : Finset ℕ → Prop := fun T => T ⊆ A ∧ T.Nonempty ∧ (∑ n ∈ T, f n) = 0
  obtain ⟨T, hMinimal⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card hZero
  obtain ⟨hTA, hTne, hTSum⟩ := hMinimal.prop
  obtain ⟨a, ha⟩ := hTne
  have hErase : ZeroSumFree (T.erase a) f := by
    intro U hU hUne hUSum
    have hUT : U ⊆ T := hU.trans (Finset.erase_subset a T)
    have hUP : P U := ⟨hUT.trans hTA, hUne, hUSum⟩
    have hCard : U.card < T.card := by
      have hLe := Finset.card_le_card hU
      have hEraseCard := Finset.card_erase_add_one ha
      omega
    exact hMinimal.not_lt hUP hCard
  have hBound := hErase.card_lt_modulus hq (fun n hn => hPos n (hTA (Finset.mem_of_mem_erase hn)))
  have hEraseCard := Finset.card_erase_add_one ha
  exact ⟨T, hTA, ⟨a, ha⟩, hTSum, by omega⟩

theorem exists_small_zero_subset_of_not_free (q : ℕ) (hq : 0 < q) (A : Finset ℕ)
    (f : ℕ → ZMod q) (hPos : ∀ n ∈ A, 0 < n) (hNotFree : ¬ZeroSumFree A f) :
    ∃ T ⊆ A, T.Nonempty ∧ (∑ n ∈ T, f n) = 0 ∧ T.card ≤ q := by
  classical
  apply exists_small_zero_subset q hq A f hPos
  by_contra hNoSubset
  apply hNotFree
  intro T hTA hTne hTSum
  exact hNoSubset ⟨T, hTA, hTne, hTSum⟩

end Erdos319Sharp
