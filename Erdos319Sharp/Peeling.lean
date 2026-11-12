import Erdos319Sharp.Basic
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

/-- Maximal removal below a threshold either leaves no small compatible block,
or produces a compatible subset in the prescribed mass interval. -/
theorem compatible_removal_or_bounded_subset
    (A : Finset ℕ) (Compatible : Finset ℕ → Prop)
    (hEmpty : Compatible ∅)
    (hUnion : ∀ {U V : Finset ℕ}, Disjoint U V →
      Compatible U → Compatible V → Compatible (U ∪ V))
    (w : ℕ → ℝ) (δ M : ℝ) (hδ : 0 < δ) :
    (∃ P ⊆ A, Compatible P ∧ (∑ n ∈ P, w n) < δ ∧
      ∀ T ⊆ A \ P, T.Nonempty → Compatible T → M < ∑ n ∈ T, w n) ∨
    (∃ W ⊆ A, Compatible W ∧ δ ≤ (∑ n ∈ W, w n) ∧
      (∑ n ∈ W, w n) < δ + M) := by
  classical
  let C := A.powerset.filter (fun P => Compatible P ∧ (∑ n ∈ P, w n) < δ)
  have hCne : C.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset A),
      hEmpty, ?_⟩⟩
    simpa using hδ
  obtain ⟨P, hPC, hCardP⟩ := Finset.exists_mem_eq_sup C hCne Finset.card
  have hPA : P ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hPC).1
  have hPcomp : Compatible P := (Finset.mem_filter.mp hPC).2.1
  have hPmass : (∑ n ∈ P, w n) < δ := (Finset.mem_filter.mp hPC).2.2
  have hMax : ∀ U ∈ C, U.card ≤ P.card := by
    intro U hUC
    exact (Finset.le_sup (f := Finset.card) hUC).trans_eq hCardP
  by_cases hSmall : ∃ T : Finset ℕ, T ⊆ A \ P ∧ T.Nonempty ∧
      Compatible T ∧ (∑ n ∈ T, w n) ≤ M
  · obtain ⟨T, hTsub, hTne, hTcomp, hTmass⟩ := hSmall
    have hDisjoint : Disjoint P T := by
      apply Finset.disjoint_left.mpr
      intro n hnP hnT
      exact (Finset.mem_sdiff.mp (hTsub hnT)).2 hnP
    have hUnionSub : P ∪ T ⊆ A := by
      intro n hn
      rcases Finset.mem_union.mp hn with hn | hn
      · exact hPA hn
      · exact (Finset.mem_sdiff.mp (hTsub hn)).1
    have hUnionComp : Compatible (P ∪ T) := hUnion hDisjoint hPcomp hTcomp
    have hLower : δ ≤ ∑ n ∈ P ∪ T, w n := by
      apply le_of_not_gt
      intro hLess
      have hMem : P ∪ T ∈ C := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hUnionSub, hUnionComp, hLess⟩
      have hCard := hMax (P ∪ T) hMem
      rw [Finset.card_union_of_disjoint hDisjoint] at hCard
      have hStrict := Nat.add_lt_add_left (Finset.card_pos.mpr hTne) P.card
      simp only [Nat.add_zero] at hStrict
      exact (Nat.not_lt_of_ge hCard) hStrict
    right
    refine ⟨P ∪ T, hUnionSub, hUnionComp, hLower, ?_⟩
    rw [Finset.sum_union hDisjoint]
    linarith
  · left
    refine ⟨P, hPA, hPcomp, hPmass, ?_⟩
    intro T hTsub hTne hTcomp
    apply lt_of_not_ge
    intro hTmass
    exact hSmall ⟨T, hTsub, hTne, hTcomp, hTmass⟩

end Erdos319Sharp
