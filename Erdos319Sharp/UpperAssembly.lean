import Erdos319Sharp.QuantitativeCompletion
import Erdos319Sharp.PrimeSetPath

set_option autoImplicit false

open Finset Erdos319Formal

namespace Erdos319Sharp

theorem primitive_of_core_bulk_completion {N B G : ℕ} {E F C : Finset ℕ}
    (hB : B ≤ N) (hCore : MinimalCore G E)
    (hE : E ⊆ Icc 1 N) (hF : F ⊆ Icc (B + 1) N) (hC : C ⊆ Icc 1 B)
    (hFCoprime : ∀ n ∈ F, n.Coprime G) (hCCoprime : ∀ n ∈ C, n.Coprime G)
    (hCompletion : reciprocalSum C = reciprocalSum E - reciprocalSum F) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ Primitive A ∧ F ⊆ A ∧ F.card ≤ A.card := by
  classical
  have hDisjoint : Disjoint F C := by
    apply Finset.disjoint_left.mpr
    intro n hnF hnC
    have hLower := (Finset.mem_Icc.mp (hF hnF)).1
    have hUpper := (Finset.mem_Icc.mp (hC hnC)).2
    omega
  have hMass : reciprocalSum (F ∪ C) = reciprocalSum E := by
    have hUnion : reciprocalSum (F ∪ C) = reciprocalSum F + reciprocalSum C :=
      Finset.sum_union hDisjoint
    rw [hUnion, hCompletion]
    ring
  have hPositive : ∀ n ∈ F ∪ C, 0 < n := by
    intro n hn
    rcases Finset.mem_union.mp hn with hnF | hnC
    · have h := (Finset.mem_Icc.mp (hF hnF)).1
      omega
    · exact (Finset.mem_Icc.mp (hC hnC)).1
  have hCoprime : ∀ n ∈ F ∪ C, n.Coprime G := by
    intro n hn
    rcases Finset.mem_union.mp hn with hnF | hnC
    · exact hFCoprime n hnF
    · exact hCCoprime n hnC
  have hPrimitive : Primitive (E ∪ (F ∪ C)) :=
    primitive_union_of_minimalCore hCore hPositive hCoprime hMass.symm
  have hContains : F ⊆ E ∪ (F ∪ C) := by
    intro n hn
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hn)
  refine ⟨E ∪ (F ∪ C), ?_, hPrimitive, hContains, Finset.card_le_card hContains⟩
  intro n hn
  rcases Finset.mem_union.mp hn with hnE | hnOther
  · exact hE hnE
  · rcases Finset.mem_union.mp hnOther with hnF | hnC
    · obtain ⟨hLower, hUpper⟩ := Finset.mem_Icc.mp (hF hnF)
      exact Finset.mem_Icc.mpr ⟨by omega, hUpper⟩
    · obtain ⟨hLower, hUpper⟩ := Finset.mem_Icc.mp (hC hnC)
      exact Finset.mem_Icc.mpr ⟨hLower, hUpper.trans hB⟩

end Erdos319Sharp
