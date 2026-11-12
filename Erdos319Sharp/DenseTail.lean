import Erdos319Sharp.QuantitativeCleaning
import Erdos319Sharp.ExactSubset

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def tailInterval (a : ℝ) (N : ℕ) : Finset ℕ := coprimeWindow 1 a N

theorem mem_tailInterval (a : ℝ) (ha : 0 ≤ a) (N n : ℕ) :
    n ∈ tailInterval a N ↔ 1 ≤ n ∧ n ≤ N ∧ a * N < (n : ℝ) := by
  simp only [tailInterval, mem_coprimeWindow_iff 1 a ha N n, Nat.coprime_one_left_iff, true_and]

theorem tailInterval_subset (a : ℝ) (N : ℕ) : tailInterval a N ⊆ Finset.Icc 1 N :=
  coprimeWindow_subset 1 a N

theorem tailInterval_card (a : ℝ) (ha : a ≤ 1) (N : ℕ) :
    ((tailInterval a N).card : ℝ) = N - (⌊a * N⌋₊ : ℕ) := by
  simpa [tailInterval, coprimePrefix_eq_filter_Icc] using coprimeWindow_card 1 a ha N

theorem tailInterval_card_lower (a : ℝ) (ha : 0 ≤ a) (haOne : a ≤ 1) (N : ℕ) :
    (1 - a) * (N : ℝ) ≤ (tailInterval a N).card := by
  rw [tailInterval_card a haOne N]
  have hFloor : (⌊a * N⌋₊ : ℝ) ≤ a * N := Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg N))
  linarith

theorem tendsto_tailInterval_reciprocal (a : ℝ) (ha : 0 < a) (haOne : a ≤ 1) :
    Tendsto (fun N : ℕ => (reciprocalSum (tailInterval a N) : ℝ))
      atTop (𝓝 (Real.log (1 / a))) := by
  simpa only [tailInterval, reciprocalSum_eq_baseline, coprimeDensity,
    Nat.totient_one, Nat.cast_one, div_one, one_mul] using
      tendsto_coprimeWindow_reciprocal 1 (by norm_num) a ha haOne

theorem tail_omission_card_le (a : ℝ) (N : ℕ) (B F : Finset ℕ) :
    ((tailInterval a N \ F).card : ℝ) ≤
      (Finset.Icc 1 N \ B).card + ((B ∩ tailInterval a N) \ F).card := by
  classical
  have hCover : tailInterval a N \ F ⊆
      (Finset.Icc 1 N \ B) ∪ ((B ∩ tailInterval a N) \ F) := by
    intro n hn
    obtain ⟨hnT, hnF⟩ := Finset.mem_sdiff.mp hn
    by_cases hnB : n ∈ B
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hnB, hnT⟩, hnF⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨tailInterval_subset a N hnT, hnB⟩)
  exact_mod_cast (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)

theorem tail_subset_mass_bounds (a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 0 < N)
    (F : Finset ℕ) (hF : F ⊆ tailInterval a N) :
    (reciprocalSum (tailInterval a N) : ℝ) - (tailInterval a N \ F).card / (a * N) ≤
        (reciprocalSum F : ℝ) ∧
      (reciprocalSum F : ℝ) ≤ (reciprocalSum (tailInterval a N) : ℝ) := by
  have hSplitQ : reciprocalSum (tailInterval a N \ F) + reciprocalSum F =
      reciprocalSum (tailInterval a N) := Finset.sum_sdiff hF
  have hSplit : (reciprocalSum (tailInterval a N \ F) : ℝ) + (reciprocalSum F : ℝ) =
      (reciprocalSum (tailInterval a N) : ℝ) := by exact_mod_cast hSplitQ
  have hBound := reciprocalSum_le_card_div_min (tailInterval a N \ F) (a * N)
    (mul_pos ha (by exact_mod_cast hN)) (by
      intro n hn
      exact ((mem_tailInterval a ha.le N n).mp (Finset.mem_sdiff.mp hn).1).2.2.le)
  rw [← reciprocalSum_eq_baseline] at hBound
  have hNonneg : (0 : ℝ) ≤ reciprocalSum (tailInterval a N \ F) := by
    rw [reciprocalSum_eq_baseline]
    exact_mod_cast Erdos319Formal.reciprocalSum_nonneg (tailInterval a N \ F)
  constructor <;> linarith

end Erdos319Sharp
