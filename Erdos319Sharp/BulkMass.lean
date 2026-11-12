import Erdos319Sharp.BulkSets

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem smoothCoprimeTail_mass_bounds (P : Finset ℕ) (b N : ℕ) (S : ℝ)
    (hb : 0 < b) (hbN : b ≤ N) (hPrime : ∀ p ∈ P, p.Prime)
    (hSmall : ∀ p ∈ P, p ≤ b) :
    (reciprocalSum (integerTail b N) : ℝ) -
        (1 + Real.log (2 * (N : ℝ) / b)) * (∑ p ∈ P, (1 : ℝ) / p) -
          (N : ℝ) * primePowerTail N S / b ≤ (reciprocalSum (smoothCoprimeTail P b N S) : ℝ) ∧
      (reciprocalSum (smoothCoprimeTail P b N S) : ℝ) ≤ (reciprocalSum (integerTail b N) : ℝ) := by
  classical
  let T := integerTail b N
  let G := T.filter (fun n => n.Coprime (P.prod id))
  let F := smoothCoprimeTail P b N S
  let K := T \ G
  let R := G \ F
  have hGSub : G ⊆ T := Finset.filter_subset _ _
  have hFSub : F ⊆ G := by
    intro n hn
    have h := mem_smoothCoprimeTail.mp hn
    exact Finset.mem_filter.mpr ⟨h.1, h.2.1⟩
  have hKCover : ∀ n ∈ K, ∃ p ∈ P, p ∣ n := by
    intro n hn
    obtain ⟨hnT, hnG⟩ := Finset.mem_sdiff.mp hn
    apply primeProduct_nonCoprime_cover P n hPrime
    intro hCop
    exact hnG (Finset.mem_filter.mpr ⟨hnT, hCop⟩)
  have hKMass : (reciprocalSum K : ℝ) ≤
      (1 + Real.log (2 * (N : ℝ) / b)) * (∑ p ∈ P, (1 : ℝ) / p) :=
    prime_covered_tail_mass b N P K hbN hPrime hSmall Finset.sdiff_subset hKCover
  have hRough : R ⊆ T.filter (fun n => ¬PrimePowerSmooth S n) := by
    intro n hn
    obtain ⟨hnG, hnF⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnT, hCop⟩ := Finset.mem_filter.mp hnG
    refine Finset.mem_filter.mpr ⟨hnT, ?_⟩
    intro hSmooth
    exact hnF (mem_smoothCoprimeTail.mpr ⟨hnT, hCop, hSmooth⟩)
  have hRCard : (R.card : ℝ) ≤ (N : ℝ) * primePowerTail N S := by
    have hCard : (R.card : ℝ) ≤ ((T.filter (fun n => ¬PrimePowerSmooth S n)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hRough
    exact hCard.trans (nonsmooth_card_bound T (integerTail_subset b N) S)
  have hBPos : (0 : ℝ) < b := by exact_mod_cast hb
  have hRMass : (reciprocalSum R : ℝ) ≤ (N : ℝ) * primePowerTail N S / b := by
    have hBound : (reciprocalSum R : ℝ) ≤ R.card / (b : ℝ) :=
      reciprocalSum_le_card_div_min R b hBPos (by
        intro n hn
        have hnT : n ∈ T := hGSub (Finset.mem_sdiff.mp hn).1
        have hLower := (Finset.mem_Icc.mp hnT).1
        exact_mod_cast (by omega : b ≤ n))
    exact hBound.trans (div_le_div_of_nonneg_right hRCard hBPos.le)
  have hSplitKQ : reciprocalSum K + reciprocalSum G = reciprocalSum T := Finset.sum_sdiff hGSub
  have hSplitRQ : reciprocalSum R + reciprocalSum F = reciprocalSum G := Finset.sum_sdiff hFSub
  have hSplitK : (reciprocalSum K : ℝ) + (reciprocalSum G : ℝ) = (reciprocalSum T : ℝ) := by
    exact_mod_cast hSplitKQ
  have hSplitR : (reciprocalSum R : ℝ) + (reciprocalSum F : ℝ) = (reciprocalSum G : ℝ) := by
    exact_mod_cast hSplitRQ
  have hUpperQ : reciprocalSum F ≤ reciprocalSum T :=
    Finset.sum_le_sum_of_subset_of_nonneg (hFSub.trans hGSub) (fun _ _ _ => by positivity)
  have hUpper : (reciprocalSum F : ℝ) ≤ (reciprocalSum T : ℝ) := by exact_mod_cast hUpperQ
  exact ⟨by linarith, hUpper⟩

end Erdos319Sharp
