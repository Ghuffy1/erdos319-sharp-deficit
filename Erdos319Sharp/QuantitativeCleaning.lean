import Erdos319Sharp.MultiplicityMoment
import Erdos319Sharp.SmoothTailRate
import Erdos319Sharp.CleaningBudget

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_quantitative_regular_subset :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      ∃ F ⊆ A,
        (∀ n ∈ F, (Real.log N) ^ (-3 / 100 : ℝ) * N ≤ (n : ℝ)) ∧
        (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
        (∀ n ∈ F, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
        (∀ q ∈ divisorPrimePowers N F, (Real.log N) ^ (-(1 / 25 : ℝ)) ≤
          (q : ℝ) * (reciprocalSum (F.filter (fun n => q ∣ n)) : ℝ)) ∧
        ((A \ F).card : ℝ) ≤ (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) := by
  classical
  filter_upwards [eventually_primePowerTail_log_rate, eventually_high_multiplicity_card_bound 1,
    eventually_primePower_reciprocal_bound, eventually_cleaningBudget_le,
    eventually_gt_atTop (1 : ℕ)] with N hSmoothRate hMultRate hPrimePowerSum hBudget hN
  intro A hA
  let c := (Real.log N) ^ (-3 / 100 : ℝ)
  let η := (Real.log N) ^ (-(1 / 25 : ℝ))
  let G : Finset ℕ := A.filter (fun n : ℕ => c * N ≤ (n : ℝ) ∧
    PrimePowerSmooth (smoothCutoff 6 N) n ∧
      (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2)
  let Low : Finset ℕ := A.filter (fun n : ℕ => (n : ℝ) < c * N)
  let Rough : Finset ℕ := A.filter (fun n : ℕ => ¬ PrimePowerSmooth (smoothCutoff 6 N) n)
  let Many : Finset ℕ := A.filter (fun n : ℕ => (Real.log (Real.log N)) ^ 2 < (primePowerMultiplicity N n : ℝ))
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hc : 0 ≤ c := Real.rpow_nonneg hL.le _
  have hη : 0 ≤ η := Real.rpow_nonneg hL.le _
  have hGSub : G ⊆ A := Finset.filter_subset _ _
  have hGPrefix : G ⊆ Finset.Icc 1 N := hGSub.trans hA
  have hLowSub : Low ⊆ Finset.Icc 1 ⌊c * N⌋₊ := by
    intro n hn
    obtain ⟨hnA, hnLow⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hA hnA)).1,
      (Nat.le_floor_iff (mul_nonneg hc (Nat.cast_nonneg N))).mpr hnLow.le⟩
  have hLow : (Low.card : ℝ) ≤ c * N := by
    have hCard : Low.card ≤ ⌊c * N⌋₊ := by simpa using Finset.card_le_card hLowSub
    exact (by exact_mod_cast hCard : (Low.card : ℝ) ≤ ⌊c * N⌋₊).trans
      (Nat.floor_le (mul_nonneg hc (Nat.cast_nonneg N)))
  have hRough : (Rough.card : ℝ) ≤ (N : ℝ) * (Real.log N) ^ (-(1 / 10 : ℝ)) :=
    (nonsmooth_card_bound A hA (smoothCutoff 6 N)).trans
      (mul_le_mul_of_nonneg_left hSmoothRate (Nat.cast_nonneg N))
  have hMany : (Many.card : ℝ) ≤ (N : ℝ) * (Real.log N) ^ (-1 : ℝ) := by
    simpa only [Nat.cast_one] using hMultRate A hA
  have hCover : A \ G ⊆ (Low ∪ Rough) ∪ Many := by
    intro n hn
    obtain ⟨hnA, hnG⟩ := Finset.mem_sdiff.mp hn
    by_cases hnLow : c * N ≤ (n : ℝ)
    · by_cases hnSmooth : PrimePowerSmooth (smoothCutoff 6 N) n
      · have hnMany : (Real.log (Real.log N)) ^ 2 < (primePowerMultiplicity N n : ℝ) := by
          apply lt_of_not_ge
          intro h
          exact hnG (Finset.mem_filter.mpr ⟨hnA, hnLow, hnSmooth, h⟩)
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnA, hnMany⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnA, hnSmooth⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hnA, lt_of_not_ge hnLow⟩))
  have hInitial : ((A \ G).card : ℝ) ≤ (N : ℝ) *
      (c + (Real.log N) ^ (-(1 / 10 : ℝ)) + (Real.log N) ^ (-1 : ℝ)) := by
    have hUnionOne : (Low ∪ Rough).card ≤ Low.card + Rough.card := Finset.card_union_le _ _
    have hUnionTwo : ((Low ∪ Rough) ∪ Many).card ≤ (Low ∪ Rough).card + Many.card :=
      Finset.card_union_le _ _
    have hCount : (A \ G).card ≤ Low.card + Rough.card + Many.card :=
      (Finset.card_le_card hCover).trans
        (hUnionTwo.trans (Nat.add_le_add_right hUnionOne Many.card))
    have hCountR : ((A \ G).card : ℝ) ≤ Low.card + Rough.card + Many.card := by exact_mod_cast hCount
    nlinarith only [hCountR, hLow, hRough, hMany]
  obtain ⟨F, hFG, hRich, hPrune⟩ := prime_power_cleanup G hGPrefix η hη
  have hFA : F ⊆ A := hFG.trans hGSub
  have hPruneCard : ((G \ F).card : ℝ) ≤
      (N : ℝ) * (2 * η * Real.log (Real.log N)) := by
    have hCount := card_le_N_mul_reciprocalSum
      ((Finset.sdiff_subset : G \ F ⊆ G).trans hGPrefix)
    have hSplit : (Erdos319Formal.reciprocalSum (G \ F) : ℝ) +
        (Erdos319Formal.reciprocalSum F : ℝ) = (Erdos319Formal.reciprocalSum G : ℝ) := by
      simp only [Erdos319Formal.reciprocalSum_real]
      exact Finset.sum_sdiff hFG
    have hLoss : (Erdos319Formal.reciprocalSum (G \ F) : ℝ) ≤
        2 * η * Real.log (Real.log N) := by
      have h := mul_le_mul_of_nonneg_left hPrimePowerSum hη
      nlinarith only [hSplit, hPrune, h]
    exact hCount.trans (mul_le_mul_of_nonneg_left hLoss (Nat.cast_nonneg N))
  have hTotalCard : ((A \ F).card : ℝ) = ((A \ G).card : ℝ) + ((G \ F).card : ℝ) := by
    have hAG := Finset.card_sdiff_add_card_eq_card hGSub
    have hGF := Finset.card_sdiff_add_card_eq_card hFG
    have hAF := Finset.card_sdiff_add_card_eq_card hFA
    have h : (A \ F).card = (A \ G).card + (G \ F).card := by omega
    exact_mod_cast h
  refine ⟨F, hFA, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact (Finset.mem_filter.mp (hFG hn)).2.1
  · intro n hn
    exact (Finset.mem_filter.mp (hFG hn)).2.2.1
  · intro n hn
    exact (Finset.mem_filter.mp (hFG hn)).2.2.2
  · intro q hq
    obtain ⟨hqPP, hqF⟩ := Finset.mem_filter.mp hq
    have hPrimePower := (Finset.mem_filter.mp hqPP).2
    simpa only [reciprocalSum_eq_baseline] using hRich q hPrimePower hqF
  · calc
      ((A \ F).card : ℝ) = ((A \ G).card : ℝ) + ((G \ F).card : ℝ) := hTotalCard
      _ ≤ (N : ℝ) * cleaningBudget N := by
        dsimp [cleaningBudget, c, η] at *
        nlinarith only [hInitial, hPruneCard]
      _ ≤ (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) :=
        mul_le_mul_of_nonneg_left hBudget (Nat.cast_nonneg N)

end Erdos319Sharp
