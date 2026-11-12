import Erdos319Sharp.DenseTail

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem small_tail_parameter (a : ℝ) (ha : 0 < a) (hMass : 3 ≤ Real.log (1 / a)) :
    a ≤ 1 / 4 := by
  have hLog := Real.log_le_sub_one_of_pos (one_div_pos.mpr ha)
  have hInv : (4 : ℝ) ≤ 1 / a := by linarith
  have hCross := (le_div_iff₀ ha).mp hInv
  linarith

theorem eventually_dense_tail_regular (a : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) :
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N →
      ((Finset.Icc 1 N \ B).card : ℝ) ≤ (a / 8) * N →
      ∃ F ⊆ B ∩ tailInterval a N,
        (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
        (∀ n ∈ F, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
        (∀ q ∈ divisorPrimePowers N F, (Real.log N) ^ (-(1 / 25 : ℝ)) ≤
          (q : ℝ) * (reciprocalSum (F.filter (fun n => q ∣ n)) : ℝ)) ∧
        ((tailInterval a N \ F).card : ℝ) ≤ (Finset.Icc 1 N \ B).card +
          (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) ∧
        (N : ℝ) / 2 ≤ F.card ∧
        |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 := by
  have haQuarter := small_tail_parameter a ha hMass
  have haOne : a ≤ 1 := by linarith
  have hLossLimit : Tendsto (fun N : ℕ => (Real.log N) ^ (-(1 / 40 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)).comp tendsto_log_coe_at_top
  have hTail := (tendsto_tailInterval_reciprocal a ha haOne).eventually
    (Ioo_mem_nhds (by linarith : Real.log (1 / a) - 1 / 4 < Real.log (1 / a))
      (by linarith : Real.log (1 / a) < Real.log (1 / a) + 1 / 4))
  filter_upwards [eventually_quantitative_regular_subset, hTail,
    hLossLimit.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < a / 8)),
    eventually_gt_atTop (0 : ℕ)] with N hClean hTailNear hLossSmall hN
  intro B hB hMissing
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨F, hF, _, hSmooth, hMult, hRich, hPrune⟩ :=
    hClean (B ∩ tailInterval a N) (Finset.inter_subset_left.trans hB)
  have hFT : F ⊆ tailInterval a N := hF.trans Finset.inter_subset_right
  have hTotal : ((tailInterval a N \ F).card : ℝ) ≤
      (Finset.Icc 1 N \ B).card + (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) := by
    have hCover := tail_omission_card_le a N B F
    linarith only [hCover, hPrune]
  have hLoss : ((tailInterval a N \ F).card : ℝ) ≤ (a / 4) * N := by
    have hSmall := mul_le_mul_of_nonneg_left hLossSmall.le hNReal.le
    nlinarith only [hTotal, hMissing, hSmall]
  have hCount : ((tailInterval a N \ F).card : ℝ) + F.card = (tailInterval a N).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hFT
  have hCard : (N : ℝ) / 2 ≤ F.card := by
    have hTailCard := tailInterval_card_lower a ha.le haOne N
    have hQuarter := mul_le_mul_of_nonneg_right haQuarter hNReal.le
    nlinarith only [hCount, hLoss, hTailCard, hQuarter, hNReal.le]
  have hFMass := tail_subset_mass_bounds a ha N hN F hFT
  have hLossMass : ((tailInterval a N \ F).card : ℝ) / (a * N) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos ha hNReal)).mpr
    nlinarith only [hLoss]
  have hApprox : |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hTailNear.1, hTailNear.2, hFMass.1, hFMass.2]
  exact ⟨F, hF, hSmooth, hMult, hRich, hTotal, hCard, hApprox⟩

end Erdos319Sharp
