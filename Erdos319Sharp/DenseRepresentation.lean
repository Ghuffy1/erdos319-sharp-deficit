import Erdos319Sharp.DenseCore

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_dense_tail_core (a : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) :
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N →
      ((Finset.Icc 1 N \ B).card : ℝ) ≤ (a / 8) * N →
      ∃ F ⊆ B ∩ tailInterval a N,
        (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
        ((tailInterval a N \ F).card : ℝ) ≤ (Finset.Icc 1 N \ B).card +
          (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) ∧
        (N : ℝ) / 2 ≤ F.card ∧
        |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 ∧
        ∀ r : ℚ, r.den ∣ F.lcm id →
          (Real.log (1 / a) + 1) / Real.log N ≤ (r : ℝ) → (r : ℝ) ≤ 2 →
          ∃ U ⊆ F, reciprocalSum U = r := by
  have haOne : a ≤ 1 := (small_tail_parameter a ha hMass).trans (by norm_num)
  have hScaleLimit : Tendsto (fun N : ℕ => (Real.log N) ^ (-(3 / 100 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 100)).comp tendsto_log_coe_at_top
  filter_upwards [eventually_dense_tail_regular a ha hMass,
    eventually_exact_subset_from_mass_bounds 1, hScaleLimit.eventually (Iio_mem_nhds ha),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (4 : ℝ))]
    with N hCore hExact hScale hL
  intro B hB hMissing
  obtain ⟨F, hF, hSmooth, hMult, hRich, hLoss, hCard, hApprox⟩ := hCore B hB hMissing
  have hFPrefix : F ⊆ Finset.Icc 1 N := (hF.trans Finset.inter_subset_left).trans hB
  have hFTail : F ⊆ tailInterval a N := hF.trans Finset.inter_subset_right
  have hMin : ∀ n ∈ F, a * N ≤ (n : ℝ) := by
    intro n hn
    exact ((mem_tailInterval a ha.le N n).mp (hFTail hn)).2.2.le
  have hLPos : 0 < Real.log N := by linarith
  have hCardEnough : (N : ℝ) / (Real.log N) ^ (1 : ℕ) ≤ F.card := by
    have hCompare : (N : ℝ) / Real.log N ≤ (N : ℝ) / 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith)
    simpa only [pow_one] using hCompare.trans hCard
  have hcLower : (Real.log N) ^ (-3 / 100 : ℝ) ≤ a := by
    convert hScale.le using 1 <;> norm_num
  refine ⟨F, hF, hSmooth, hLoss, hCard, hApprox, ?_⟩
  intro r hDen hLower hUpper
  have hrPos : (0 : ℝ) < r :=
    (div_pos (by linarith : 0 < Real.log (1 / a) + 1) hLPos).trans_le hLower
  have hr : 0 < r := by exact_mod_cast hrPos
  have hTargetLower : (1 + 1 / Real.log N) * (r : ℝ) ≤ (reciprocalSum F : ℝ) := by
    have hInv : (1 : ℝ) / Real.log N ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hL
    have hMul := mul_le_mul_of_nonneg_left hUpper
      (show 0 ≤ 1 + 1 / Real.log N by positivity)
    have hLowMass := (abs_le.mp hApprox).1
    nlinarith only [hInv, hMul, hLowMass, hMass]
  have hTargetUpper : (reciprocalSum F : ℝ) ≤ Real.log N * (r : ℝ) := by
    have hCross := (div_le_iff₀ hLPos).mp hLower
    have hHighMass := (abs_le.mp hApprox).2
    nlinarith only [hCross, hHighMass]
  exact hExact a ((Real.log N) ^ (-(1 / 25 : ℝ))) F ha haOne hcLower (by norm_num)
    hFPrefix hMin hSmooth hMult hRich hCardEnough r hr hDen hTargetLower hTargetUpper

end Erdos319Sharp
