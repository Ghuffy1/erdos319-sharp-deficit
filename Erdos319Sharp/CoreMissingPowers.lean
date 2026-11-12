import Erdos319Sharp.FirstMissingPowers
import Erdos319Sharp.DenseSigning

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def coreOmissionRate (K : ℝ) (N : ℕ) : ℝ :=
  (201 + 2 * |K|) * minorityScale N + (Real.log N) ^ (-(1 / 40 : ℝ))

theorem tendsto_coreOmissionRate_zero (K : ℝ) :
    Tendsto (coreOmissionRate K) atTop (𝓝 0) := by
  have hPower := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)).comp
    tendsto_log_coe_at_top
  change Tendsto (fun N : ℕ => (201 + 2 * |K|) * minorityScale N +
    (Real.log N) ^ (-(1 / 40 : ℝ))) atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero, add_zero] using
    (tendsto_minorityScale_zero.const_mul (201 + 2 * |K|)).add hPower

theorem eventually_coreOmissionRate_nonneg (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 ≤ coreOmissionRate K N := by
  filter_upwards [eventually_positive_scale,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ))] with N hN hL
  unfold coreOmissionRate
  exact add_nonneg (mul_nonneg (by positivity) (div_pos hN.2.2 hN.2.1).le)
    (Real.rpow_nonneg hL _)

theorem eventually_core_missing_mass_small (a K ε : ℝ) (ha : 0 ≤ a)
    (haQuarter : a ≤ 1 / 4) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ F : Finset ℕ, F ⊆ Finset.Icc 1 N →
      ((tailInterval a N \ F).card : ℝ) ≤ (N : ℝ) * coreOmissionRate K N →
      (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) ≤ ε := by
  filter_upwards [eventually_coreOmissionRate_nonneg K,
    (tendsto_coreOmissionRate_zero K).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32)),
    (tendsto_coreOmissionRate_zero K).eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 32)),
    eventually_gt_atTop (0 : ℕ)] with N hRate hSmall hTarget hN
  intro F hF hLoss
  have h := firstMissingPowers_mass_bound a (coreOmissionRate K N) ha haQuarter hRate hSmall.le
    N hN F hF (by simpa only [mul_comm] using hLoss)
  exact h.trans (by linarith only [hTarget])

theorem eventually_dense_sign_core_with_missing_bound (a K ε : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ →
      ((N - A.card : ℕ) : ℝ) ≤ K * ((N : ℝ) * minorityScale N) →
      ∃ B : Finset ℕ, (B = positivePart A δ ∨ B = negativePart A δ) ∧
        ∃ F ⊆ B ∩ tailInterval a N,
          (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
          ((tailInterval a N \ F).card : ℝ) ≤ (N : ℝ) * coreOmissionRate K N ∧
          (N : ℝ) / 2 ≤ F.card ∧
          |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 ∧
          (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) ≤ ε ∧
          ∀ r : ℚ, r.den ∣ F.lcm id →
            (Real.log (1 / a) + 1) / Real.log N ≤ (r : ℝ) → (r : ℝ) ≤ 2 →
            ∃ U ⊆ F, reciprocalSum U = r := by
  filter_upwards [eventually_dense_sign_core a |K| ha hMass,
    eventually_core_missing_mass_small a K ε ha.le (small_tail_parameter a ha hMass) hε,
    eventually_positive_scale] with N hCore hSmall hN
  intro A δ hA hPrimitive hDeficit
  have hScale : 0 ≤ (N : ℝ) * minorityScale N :=
    mul_nonneg hN.1.le (div_pos hN.2.2 hN.2.1).le
  have hAbs : ((N - A.card : ℕ) : ℝ) ≤ |K| * ((N : ℝ) * minorityScale N) :=
    hDeficit.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hScale)
  obtain ⟨B, hChoice, F, hF, hSmooth, hLoss, hCard, hApprox, hTargets⟩ :=
    hCore A δ hA hPrimitive hAbs
  have hPrefix : F ⊆ Finset.Icc 1 N :=
    (hF.trans Finset.inter_subset_right).trans (tailInterval_subset a N)
  have hRateLoss : ((tailInterval a N \ F).card : ℝ) ≤ (N : ℝ) * coreOmissionRate K N := hLoss
  exact ⟨B, hChoice, F, hF, hSmooth, hRateLoss, hCard, hApprox,
    hSmall F hPrefix hRateLoss, hTargets⟩

end Erdos319Sharp
