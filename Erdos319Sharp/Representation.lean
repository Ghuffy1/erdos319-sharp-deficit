import Erdos319Sharp.Major
import Erdos319Sharp.Middle

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- Uniform exact representation once the finite localization property is
available. Density, minimum denominator and variance may vary with `N`.
The localization property remains an explicit hypothesis here.
-/
theorem eventually_exact_target_of_localization (k l m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c τ : ℝ, ∀ A : Finset ℕ,
      0 < c → c ≤ 1 → 0 < τ →
      1 / (Real.log N) ^ k ≤ c → 1 / (Real.log N) ^ l ≤ τ →
      A ⊆ Finset.Icc 1 N →
      (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (N : ℝ) / (Real.log N) ^ m ≤ (A.card : ℝ) →
      (∀ h : ℤ, ∃ y : ℤ, |(y : ℝ) - h| < localizationWidth c N / 2 ∧
        ∀ q ∈ rareDivisorSet c τ N A h, (q : ℤ) ∣ y) →
      ∀ r : ℚ, 0 ≤ r → r.den ∣ A.lcm id →
      ∀ p : ℕ → ℝ, (∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) →
      (∀ n ∈ A, τ ≤ p n * (1 - p n)) →
      (∑ n ∈ A, p n / n) = (r : ℝ) →
      ∃ B ⊆ A, reciprocalSum B = r := by
  filter_upwards [eventually_uniform_smooth_lcm_log_growth k,
    eventually_major_parameters_of_log_bound k,
    eventually_middle_parameters_of_log_bounds l m,
    tendsto_classificationMajorant.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)]
      with N hGrowth hMajor hMiddle hClass hLL hL hN
  intro c τ A hc hc1 hτ hcLower hτLower hA hMin hSmooth hMult hCard hLocal
    r hr hDen p hp hVar hMean
  let Q := A.lcm id
  have hPos : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  have hQPos : 0 < Q :=
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos n hn).ne'))
  letI : NeZero Q := ⟨hQPos.ne'⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hAne : A.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (div_pos hNR (pow_pos hL m)).trans_le hCard
  obtain ⟨x, hx⟩ := exists_numerator_over_common (Q := Q) r hr hDen
  have hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q := by
    rw [hMean]
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) hx
  have hLarge := large_frequency_bound_of_localization (Q := Q) (x := x)
    A p c τ hN hc hc1 hτ hLL rfl hAne hA hMin hMult hp hVar hLocal hClass
  have hGrowthN := hGrowth c hc hcLower A hSmooth
  have hMajorN := hMajor c hc hcLower
  have hMiddleN := hMiddle τ (A.card : ℝ) hτLower hCard
  have hMN : c * (N : ℝ) ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hNR.le
  have hDiv : ∀ n ∈ A, n ∣ Q := fun n hn => Finset.dvd_lcm hn
  obtain ⟨B, hB, hSum⟩ := exact_subset_of_large_frequency_bound A p
    ((N : ℝ) ^ (3 / 5 : ℝ)) (c * N) τ hN (mul_pos hc hNR) hMN
    (Real.rpow_nonneg hNR.le _) hMajorN.1 hA hMin hDiv hp hτ.le hVar hExpected
    hMajorN.2.1 hMajorN.2.2 hMiddleN hLarge hGrowthN.1 hGrowthN.2
  exact ⟨B, hB, hSum.trans hx.symm⟩

end Erdos319Sharp
