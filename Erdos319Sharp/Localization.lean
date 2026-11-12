import Erdos319Sharp.Fourier

set_option autoImplicit false

open Filter Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- The rare-residue cost can be made smaller than a varying prime-power
fiber threshold with an inverse-logarithmic lower bound. -/
theorem eventually_localization_cost_with_log_mass (k l m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c τ η : ℝ,
      0 < c → 0 < τ →
      1 / (Real.log N) ^ k ≤ c →
      1 / (Real.log N) ^ l ≤ τ →
      1 / (Real.log N) ^ m ≤ η →
      ∀ q : ℕ, (q : ℝ) ≤ smoothCutoff 6 N →
        (q : ℝ) * localizationRarity c τ N / (c * N) ≤ η / 2 := by
  filter_upwards [eventually_localization_cost_of_log_bounds k (l + m),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hCost hLL hL hN c τ η hc hτ hcLower hτLower hηLower q hq
  let a : ℝ := (Real.log N) ^ m
  have ha : 0 < a := pow_pos hL m
  have hScaledLower : 1 / (Real.log N) ^ (l + m) ≤ τ / a := by
    rw [pow_add, ← div_div]
    exact div_le_div_of_nonneg_right hτLower ha.le
  have hScaled := hCost c (τ / a) hc (div_pos hτ ha) hcLower hScaledLower q hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hWidth : 0 < localizationWidth c N := by
    unfold localizationWidth
    positivity
  have hIdentity : (q : ℝ) * localizationRarity c (τ / a) N / (c * N) =
      a * ((q : ℝ) * localizationRarity c τ N / (c * N)) := by
    unfold localizationRarity
    field_simp [ha.ne', hτ.ne', hWidth.ne', (mul_pos hc hNR).ne'] <;> ring
  rw [hIdentity] at hScaled
  have hHalf : 1 / (2 * (Real.log (Real.log N)) ^ 2) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (Real.log N)) ^ 2)).mpr
    nlinarith only [hLL]
  have hSmall : (q : ℝ) * localizationRarity c τ N / (c * N) ≤ (1 / a) / 2 := by
    rw [div_right_comm]
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using hScaled.trans hHalf
  exact hSmall.trans (div_le_div_of_nonneg_right hηLower (by norm_num))

end Erdos319Sharp
