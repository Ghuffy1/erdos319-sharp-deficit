import Erdos319Sharp.ConstructionGrowth
import Erdos319Sharp.Harmonic

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem tendsto_constructionBoundary_unfloored :
    Tendsto (fun N : ℕ => (N : ℝ) / constructionMass N) atTop atTop := by
  have hSmall : Tendsto (fun N : ℕ => constructionMass N / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_constructionMass_div_power 1 (by norm_num)
  have hPositive : ∀ᶠ N : ℕ in atTop, 0 < constructionMass N / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact div_pos (lt_of_lt_of_le (by norm_num) (constructionMass_one_le N))
      (by exact_mod_cast (by omega : 0 < N))
  have hWithin : Tendsto (fun N : ℕ => constructionMass N / (N : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hSmall, hPositive⟩
  convert hWithin.inv_tendsto_nhdsGT_zero using 1
  funext N
  simp only [Pi.inv_apply, inv_div]

theorem tendsto_constructionBoundary : Tendsto constructionBoundary atTop atTop := by
  change Tendsto (fun N : ℕ => ⌊(N : ℝ) / constructionMass N⌋₊) atTop atTop
  exact tendsto_nat_floor_atTop.comp tendsto_constructionBoundary_unfloored

theorem constructionBoundary_le_div (N : ℕ) :
    (constructionBoundary N : ℝ) ≤ (N : ℝ) / constructionMass N :=
  Nat.floor_le (div_nonneg (Nat.cast_nonneg _) (le_trans (by norm_num) (constructionMass_one_le N)))

theorem constructionBoundary_le (N : ℕ) : constructionBoundary N ≤ N := by
  apply Nat.floor_le_of_le
  exact div_le_self (Nat.cast_nonneg N) (constructionMass_one_le N)

theorem tendsto_constructionBoundary_mass_ratio :
    Tendsto (fun N : ℕ => (constructionBoundary N : ℝ) * constructionMass N / N)
      atTop (𝓝 1) := by
  have hRatio := tendsto_nat_floor_div_atTop.comp tendsto_constructionBoundary_unfloored
  apply (show Tendsto (fun N : ℕ =>
      (constructionBoundary N : ℝ) / ((N : ℝ) / constructionMass N)) atTop (𝓝 1) from hRatio).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNZero : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hMass : constructionMass N ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)).ne'
  field_simp [hNZero, hMass]

theorem eventually_constructionBoundary_lower :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) / (2 * constructionMass N) ≤ constructionBoundary N := by
  have hHalf := tendsto_constructionBoundary_mass_ratio.eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hHalf, eventually_ge_atTop (1 : ℕ)] with N hHalfN hN
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hMassPos)).mpr
  have hProduct := (le_div_iff₀ hNPos).mp hHalfN.le
  nlinarith only [hProduct]

theorem tendsto_constructionBoundary_harmonic_gap :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) - (harmonic (constructionBoundary N) : ℝ) -
      Real.log (constructionMass N)) atTop (𝓝 0) := by
  have hLog : Tendsto (fun N : ℕ => Real.log
      ((constructionBoundary N : ℝ) * constructionMass N / N)) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      tendsto_constructionBoundary_mass_ratio.log (by norm_num : (1 : ℝ) ≠ 0)
  have h := (Real.tendsto_harmonic_sub_log.sub
    (Real.tendsto_harmonic_sub_log.comp tendsto_constructionBoundary)).sub hLog
  apply (show Tendsto (fun N : ℕ =>
      ((harmonic N : ℝ) - Real.log N) -
        ((harmonic (constructionBoundary N) : ℝ) - Real.log (constructionBoundary N)) -
          Real.log ((constructionBoundary N : ℝ) * constructionMass N / N)) atTop (𝓝 0) from
    by simpa only [Function.comp_def, sub_self, sub_zero] using h).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    tendsto_constructionBoundary.eventually (eventually_ge_atTop (1 : ℕ))] with N hN hB
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBPos : (0 : ℝ) < constructionBoundary N := by exact_mod_cast (by omega : 0 < constructionBoundary N)
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  rw [Real.log_div (mul_pos hBPos hMassPos).ne' hNPos.ne', Real.log_mul hBPos.ne' hMassPos.ne']
  ring

end Erdos319Sharp
