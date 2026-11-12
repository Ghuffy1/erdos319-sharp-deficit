import Erdos319Sharp.BoundaryScales

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_constructionBoundary_sqrt :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 / 2 : ℝ) ≤ constructionBoundary N := by
  have hHalf := (tendsto_constructionMass_div_power (1 / 2) (by norm_num)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hHalf, eventually_constructionBoundary_lower, eventually_ge_atTop (1 : ℕ)]
    with N hHalfN hLower hN
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  have hPowerPos := Real.rpow_pos_of_pos hNPos (1 / 2 : ℝ)
  have hMassBound : 2 * constructionMass N ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have h := (div_lt_iff₀ hPowerPos).mp hHalfN
    linarith
  have hProd : (N : ℝ) ^ (1 / 2 : ℝ) * (2 * constructionMass N) ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hMassBound hPowerPos.le
      _ = N := by rw [← Real.rpow_add hNPos]; norm_num
  exact ((le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hMassPos)).mpr hProd).trans hLower

theorem eventually_constructionPrimeBand_below_boundary :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ constructionPrimeBand N, p ≤ constructionBoundary N := by
  filter_upwards [eventually_constructionBoundary_sqrt, eventually_ge_atTop (1 : ℕ)]
    with N hBoundary hN p hp
  have hPrime := (constructionPrimeBand_power_bounds hp).2
  have hPower : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  exact_mod_cast hPrime.trans (hPower.trans hBoundary)

theorem eventually_construction_boundary_log_bound :
    ∀ᶠ N : ℕ in atTop,
      Real.log (2 * (N : ℝ) / constructionBoundary N) ≤ Real.log (4 * constructionMass N) := by
  filter_upwards [eventually_constructionBoundary_lower, eventually_ge_atTop (1 : ℕ),
    tendsto_constructionBoundary.eventually (eventually_ge_atTop (1 : ℕ))]
    with N hLower hN hB
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBPos : (0 : ℝ) < constructionBoundary N := by exact_mod_cast (by omega : 0 < constructionBoundary N)
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  apply Real.log_le_log (div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hNPos) hBPos)
  apply (div_le_iff₀ hBPos).mpr
  have hProduct := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hMassPos)).mp hLower
  nlinarith only [hProduct]

end Erdos319Sharp
