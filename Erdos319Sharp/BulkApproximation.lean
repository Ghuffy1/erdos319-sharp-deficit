import Erdos319Sharp.BulkMass
import Erdos319Sharp.BulkParameters
import Erdos319Sharp.BulkErrorScales

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_constructionBulk_mass_approximation (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ, P ⊆ constructionPrimeBand N →
      (∑ p ∈ P, (1 : ℝ) / p) ≤ constructionTarget η N + 1 / constructionPrimeBase N →
      |(reciprocalSum (constructionBulk P N) : ℝ) - Real.log (constructionMass N)| ≤
        constructionBulkError η N := by
  filter_upwards [eventually_constructionPrimeBand_below_boundary,
    eventually_construction_boundary_log_bound, eventually_constructionBoundary_lower,
    eventually_primePowerTail_log_rate,
    tendsto_constructionBoundary.eventually (eventually_ge_atTop (1 : ℕ))]
    with N hBelow hLog hLower hRate hB P hP hRhoUpper
  have hBPos : (0 : ℝ) < constructionBoundary N := by exact_mod_cast (by omega : 0 < constructionBoundary N)
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  have hRhoNonneg : 0 ≤ ∑ p ∈ P, (1 : ℝ) / p := Finset.sum_nonneg (fun _ _ => by positivity)
  have hLogNonneg : 0 ≤ Real.log (4 * constructionMass N) :=
    Real.log_nonneg (by linarith [constructionMass_one_le N])
  have hPrimeLoss : (1 + Real.log (2 * (N : ℝ) / constructionBoundary N)) *
      (∑ p ∈ P, (1 : ℝ) / p) ≤ constructionPrimeLoss η N := by
    calc
      _ ≤ (1 + Real.log (4 * constructionMass N)) * (∑ p ∈ P, (1 : ℝ) / p) :=
        mul_le_mul_of_nonneg_right (show 1 + Real.log (2 * (N : ℝ) / constructionBoundary N) ≤
          1 + Real.log (4 * constructionMass N) by linarith) hRhoNonneg
      _ ≤ (1 + Real.log (4 * constructionMass N)) *
          (constructionTarget η N + 1 / constructionPrimeBase N) :=
        mul_le_mul_of_nonneg_left hRhoUpper (by linarith)
      _ = constructionPrimeLoss η N := by unfold constructionPrimeLoss; ring
  have hRatio : (N : ℝ) / constructionBoundary N ≤ 2 * constructionMass N := by
    apply (div_le_iff₀ hBPos).mpr
    have h := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hMassPos)).mp hLower
    simpa only [mul_comm] using h
  have hSmoothLoss : (N : ℝ) * primePowerTail N (smoothCutoff 6 N) / constructionBoundary N ≤
      constructionSmoothLoss N := by
    calc
      _ ≤ (N : ℝ) * (Real.log N) ^ (-(1 / 10 : ℝ)) / constructionBoundary N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRate (Nat.cast_nonneg N)) hBPos.le
      _ = ((N : ℝ) / constructionBoundary N) * (Real.log N) ^ (-(1 / 10 : ℝ)) := by ring
      _ ≤ (2 * constructionMass N) * (Real.log N) ^ (-(1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_right hRatio (by positivity)
      _ = constructionSmoothLoss N := rfl
  have hPrimeNonneg : 0 ≤ constructionPrimeLoss η N := by
    unfold constructionPrimeLoss
    exact mul_nonneg (add_nonneg (constructionTarget_pos η hη N).le (by positivity)) (by linarith)
  have hSmoothNonneg : 0 ≤ constructionSmoothLoss N := by
    unfold constructionSmoothLoss
    exact mul_nonneg (mul_nonneg (by norm_num) hMassPos.le) (by positivity)
  have hBounds := smoothCoprimeTail_mass_bounds P (constructionBoundary N) N (smoothCutoff 6 N)
    (by omega) (constructionBoundary_le N)
    (fun p hp => (mem_constructionPrimeBand.mp (hP hp)).1) (fun p hp => hBelow p (hP hp))
  have hTail : (reciprocalSum (integerTail (constructionBoundary N) N) : ℝ) =
      (harmonic N : ℝ) - (harmonic (constructionBoundary N) : ℝ) := by
    exact_mod_cast reciprocalSum_integerTail (constructionBoundary N) N (constructionBoundary_le N)
  rw [hTail] at hBounds
  change |(reciprocalSum (smoothCoprimeTail P (constructionBoundary N) N (smoothCutoff 6 N)) : ℝ) -
      Real.log (constructionMass N)| ≤ _
  unfold constructionBulkError
  have hAbsLower := neg_abs_le ((harmonic N : ℝ) - (harmonic (constructionBoundary N) : ℝ) -
    Real.log (constructionMass N))
  have hAbsUpper := le_abs_self ((harmonic N : ℝ) - (harmonic (constructionBoundary N) : ℝ) -
    Real.log (constructionMass N))
  apply abs_le.mpr
  constructor <;> linarith [hBounds.1, hBounds.2]

theorem eventually_constructionBulk_omissions :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ, P ⊆ constructionPrimeBand N →
      (N : ℝ) - (constructionBulk P N).card ≤
        constructionBoundary N + (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) +
          (N : ℝ) * (Real.log N) ^ (-(1 / 10 : ℝ)) := by
  filter_upwards [eventually_primePowerTail_log_rate] with N hRate P hP
  have hBound := smoothCoprimeTail_omission_bound P (constructionBoundary N) N (smoothCutoff 6 N)
    (fun p hp => (mem_constructionPrimeBand.mp (hP hp)).1)
  have hProduct := mul_le_mul_of_nonneg_left hRate (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  exact hBound.trans (by linarith)

end Erdos319Sharp
