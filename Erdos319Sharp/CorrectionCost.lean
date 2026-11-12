import Erdos319Sharp.LogarithmicPrimeSupply
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def logSquareCost (q : ℕ) : ℝ := 1 / ((q : ℝ) * (Real.log q) ^ 2)

def logarithmicCorrectionCost (q : ℕ) : ℝ :=
  1 / ((q : ℝ) * (⌊Real.log q⌋₊ : ℝ) ^ 2)

theorem logSquareCost_nonneg (q : ℕ) : 0 ≤ logSquareCost q := by
  unfold logSquareCost
  positivity

theorem logSquareCost_antitone {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    logSquareCost n ≤ logSquareCost m := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hLogPos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hmnReal : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hLog := Real.log_le_log hmPos hmnReal
  have hProduct : (m : ℝ) * (Real.log m) ^ 2 ≤ (n : ℝ) * (Real.log n) ^ 2 :=
    mul_le_mul (by exact_mod_cast hmn) (pow_le_pow_left₀ hLogPos.le hLog 2)
      (sq_nonneg _) (Nat.cast_nonneg n)
  exact one_div_le_one_div_of_le (mul_pos hmPos (sq_pos_of_pos hLogPos)) hProduct

theorem summable_logSquareCost : Summable logSquareCost := by
  have hMono : ∀ᶠ k : ℕ in atTop, logSquareCost (k + 1) ≤ logSquareCost k := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
    exact logSquareCost_antitone hk (by omega)
  apply (summable_condensed_iff_of_eventually_nonneg
    (Filter.Eventually.of_forall logSquareCost_nonneg) hMono).mp
  have hSeries : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  apply (hSeries.mul_left ((Real.log 2) ^ 2)⁻¹).congr
  intro k
  unfold logSquareCost
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  by_cases hk : k = 0
  · simp [hk]
  · have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hLogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp [hkReal, hLogTwo]

theorem logarithmicCorrectionCost_nonneg (q : ℕ) : 0 ≤ logarithmicCorrectionCost q := by
  unfold logarithmicCorrectionCost
  positivity

theorem eventually_logarithmicCorrectionCost_le :
    ∀ᶠ q : ℕ in atTop, logarithmicCorrectionCost q ≤ 4 * logSquareCost q := by
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hLogLimit.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with q hLog hq
  change 2 ≤ Real.log (q : ℝ) at hLog
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hLogPos : 0 < Real.log q := by linarith
  have hFloor := Nat.lt_floor_add_one (Real.log q)
  have hFloorLower : Real.log q / 2 ≤ (⌊Real.log q⌋₊ : ℝ) := by linarith
  have hFloorPos : (0 : ℝ) < (⌊Real.log q⌋₊ : ℝ) := by linarith
  have hSquare : (Real.log q) ^ 2 ≤ 4 * (⌊Real.log q⌋₊ : ℝ) ^ 2 := by
    nlinarith only [hFloorLower, hLogPos, hFloorPos]
  have hProduct := mul_le_mul_of_nonneg_left hSquare hqReal.le
  unfold logarithmicCorrectionCost logSquareCost
  rw [mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hqReal (sq_pos_of_pos hFloorPos))
    (mul_pos hqReal (sq_pos_of_pos hLogPos))).mpr
  nlinarith only [hProduct]

theorem summable_logarithmicCorrectionCost : Summable logarithmicCorrectionCost := by
  apply (summable_logSquareCost.mul_left 4).of_norm_bounded_eventually_nat
  filter_upwards [eventually_logarithmicCorrectionCost_le] with q hq
  simpa only [Real.norm_eq_abs, abs_of_nonneg (logarithmicCorrectionCost_nonneg q)] using hq

theorem exists_small_correction_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ Q : Finset ℕ, (∀ q ∈ Q, L ≤ q) →
      (∑ q ∈ Q, logarithmicCorrectionCost q) < ε := by
  have hPartial : Tendsto (fun L : ℕ => (∑' q, logarithmicCorrectionCost q) -
      ∑ q ∈ Finset.range L, logarithmicCorrectionCost q) atTop (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ => ∑' q, logarithmicCorrectionCost q) atTop
        (𝓝 (∑' q, logarithmicCorrectionCost q)) := tendsto_const_nhds
    simpa only [sub_self] using
      hConst.sub summable_logarithmicCorrectionCost.hasSum.tendsto_sum_nat
  obtain ⟨L, hL⟩ := (hPartial.eventually (Iio_mem_nhds hε)).exists
  refine ⟨L, ?_⟩
  intro Q hQ
  have hDisjoint : Disjoint Q (Finset.range L) := Finset.disjoint_left.mpr (by
    intro q hq hRange
    have hSmall := Finset.mem_range.mp hRange
    have hLarge := hQ q hq
    omega)
  have hBound := summable_logarithmicCorrectionCost.sum_le_tsum (Q ∪ Finset.range L)
    (fun q _ => logarithmicCorrectionCost_nonneg q)
  rw [Finset.sum_union hDisjoint] at hBound
  linarith only [hBound, hL]

end Erdos319Sharp
