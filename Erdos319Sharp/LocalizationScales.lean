import Erdos319Sharp.FiniteLocalization

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def stretchedExponent (a : ℝ) (b : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  (Real.log N) ^ a / (C * (Real.log (Real.log N)) ^ b)

def stretchedCutoff (a : ℝ) (b : ℕ) (C : ℝ) (N : ℕ) : ℕ :=
  ⌊Real.exp (stretchedExponent a b C N)⌋₊

theorem tendsto_stretchedExponent (a : ℝ) (b : ℕ) (C : ℝ)
    (ha : 0 < a) (hC : 0 < C) :
    Tendsto (stretchedExponent a b C) atTop atTop := by
  have hSmall : Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ b /
      (Real.log N) ^ a) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      ((isLittleO_log_rpow_rpow_atTop (b : ℝ) ha).tendsto_div_nhds_zero).comp
        tendsto_log_coe_at_top
  have hPositive : ∀ᶠ N : ℕ in atTop, 0 < (Real.log (Real.log N)) ^ b /
      (Real.log N) ^ a := by
    filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLL hL
    exact div_pos (pow_pos hLL b) (Real.rpow_pos_of_pos hL a)
  have hSmallWithin : Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ b /
      (Real.log N) ^ a) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hSmall, hPositive⟩
  have hGrowth : Tendsto (fun N : ℕ => (Real.log N) ^ a /
      (Real.log (Real.log N)) ^ b) atTop atTop := by
    convert hSmallWithin.inv_tendsto_nhdsGT_zero using 1
    funext N
    simp only [Pi.inv_apply, inv_div]
  change Tendsto (fun N : ℕ => (Real.log N) ^ a /
    (C * (Real.log (Real.log N)) ^ b)) atTop atTop
  simpa only [div_div, mul_comm] using hGrowth.atTop_div_const hC

theorem tendsto_stretchedCutoff (a : ℝ) (b : ℕ) (C : ℝ)
    (ha : 0 < a) (hC : 0 < C) :
    Tendsto (stretchedCutoff a b C) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_exp_atTop.comp (tendsto_stretchedExponent a b C ha hC))

theorem eventually_stretchedCutoff_loglog_bounds (a : ℝ) (b : ℕ) (C : ℝ)
    (ha : 0 < a) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      a * Real.log (Real.log N) - (b : ℝ) * Real.log (Real.log (Real.log N)) -
          Real.log (2 * C) ≤ Real.log (Real.log (stretchedCutoff a b C N)) ∧
        Real.log (Real.log (stretchedCutoff a b C N)) ≤
          a * Real.log (Real.log N) - (b : ℝ) * Real.log (Real.log (Real.log N)) -
            Real.log C := by
  filter_upwards [
    (tendsto_stretchedExponent a b C ha hC).eventually
      (eventually_ge_atTop (max 1 (2 * Real.log 2))),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
    with N hGrowth hL hLL
  let u := stretchedExponent a b C N
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hGrowth)
  have huTwo : 2 * Real.log 2 ≤ u := (le_max_right _ _).trans hGrowth
  have hLogU : Real.log u = a * Real.log (Real.log N) - Real.log C -
      (b : ℝ) * Real.log (Real.log (Real.log N)) := by
    dsimp [u, stretchedExponent]
    rw [Real.log_div (Real.rpow_pos_of_pos hL a).ne' (by positivity),
      Real.log_rpow hL, Real.log_mul hC.ne' (pow_ne_zero _ hLL.ne'), Real.log_pow]
    ring
  have hFloor := log_floor_exp_bounds u hu.le
  have hHalf : u / 2 ≤ Real.log (stretchedCutoff a b C N) := by
    change u / 2 ≤ Real.log (⌊Real.exp u⌋₊ : ℕ)
    linarith only [hFloor.1, huTwo]
  have hLogPos : 0 < Real.log (stretchedCutoff a b C N) := (half_pos hu).trans_le hHalf
  have hLower := Real.log_le_log (half_pos hu) hHalf
  have hUpper := Real.log_le_log hLogPos hFloor.2
  change Real.log (Real.log (stretchedCutoff a b C N)) ≤ Real.log u at hUpper
  rw [Real.log_div hu.ne' (by norm_num), hLogU] at hLower
  rw [hLogU] at hUpper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hC.ne']
  constructor <;> linarith

theorem stretchedCutoff_le_ambient (a : ℝ) (b : ℕ) (C : ℝ) (N : ℕ)
    (ha : a ≤ 1) (hC : 1 ≤ C) (hN : 0 < N)
    (hL : 1 ≤ Real.log N) (hLL : 1 ≤ Real.log (Real.log N)) :
    stretchedCutoff a b C N ≤ N := by
  apply floor_exp_le_nat N (stretchedExponent a b C N) hN
  have hDen : 1 ≤ C * (Real.log (Real.log N)) ^ b :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hLL)
  calc
    stretchedExponent a b C N ≤ (Real.log N) ^ a :=
      div_le_self (Real.rpow_nonneg (zero_le_one.trans hL) _) hDen
    _ ≤ Real.log N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL ha

theorem nat_le_of_loglog_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : Real.log (Real.log a) ≤ Real.log (Real.log b)) : a ≤ b := by
  have haR : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hLog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    (Real.log_le_log_iff (Real.log_pos haR) (Real.log_pos hbR)).mp h
  exact_mod_cast (Real.log_le_log_iff (by linarith : (0 : ℝ) < a)
    (by linarith : (0 : ℝ) < b)).mp hLog

def packetMediumBound (N : ℕ) : ℕ := stretchedCutoff (3 / 5) 0 1 N

def packetCommonBound (N : ℕ) : ℕ := stretchedCutoff (3 / 5) 2 16 N

theorem tendsto_packetMediumBound : Tendsto packetMediumBound atTop atTop :=
  tendsto_stretchedCutoff (3 / 5) 0 1 (by norm_num) (by norm_num)

theorem tendsto_packetCommonBound : Tendsto packetCommonBound atTop atTop :=
  tendsto_stretchedCutoff (3 / 5) 2 16 (by norm_num) (by norm_num)

end Erdos319Sharp
