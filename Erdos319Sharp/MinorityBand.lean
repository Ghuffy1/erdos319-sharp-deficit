import Erdos319Sharp.MinorityCounting
import Erdos319Sharp.PrimeBand

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def minorityLower (N : ℕ) : ℕ := ⌈(Real.log (Real.log N)) ^ 2⌉₊

def minorityUpper (N : ℕ) : ℕ := ⌊(Real.log N) ^ (1 / 100 : ℝ)⌋₊

def minorityPrimeBand (N : ℕ) : Finset ℕ := primeInterval (minorityLower N) (minorityUpper N)

def minorityScale (N : ℕ) : ℝ :=
  Real.log (Real.log (Real.log N)) / Real.log (Real.log N)

theorem tendsto_log_natCast_div_log_of_ratio (g : ℝ → ℕ)
    (hRatio : Tendsto (fun x => (g x : ℝ) / x) atTop (𝓝 1))
    (hg : Tendsto g atTop atTop) :
    Tendsto (fun x => Real.log (g x : ℝ) / Real.log x) atTop (𝓝 1) := by
  have hLogRatio := hRatio.log (by norm_num : (1 : ℝ) ≠ 0)
  have hSmall : Tendsto (fun x => Real.log ((g x : ℝ) / x) / Real.log x) atTop (𝓝 0) := by
    simpa only [Real.log_one, div_eq_mul_inv, zero_mul, Function.comp_def] using
      hLogRatio.mul (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop)
  have h := hSmall.add_const 1
  apply (show Tendsto (fun x => Real.log ((g x : ℝ) / x) / Real.log x + 1)
    atTop (𝓝 1) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hg.eventually (eventually_ge_atTop (1 : ℕ))]
    with x hx hgx
  have hgPos : (0 : ℝ) < g x := by exact_mod_cast (show 0 < g x by omega)
  have hxPos : 0 < x := zero_lt_one.trans hx
  rw [Real.log_div hgPos.ne' hxPos.ne']
  field_simp [(Real.log_pos hx).ne']
  ring

theorem tendsto_log_nat_floor_div_log :
    Tendsto (fun x : ℝ => Real.log (⌊x⌋₊ : ℕ) / Real.log x) atTop (𝓝 1) :=
  tendsto_log_natCast_div_log_of_ratio Nat.floor tendsto_nat_floor_div_atTop tendsto_nat_floor_atTop

theorem tendsto_log_nat_ceil_div_log :
    Tendsto (fun x : ℝ => Real.log (⌈x⌉₊ : ℕ) / Real.log x) atTop (𝓝 1) :=
  tendsto_log_natCast_div_log_of_ratio Nat.ceil tendsto_nat_ceil_div_atTop tendsto_nat_ceil_atTop

theorem tendsto_minorityLower : Tendsto minorityLower atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
    tendsto_log_log_coe_at_top)

theorem tendsto_minorityUpper : Tendsto minorityUpper atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
    tendsto_log_coe_at_top)

theorem tendsto_log_minorityLower_div_logloglog :
    Tendsto (fun N : ℕ => Real.log (minorityLower N) / Real.log (Real.log (Real.log N)))
      atTop (𝓝 2) := by
  have hGrowth := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_log_log_coe_at_top
  have h := (tendsto_log_nat_ceil_div_log.comp hGrowth).mul_const 2
  apply (show Tendsto (fun N : ℕ =>
    Real.log (minorityLower N) / Real.log ((Real.log (Real.log N)) ^ 2) * 2)
    atTop (𝓝 2) by simpa [minorityLower, Function.comp_def] using h).congr'
  filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
    with N hLL
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp [(Real.log_pos hLL).ne']

theorem tendsto_log_minorityUpper_div_loglog :
    Tendsto (fun N : ℕ => Real.log (minorityUpper N) / Real.log (Real.log N))
      atTop (𝓝 (1 / 100 : ℝ)) := by
  have hGrowth := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp tendsto_log_coe_at_top
  have h := (tendsto_log_nat_floor_div_log.comp hGrowth).mul_const (1 / 100 : ℝ)
  apply (show Tendsto (fun N : ℕ =>
    Real.log (minorityUpper N) / Real.log ((Real.log N) ^ (1 / 100 : ℝ)) * (1 / 100 : ℝ))
    atTop (𝓝 (1 / 100 : ℝ)) by simpa [minorityUpper, Function.comp_def] using h).congr'
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
    with N hL
  rw [Real.log_rpow (zero_lt_one.trans hL)]
  field_simp [(Real.log_pos hL).ne']

theorem tendsto_minorityScale_zero : Tendsto minorityScale atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => Real.log (Real.log (Real.log N)) / Real.log (Real.log N))
    atTop (𝓝 0)
  simpa only [Function.comp_def, id_eq] using
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_log_coe_at_top)

end Erdos319Sharp
