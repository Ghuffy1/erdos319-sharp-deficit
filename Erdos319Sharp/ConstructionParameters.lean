import Erdos319Sharp.LcmMass
import Erdos319Sharp.MinorityBand

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def constructionBase (N : ℕ) : ℕ := ⌊Real.log N / 1000⌋₊

def constructionModulus (N : ℕ) : ℕ := Nat.lcmUpto (constructionBase N)

def constructionMass (N : ℕ) : ℝ := divisorReciprocalMass (constructionModulus N)

def constructionPrimeBase (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊

def constructionPrimeBand (N : ℕ) : Finset ℕ :=
  primeInterval (constructionPrimeBase N) (constructionPrimeBase N ^ 2)

def constructionBoundary (N : ℕ) : ℕ := ⌊(N : ℝ) / constructionMass N⌋₊

theorem constructionModulus_pos (N : ℕ) : 0 < constructionModulus N := Nat.lcmUpto_pos _

theorem constructionMass_one_le (N : ℕ) : 1 ≤ constructionMass N := by
  have hSub : ({1} : Finset ℕ) ⊆ (constructionModulus N).divisors := by
    intro n hn
    rcases Finset.mem_singleton.mp hn with rfl
    exact Nat.one_mem_divisors.mpr (constructionModulus_pos N).ne'
  have hSum : (∑ n ∈ ({1} : Finset ℕ), (n : ℚ)⁻¹) ≤
      ∑ n ∈ (constructionModulus N).divisors, (n : ℚ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => by positivity)
  have hRational : (1 : ℚ) ≤ reciprocalSum (constructionModulus N).divisors := by
    simpa [reciprocalSum] using hSum
  change (1 : ℝ) ≤ (reciprocalSum (constructionModulus N).divisors : ℝ)
  exact_mod_cast hRational

theorem tendsto_constructionBase : Tendsto constructionBase atTop atTop := by
  change Tendsto (fun N : ℕ => ⌊Real.log N / 1000⌋₊) atTop atTop
  exact tendsto_nat_floor_atTop.comp
    (tendsto_log_coe_at_top.atTop_div_const (by norm_num : (0 : ℝ) < 1000))

theorem tendsto_log_scaled_div_log (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log (x / c) / Real.log x) atTop (𝓝 1) := by
  have hError : Tendsto (fun x : ℝ => Real.log c / Real.log x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop) :
        Tendsto (fun x : ℝ => Real.log c * (Real.log x)⁻¹) atTop (𝓝 (Real.log c * 0)))
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  apply (show Tendsto (fun x : ℝ => 1 - Real.log c / Real.log x) atTop (𝓝 1) from
    by simpa only [sub_zero] using hOne.sub hError).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.log_div (zero_lt_one.trans hx).ne' hc.ne']
  field_simp [(Real.log_pos hx).ne']
  <;> ring

theorem tendsto_log_constructionBase_ratio :
    Tendsto (fun N : ℕ => Real.log (constructionBase N) / Real.log (Real.log N)) atTop (𝓝 1) := by
  have hX : Tendsto (fun N : ℕ => Real.log N / 1000) atTop atTop :=
    tendsto_log_coe_at_top.atTop_div_const (by norm_num)
  have hFirst := tendsto_log_nat_floor_div_log.comp hX
  have hSecond := (tendsto_log_scaled_div_log 1000 (by norm_num)).comp tendsto_log_coe_at_top
  have hProduct := hFirst.mul hSecond
  apply (show Tendsto (fun N : ℕ =>
      (Real.log (constructionBase N) / Real.log (Real.log N / 1000)) *
        (Real.log (Real.log N / 1000) / Real.log (Real.log N))) atTop (𝓝 1) from
    by simpa only [Function.comp_def, constructionBase, one_mul] using hProduct).congr'
  filter_upwards [hX.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))] with N hXN hLN
  field_simp [(Real.log_pos hXN).ne', (Real.log_pos hLN).ne']

theorem tendsto_constructionMass_ratio :
    Tendsto (fun N : ℕ => constructionMass N / Real.log (Real.log N)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have hFirst := tendsto_lcm_divisorReciprocalMass_div_log.comp tendsto_constructionBase
  have hProduct := hFirst.mul tendsto_log_constructionBase_ratio
  apply (show Tendsto (fun N : ℕ =>
      (constructionMass N / Real.log (constructionBase N)) *
        (Real.log (constructionBase N) / Real.log (Real.log N))) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) from
    by simpa only [constructionMass, constructionModulus, Function.comp_def, mul_one] using hProduct).congr'
  filter_upwards [tendsto_constructionBase.eventually (eventually_ge_atTop (2 : ℕ)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hBase hLoglog
  have hLogBase : 0 < Real.log (constructionBase N) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < constructionBase N))
  field_simp [hLogBase.ne', hLoglog.ne']

theorem constructionModulus_power_bound (N : ℕ) (hN : 1 ≤ N) :
    (constructionModulus N : ℝ) ≤ (N : ℝ) ^ (1 / 100 : ℝ) := by
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hBase : (constructionBase N : ℝ) ≤ Real.log N / 1000 :=
    Nat.floor_le (div_nonneg hLogN (by norm_num))
  have hLogFour : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hChebyshev := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (constructionBase N))
  rw [Chebyshev.psi_eq_log_lcmUpto] at hChebyshev
  have hLogD : Real.log (constructionModulus N) ≤ Real.log N / 100 := by
    change Real.log (Nat.lcmUpto (constructionBase N)) ≤ Real.log N / 100
    have hBaseNonneg : (0 : ℝ) ≤ constructionBase N := Nat.cast_nonneg _
    nlinarith
  have hDPos : (0 : ℝ) < constructionModulus N := by exact_mod_cast constructionModulus_pos N
  calc
    (constructionModulus N : ℝ) = Real.exp (Real.log (constructionModulus N)) := (Real.exp_log hDPos).symm
    _ ≤ Real.exp (Real.log N / 100) := Real.exp_le_exp.mpr hLogD
    _ = (N : ℝ) ^ (1 / 100 : ℝ) := by
      rw [Real.rpow_def_of_pos hNPos]
      congr 1
      ring

end Erdos319Sharp
