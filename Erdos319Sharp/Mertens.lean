import Salt.Mertens.Third

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def primeProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

def inversePrimeProduct (N : ℕ) : ℝ := (primeProduct N)⁻¹

theorem primeProduct_pos (N : ℕ) : 0 < primeProduct N := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1)

theorem tendsto_primeProduct_mul_log :
    Tendsto (fun N : ℕ => primeProduct N * Real.log (N : ℝ)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  obtain ⟨C, _, hbound⟩ := Salt.Mertens.mertens_third
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror : Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hlog) :
        Tendsto (fun N : ℕ => C * (Real.log (N : ℝ))⁻¹) atTop (𝓝 (C * 0)))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hsmall := (tendsto_order.mp herror).2
      (Real.exp (-Real.eulerMascheroniConstant) - a) (by linarith)
    filter_upwards [eventually_ge_atTop (3 : ℕ), hsmall] with N hN hsmallN
    have hb := (abs_le.mp (hbound N hN)).1
    change -(C / Real.log (N : ℝ)) ≤
      primeProduct N * Real.log (N : ℝ) - Real.exp (-Real.eulerMascheroniConstant) at hb
    linarith
  · intro b hb
    have hsmall := (tendsto_order.mp herror).2
      (b - Real.exp (-Real.eulerMascheroniConstant)) (by linarith)
    filter_upwards [eventually_ge_atTop (3 : ℕ), hsmall] with N hN hsmallN
    have hupper := (abs_le.mp (hbound N hN)).2
    change primeProduct N * Real.log (N : ℝ) -
      Real.exp (-Real.eulerMascheroniConstant) ≤ C / Real.log (N : ℝ) at hupper
    linarith

theorem tendsto_inversePrimeProduct_div_log :
    Tendsto (fun N : ℕ => inversePrimeProduct N / Real.log (N : ℝ)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have h := tendsto_primeProduct_mul_log.inv₀ (Real.exp_ne_zero _)
  simpa [inversePrimeProduct, div_eq_mul_inv, mul_inv, Real.exp_neg, mul_comm] using h

end Erdos319Sharp
