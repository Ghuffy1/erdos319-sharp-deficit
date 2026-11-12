import Erdos319Sharp.Mertens

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / p

theorem exists_primeReciprocalSum_centered_limit :
    ∃ M : ℝ, Tendsto (fun N : ℕ => primeReciprocalSum N - Real.log (Real.log N))
      atTop (𝓝 M) := by
  obtain ⟨M, C, _, hBound⟩ := Salt.Mertens.mertens_second_sharp
  have hLog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hError : Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hLog) :
        Tendsto (fun N : ℕ => C * (Real.log (N : ℝ))⁻¹) atTop (𝓝 (C * 0)))
  refine ⟨M, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    have hSmall := (tendsto_order.mp hError).2 (M - a) (by linarith)
    filter_upwards [eventually_ge_atTop (2 : ℕ), hSmall] with N hN hSmallN
    have hLower := (abs_le.mp (hBound N hN)).1
    change -(C / Real.log (N : ℝ)) ≤
      primeReciprocalSum N - (Real.log (Real.log N) + M) at hLower
    linarith
  · intro b hb
    have hSmall := (tendsto_order.mp hError).2 (b - M) (by linarith)
    filter_upwards [eventually_ge_atTop (2 : ℕ), hSmall] with N hN hSmallN
    have hUpper := (abs_le.mp (hBound N hN)).2
    change primeReciprocalSum N - (Real.log (Real.log N) + M) ≤
      C / Real.log (N : ℝ) at hUpper
    linarith

/-- Reciprocal mass in a growing prime band is determined by its logarithmic
endpoint ratio. This will supply the correction-prime pools. -/
theorem primeReciprocalBand_limit (a b : ℕ → ℕ) (value : ℝ)
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hLogs : Tendsto (fun N : ℕ => Real.log (Real.log (b N)) -
      Real.log (Real.log (a N))) atTop (𝓝 value)) :
    Tendsto (fun N : ℕ => primeReciprocalSum (b N) - primeReciprocalSum (a N))
      atTop (𝓝 value) := by
  obtain ⟨M, hM⟩ := exists_primeReciprocalSum_centered_limit
  have hCentered := (hM.comp hb).sub (hM.comp ha)
  have hLimit : Tendsto (fun N : ℕ =>
      (primeReciprocalSum (b N) - Real.log (Real.log (b N))) -
        (primeReciprocalSum (a N) - Real.log (Real.log (a N))) +
        (Real.log (Real.log (b N)) - Real.log (Real.log (a N))))
      atTop (𝓝 value) := by
    simpa only [Function.comp_def, sub_self, zero_add] using hCentered.add hLogs
  apply hLimit.congr'
  filter_upwards with N using by ring

end Erdos319Sharp
