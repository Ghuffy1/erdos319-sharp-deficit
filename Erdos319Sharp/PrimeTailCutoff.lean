import Erdos319Sharp.PrimeTail

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def harmonicPrimeCutoff (q : ℕ) : ℕ := ⌈(Real.log q) ^ 12⌉₊

theorem harmonicPrimeCutoff_root_lower (q : ℕ) (hL : 0 ≤ Real.log q) :
    (Real.log q) ^ 2 ≤ (harmonicPrimeCutoff q : ℝ) ^ (1 / 6 : ℝ) := by
  have hBound : (Real.log q) ^ 12 ≤ (harmonicPrimeCutoff q : ℝ) := Nat.le_ceil _
  have hPower := Real.rpow_le_rpow (pow_nonneg hL 12) hBound (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hIdentity : ((Real.log q) ^ 12) ^ (1 / 6 : ℝ) = (Real.log q) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  rwa [hIdentity] at hPower

theorem eventually_log_harmonicPrimeCutoff_bound :
    ∀ᶠ q : ℕ in atTop,
      Real.log (harmonicPrimeCutoff q : ℝ) ≤ 13 * Real.log (Real.log q) := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ))]
    with q hL
  have hLPos : 0 < Real.log q := by linarith
  have hOne : 1 ≤ (Real.log q) ^ 12 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 1 ≤ Real.log q) 12
  have hYPos : (0 : ℝ) < harmonicPrimeCutoff q := by
    exact_mod_cast Nat.ceil_pos.mpr (pow_pos hLPos 12)
  have hCeil : (harmonicPrimeCutoff q : ℝ) < (Real.log q) ^ 12 + 1 :=
    Nat.ceil_lt_add_one (pow_nonneg hLPos.le 12)
  have hYUpper : (harmonicPrimeCutoff q : ℝ) ≤ 2 * (Real.log q) ^ 12 := by linarith
  have hLogTwo : Real.log 2 ≤ Real.log (Real.log q) := Real.log_le_log (by norm_num) hL
  calc
    Real.log (harmonicPrimeCutoff q : ℝ) ≤ Real.log (2 * (Real.log q) ^ 12) :=
      Real.log_le_log hYPos hYUpper
    _ = Real.log 2 + 12 * Real.log (Real.log q) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 12 hLPos.ne'), Real.log_pow]
      norm_num
    _ ≤ 13 * Real.log (Real.log q) := by linarith

/-- The larger polynomial logarithmic cutoff gives a uniformly vanishing
tail and is sufficient for the final sharp leading constant. -/
theorem exists_vanishing_large_prime_tail_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ q : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, harmonicPrimeCutoff q ≤ n.maxPrimeFac) →
      (reciprocalSum A : ℝ) ≤ K / Real.log q := by
  obtain ⟨K, hK, hTail⟩ := exists_uniform_large_prime_tail_bound
  refine ⟨K, hK, ?_⟩
  filter_upwards [hTail,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ))]
    with q hBound hL
  intro A hCop hFree hLarge
  have hLPos : 0 < Real.log q := by linarith
  have hYReal : (2 : ℝ) ≤ harmonicPrimeCutoff q := by
    have hPow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 12
    have hCeil : (Real.log q) ^ 12 ≤ (harmonicPrimeCutoff q : ℝ) := Nat.le_ceil _
    norm_num at hPow
    linarith
  have hY : 2 ≤ harmonicPrimeCutoff q := by exact_mod_cast hYReal
  have hRoot := harmonicPrimeCutoff_root_lower q hLPos.le
  have hFirst := hBound A (harmonicPrimeCutoff q) hY hCop hFree hLarge
  calc
    (reciprocalSum A : ℝ) ≤ K * Real.log q /
        (harmonicPrimeCutoff q : ℝ) ^ (1 / 6 : ℝ) := hFirst
    _ ≤ K * Real.log q / (Real.log q) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hK.le hLPos.le) (sq_pos_of_pos hLPos) hRoot
    _ = K / Real.log q := by field_simp

theorem eventually_large_prime_tail_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, harmonicPrimeCutoff q ≤ n.maxPrimeFac) →
      (reciprocalSum A : ℝ) ≤ ε := by
  obtain ⟨K, _, hTail⟩ := exists_vanishing_large_prime_tail_bound
  have hLimit : Tendsto (fun q : ℕ => K / Real.log q) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top).const_mul K
  filter_upwards [hTail, hLimit.eventually (Iio_mem_nhds hε)] with q hBound hSmall
  intro A hCop hFree hLarge
  exact (hBound A hCop hFree hLarge).trans hSmall.le

end Erdos319Sharp
