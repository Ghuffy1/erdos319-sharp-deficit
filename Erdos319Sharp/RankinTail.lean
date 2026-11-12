import Erdos319Sharp.RankinProduct
import Erdos319Sharp.PrimeTailCutoff

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem rankin_reciprocal_term (Y n a : ℝ) (hY : 1 < Y) (hn : 0 < n)
    (hLarge : Y ^ a ≤ n) :
    1 / n ≤ Real.exp (-a) * n ^ (1 / Real.log Y - 1) := by
  have hYPos : 0 < Y := by linarith
  have hLogPos : 0 < Real.log Y := Real.log_pos hY
  have hLogs := Real.log_le_log (Real.rpow_pos_of_pos hYPos a) hLarge
  rw [Real.log_rpow hYPos] at hLogs
  have hExponent : a ≤ Real.log n * (1 / Real.log Y) := by
    have h := (le_div_iff₀ hLogPos).mpr hLogs
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  have hPower : Real.exp a ≤ n ^ (1 / Real.log Y) := by
    rw [Real.rpow_def_of_pos hn]
    exact Real.exp_le_exp.mpr hExponent
  calc
    1 / n = Real.exp (-a) * (Real.exp a / n) := by
      rw [← mul_div_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-a) * (n ^ (1 / Real.log Y) / n) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hPower hn.le) (Real.exp_nonneg _)
    _ = Real.exp (-a) * n ^ (1 / Real.log Y - 1) := by rw [Real.rpow_sub_one hn.ne']

theorem rankin_reciprocal_sum_bound (A : Finset ℕ) (Y : ℕ) (a : ℝ)
    (hY : 1 < (Y : ℝ))
    (hSmooth : ∀ n ∈ A, n ∈ Nat.factoredNumbers ((Finset.Icc 1 Y).filter Nat.Prime))
    (hLarge : ∀ n ∈ A, (Y : ℝ) ^ a ≤ n)
    (hTheta : 1 / Real.log Y < 1) :
    (reciprocalSum A : ℝ) ≤ Real.exp (-a) *
      weightedPrimeProduct ((Finset.Icc 1 Y).filter Nat.Prime) (1 / Real.log Y) := by
  have hWeighted := weighted_factored_sum_le A ((Finset.Icc 1 Y).filter Nat.Prime)
    (1 / Real.log Y) (fun p hp => (Finset.mem_filter.mp hp).2) hTheta hSmooth
  rw [reciprocalSum_eq_baseline, reciprocalSum_real]
  calc
    (∑ n ∈ A, (1 : ℝ) / n) ≤
        ∑ n ∈ A, Real.exp (-a) * (n : ℝ) ^ (1 / Real.log Y - 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (hSmooth n hn).1
      exact rankin_reciprocal_term Y n a hY hnPos (hLarge n hn)
    _ = Real.exp (-a) * (∑ n ∈ A, (n : ℝ) ^ (1 / Real.log Y - 1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hWeighted (Real.exp_nonneg _)

theorem factoredNumbers_of_maxPrimeFac_le (n Y : ℕ) (hn : 0 < n) (hMax : n.maxPrimeFac ≤ Y) :
    n ∈ Nat.factoredNumbers ((Finset.Icc 1 Y).filter Nat.Prime) := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hpn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hp.one_le, (Nat.le_maxPrimeFac hn.ne' hp hpn).trans hMax⟩, hp⟩

theorem exists_rankin_smooth_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℕ) (a : ℝ) (A : Finset ℕ),
      4 ≤ Real.log Y → (∀ n ∈ A, 0 < n ∧ n.maxPrimeFac ≤ Y) →
      (∀ n ∈ A, (Y : ℝ) ^ a ≤ n) →
      (reciprocalSum A : ℝ) ≤ C * Real.exp (-a) * Real.log Y := by
  obtain ⟨C, hC, hProduct⟩ := exists_rankin_product_bound
  refine ⟨C, hC, ?_⟩
  intro Y a A hLog hSmooth hLarge
  have hLogPos : 0 < Real.log Y := by linarith
  have hY : 1 < (Y : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg Y)).mp hLogPos
  have hTheta : 1 / Real.log Y < 1 := (div_lt_one hLogPos).mpr (by linarith)
  have h := rankin_reciprocal_sum_bound A Y a hY
    (fun n hn => factoredNumbers_of_maxPrimeFac_le n Y (hSmooth n hn).1 (hSmooth n hn).2)
    hLarge hTheta
  calc
    (reciprocalSum A : ℝ) ≤ Real.exp (-a) *
        weightedPrimeProduct ((Finset.Icc 1 Y).filter Nat.Prime) (1 / Real.log Y) := h
    _ ≤ Real.exp (-a) * (C * Real.log Y) :=
      mul_le_mul_of_nonneg_left (hProduct Y hLog) (Real.exp_nonneg _)
    _ = C * Real.exp (-a) * Real.log Y := by ring

theorem exists_rankin_tail_at_harmonic_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : ℕ in atTop, ∀ (a : ℝ) (A : Finset ℕ),
      (∀ n ∈ A, 0 < n ∧ n.maxPrimeFac ≤ harmonicPrimeCutoff q) →
      (∀ n ∈ A, (harmonicPrimeCutoff q : ℝ) ^ a ≤ n) →
      (reciprocalSum A : ℝ) ≤ C * Real.exp (-a) * Real.log (Real.log q) := by
  obtain ⟨C, hC, hRankin⟩ := exists_rankin_smooth_tail_bound
  refine ⟨13 * C, by positivity, ?_⟩
  filter_upwards [eventually_log_harmonicPrimeCutoff_bound,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with q hUpper hL hLL
  intro a A hSmooth hLarge
  have hLPos : 0 < Real.log q := by linarith
  have hLower := Real.log_le_log (pow_pos hLPos 12)
    (Nat.le_ceil ((Real.log q) ^ 12))
  rw [Real.log_pow] at hLower
  have hLogY : 4 ≤ Real.log (harmonicPrimeCutoff q : ℝ) := by
    change (12 : ℝ) * Real.log (Real.log q) ≤ Real.log (harmonicPrimeCutoff q : ℝ) at hLower
    linarith
  calc
    (reciprocalSum A : ℝ) ≤ C * Real.exp (-a) * Real.log (harmonicPrimeCutoff q : ℝ) :=
      hRankin (harmonicPrimeCutoff q) a A hLogY hSmooth hLarge
    _ ≤ C * Real.exp (-a) * (13 * Real.log (Real.log q)) :=
      mul_le_mul_of_nonneg_left hUpper (mul_nonneg hC.le (Real.exp_nonneg _))
    _ = (13 * C) * Real.exp (-a) * Real.log (Real.log q) := by ring

end Erdos319Sharp
