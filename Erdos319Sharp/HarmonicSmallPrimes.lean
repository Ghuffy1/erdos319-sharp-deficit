import Erdos319Sharp.RankinTail

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem partial_euler_product_eq_inversePrimeProduct (N : ℕ) :
    partial_euler_product N = inversePrimeProduct N := by
  have hSets : (Finset.Icc 1 N).filter Nat.Prime = (Finset.range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp0, hpN⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  unfold partial_euler_product inversePrimeProduct primeProduct
  rw [hSets, ← Finset.prod_inv_distrib]
  simp only [one_div]

theorem eventually_small_prime_harmonic_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, 0 < n ∧ (n.maxPrimeFac : ℝ) ≤ Real.log q) →
      (reciprocalSum A : ℝ) ≤
        (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log q) := by
  have hEvent := tendsto_inversePrimeProduct_div_log.eventually
    (Iio_mem_nhds (by linarith : Real.exp Real.eulerMascheroniConstant <
      Real.exp Real.eulerMascheroniConstant + ε))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hEvent
  filter_upwards [tendsto_log_coe_at_top.eventually
    (eventually_ge_atTop (max (K : ℝ) 2))] with q hLog
  intro A hA
  have hL : (2 : ℝ) ≤ Real.log q := (le_max_right _ _).trans hLog
  have hLPos : 0 < Real.log q := by linarith
  let Y : ℕ := ⌊Real.log q⌋₊
  have hYK : K ≤ Y := (Nat.le_floor_iff hLPos.le).mpr ((le_max_left _ _).trans hLog)
  have hY : 2 ≤ Y := (Nat.le_floor_iff hLPos.le).mpr hL
  have hYR : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hLogY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hMass : (reciprocalSum A : ℝ) ≤ partial_euler_product Y := by
    rw [reciprocalSum_eq_baseline, reciprocalSum_real]
    simp only [one_div]
    apply factored_reciprocal_sum_le A ((Finset.Icc 1 Y).filter Nat.Prime)
      (fun p hp => (Finset.mem_filter.mp hp).2)
    intro n hn
    exact factoredNumbers_of_maxPrimeFac_le n Y (hA n hn).1
      ((Nat.le_floor_iff hLPos.le).mpr (hA n hn).2)
  have hProduct : partial_euler_product Y ≤
      (Real.exp Real.eulerMascheroniConstant + ε) * Real.log Y := by
    rw [partial_euler_product_eq_inversePrimeProduct]
    exact ((div_lt_iff₀ hLogY).mp (hK Y hYK)).le
  have hLogCompare : Real.log Y ≤ Real.log (Real.log q) :=
    Real.log_le_log hYR (Nat.floor_le hLPos.le)
  exact hMass.trans (hProduct.trans
    (mul_le_mul_of_nonneg_left hLogCompare (by positivity)))

end Erdos319Sharp
