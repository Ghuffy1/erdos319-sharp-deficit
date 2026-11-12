import Erdos319Sharp.UniformCompletion

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_quantitative_rational_completion (η : ℝ) (hη : 0 < η) :
    ∃ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (r : ℚ) (G : ℕ),
      η ≤ (r : ℝ) → (r : ℝ) ≤ 2 → r.den.Coprime G →
      (primaryHeight r.den : ℝ) ≤ (N : ℝ) / (Real.log N) ^ 14 →
      (∀ p : ℕ, p.Prime → p ∣ G → C < p ∧ (Real.log N) ^ 13 < (p : ℝ)) →
      ∃ A ⊆ Finset.Icc 1 N, (∀ n ∈ A, n.Coprime G) ∧ reciprocalSum A = r := by
  obtain ⟨C, hComplete⟩ := exists_uniform_rational_completion η hη
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop C,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hCN hLogN hN
  intro r G hrLow hrHigh hrCop hHeight hPrimes
  let H := primaryHeight r.den
  let B := ⌊Real.log H⌋₊ ^ 13
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hLogPos : 0 < Real.log N := zero_lt_one.trans_le hLogN
  have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast one_le_primaryHeight r.den
  have hHPos : (0 : ℝ) < H := zero_lt_one.trans_le hHOne
  have hHBound : (H : ℝ) ≤ N := hHeight.trans
    (div_le_self hNReal.le (one_le_pow₀ hLogN))
  have hLogH : Real.log H ≤ Real.log N := Real.log_le_log hHPos hHBound
  have hFloor : (⌊Real.log H⌋₊ : ℝ) ≤ Real.log N :=
    (Nat.floor_le (Real.log_nonneg hHOne)).trans hLogH
  have hB : (B : ℝ) ≤ (Real.log N) ^ 13 := by
    simpa only [B, Nat.cast_pow] using
      pow_le_pow_left₀ (Nat.cast_nonneg ⌊Real.log H⌋₊) hFloor 13
  obtain ⟨A, hSum, hA⟩ := hComplete r G hrLow hrHigh hrCop (by
    intro p hp hpG
    have h := hPrimes p hp hpG
    have hBp : B < p := by exact_mod_cast hB.trans_lt h.2
    exact max_lt_iff.mpr ⟨h.1, hBp⟩)
  have hProduct : H * B ≤ N := by
    have hProductR : (H : ℝ) * B ≤ (N : ℝ) := by
      calc
        (H : ℝ) * B ≤ ((N : ℝ) / (Real.log N) ^ 14) * (Real.log N) ^ 13 :=
          mul_le_mul hHeight hB (Nat.cast_nonneg B) (by positivity)
        _ = (N : ℝ) / Real.log N := by field_simp
        _ ≤ N := div_le_self hNReal.le hLogN
    exact_mod_cast hProductR
  refine ⟨A, ?_, fun n hn => (hA n hn).2.1, hSum⟩
  intro n hn
  have h := hA n hn
  exact Finset.mem_Icc.mpr ⟨h.1, h.2.2.trans (max_le hCN hProduct)⟩

end Erdos319Sharp
