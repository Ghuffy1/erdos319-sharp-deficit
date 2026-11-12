import Erdos319Sharp.PrimeBlockEstimates

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def primeTailRatio : ℝ := (2 : ℝ) ^ (-(1 / 6 : ℝ))

theorem primeTailRatio_pos : 0 < primeTailRatio := Real.rpow_pos_of_pos (by norm_num) _

theorem primeTailRatio_lt_one : primeTailRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem reciprocal_dyadic_sixth (Y j : ℕ) (hY : 0 < Y) :
    (1 : ℝ) / ((Y * 2 ^ j : ℕ) : ℝ) ^ (1 / 6 : ℝ) =
      (1 / (Y : ℝ) ^ (1 / 6 : ℝ)) * primeTailRatio ^ j := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.mul_rpow (Nat.cast_nonneg Y) (by positivity),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) (1 / 6 : ℝ) j]
  simp only [primeTailRatio, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    one_div, mul_inv, inv_pow]

/-- Summation of the prime blocks needs only a geometric series once each
block has an inverse-sixth-power majorant. -/
theorem prime_tail_from_block_bounds (A : Finset ℕ) (Y : ℕ) (C : ℝ)
    (hY : 2 ≤ Y) (hC : 0 ≤ C) (hLarge : ∀ n ∈ A, Y ≤ n.maxPrimeFac)
    (hBound : ∀ (B : Finset ℕ), B ⊆ A → ∀ X : ℕ, 2 ≤ X →
      (∀ n ∈ B, X ≤ n.maxPrimeFac ∧ n.maxPrimeFac < 2 * X) →
      (reciprocalSum B : ℝ) ≤ C / (X : ℝ) ^ (1 / 6 : ℝ)) :
    (reciprocalSum A : ℝ) ≤
      C / ((Y : ℝ) ^ (1 / 6 : ℝ) * (1 - primeTailRatio)) := by
  classical
  have hYPos : 0 < Y := by omega
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hYPos
  have hBins : ∀ n : ℕ, ∃ j : ℕ, n ∈ A →
      Y * 2 ^ j ≤ n.maxPrimeFac ∧ n.maxPrimeFac < 2 * (Y * 2 ^ j) := by
    intro n
    by_cases hn : n ∈ A
    · have hStart : (1 : ℝ) ≤ (n.maxPrimeFac : ℝ) / Y :=
        (le_div_iff₀ hYR).mpr (by
          simpa only [one_mul] using (show (Y : ℝ) ≤ n.maxPrimeFac by exact_mod_cast hLarge n hn))
      obtain ⟨j, hjLo, hjHi⟩ := exists_nat_pow_near hStart (by norm_num : (1 : ℝ) < 2)
      refine ⟨j, fun _ => ⟨?_, ?_⟩⟩
      · have h := (le_div_iff₀ hYR).mp hjLo
        have hNat : 2 ^ j * Y ≤ n.maxPrimeFac := by exact_mod_cast h
        simpa only [Nat.mul_comm] using hNat
      · have h := (div_lt_iff₀ hYR).mp hjHi
        have hNat : n.maxPrimeFac < 2 ^ (j + 1) * Y := by exact_mod_cast h
        simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hNat
    · exact ⟨0, fun h => False.elim (hn h)⟩
  choose bin hBin using hBins
  let J := A.image bin
  have hSplit : (∑ n ∈ A, (n : ℝ)⁻¹) =
      ∑ j ∈ J, ∑ n ∈ A.filter (fun n => bin n = j), (n : ℝ)⁻¹ := by
    exact (Finset.sum_fiberwise_of_maps_to
      (fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩) _).symm
  have hEach : ∀ j ∈ J, (∑ n ∈ A.filter (fun n => bin n = j), (n : ℝ)⁻¹) ≤
      C / ((Y * 2 ^ j : ℕ) : ℝ) ^ (1 / 6 : ℝ) := by
    intro j hj
    have hX : 2 ≤ Y * 2 ^ j := by
      have hPow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
      have h := Nat.mul_le_mul_left Y hPow
      omega
    have h := hBound (A.filter (fun n => bin n = j)) (Finset.filter_subset _ _) (Y * 2 ^ j) hX
      (by
        intro n hn
        obtain ⟨hnA, hnj⟩ := Finset.mem_filter.mp hn
        simpa only [hnj] using hBin n hnA)
    simpa only [reciprocalSum_eq_baseline, reciprocalSum_real, one_div] using h
  have hGeom : (∑ j ∈ J, primeTailRatio ^ j) ≤ (1 - primeTailRatio)⁻¹ :=
    sum_le_hasSum J (fun j _ => pow_nonneg primeTailRatio_pos.le j)
      (hasSum_geometric_of_lt_one primeTailRatio_pos.le primeTailRatio_lt_one)
  rw [reciprocalSum_eq_baseline, reciprocalSum_real]
  simp only [one_div]
  calc
    _ = ∑ j ∈ J, ∑ n ∈ A.filter (fun n => bin n = j), (n : ℝ)⁻¹ := hSplit
    _ ≤ ∑ j ∈ J, C / ((Y * 2 ^ j : ℕ) : ℝ) ^ (1 / 6 : ℝ) :=
      Finset.sum_le_sum hEach
    _ = (C / (Y : ℝ) ^ (1 / 6 : ℝ)) * ∑ j ∈ J, primeTailRatio ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have h := congrArg (fun t : ℝ => C * t) (reciprocal_dyadic_sixth Y j hYPos)
      simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h
    _ ≤ (C / (Y : ℝ) ^ (1 / 6 : ℝ)) * (1 - primeTailRatio)⁻¹ :=
      mul_le_mul_of_nonneg_left hGeom (div_nonneg hC (Real.rpow_nonneg hYR.le _))
    _ = _ := by simp only [div_eq_mul_inv, mul_inv, mul_assoc, one_mul]

theorem exists_uniform_large_prime_tail_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ q : ℕ in atTop, ∀ (A : Finset ℕ) (Y : ℕ),
      2 ≤ Y → (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, Y ≤ n.maxPrimeFac) →
      (reciprocalSum A : ℝ) ≤ K * Real.log q / (Y : ℝ) ^ (1 / 6 : ℝ) := by
  obtain ⟨C, hC, hBlocks⟩ := exists_uniform_prime_block_power_bound
  refine ⟨C / (1 - primeTailRatio), div_pos hC (sub_pos.mpr primeTailRatio_lt_one), ?_⟩
  filter_upwards [hBlocks, tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with q hBlock hL
  intro A Y hY hCop hFree hLarge
  have h := prime_tail_from_block_bounds A Y (C * Real.log q) hY
    (mul_nonneg hC.le (by linarith)) hLarge (by
      intro B hBA X hX hRange
      exact hBlock B X hX (fun n hn => hCop n (hBA hn)) (ZeroSumFree.mono hFree hBA) hRange)
  convert h using 1 <;> simp only [div_eq_mul_inv, mul_inv] <;> ring

end Erdos319Sharp
