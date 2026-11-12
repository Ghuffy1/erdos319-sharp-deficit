import Erdos319Sharp.BoundaryScales
import Erdos319Sharp.QuantitativeCompletion

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_smoothCutoff_le_boundary_div_log :
    ∀ᶠ N : ℕ in atTop, smoothCutoff 6 N ≤
      (constructionBoundary N : ℝ) / (Real.log (constructionBoundary N)) ^ 14 := by
  have hTail := (tendsto_log_pow_mul_exp_neg_localizationPower 15 6 (by norm_num)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hMass := tendsto_constructionMass_div_log.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hTail, hMass, eventually_constructionBoundary_lower,
    tendsto_constructionBoundary.eventually (eventually_ge_atTop (2 : ℕ)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hTailN hMassN hBoundary hB hLog
  have hLPos : 0 < Real.log N := lt_of_lt_of_le (by norm_num) hLog
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  have hMassLe : constructionMass N ≤ Real.log N := (div_lt_one hLPos).mp hMassN |>.le
  have hBPos : (0 : ℝ) < constructionBoundary N := by exact_mod_cast (by omega : 0 < constructionBoundary N)
  have hBOne : (1 : ℝ) < constructionBoundary N := by exact_mod_cast (by omega : 1 < constructionBoundary N)
  have hLogBPos := Real.log_pos hBOne
  have hLogLe : Real.log (constructionBoundary N) ≤ Real.log N :=
    Real.log_le_log hBPos (by exact_mod_cast constructionBoundary_le N)
  have hProduct : 2 * constructionMass N * (Real.log N) ^ 14 *
      Real.exp (-6 * localizationPower N) ≤ 1 := by
    calc
      _ ≤ 2 * Real.log N * (Real.log N) ^ 14 * Real.exp (-6 * localizationPower N) := by
        gcongr
      _ = 2 * ((Real.log N) ^ 15 * Real.exp (-6 * localizationPower N)) := by ring
      _ ≤ 1 := by linarith
  have hDenPos : 0 < 2 * constructionMass N * (Real.log N) ^ 14 := by positivity
  have hExpBound : Real.exp (-6 * localizationPower N) ≤
      1 / (2 * constructionMass N * (Real.log N) ^ 14) := by
    apply (le_div_iff₀ hDenPos).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hProduct
  calc
    smoothCutoff 6 N = (N : ℝ) * Real.exp (-6 * localizationPower N) := rfl
    _ ≤ (N : ℝ) * (1 / (2 * constructionMass N * (Real.log N) ^ 14)) :=
      mul_le_mul_of_nonneg_left hExpBound (Nat.cast_nonneg N)
    _ = ((N : ℝ) / (2 * constructionMass N)) / (Real.log N) ^ 14 := by ring
    _ ≤ (constructionBoundary N : ℝ) / (Real.log N) ^ 14 :=
      div_le_div_of_nonneg_right hBoundary (pow_nonneg hLPos.le _)
    _ ≤ (constructionBoundary N : ℝ) / (Real.log (constructionBoundary N)) ^ 14 := by
      apply (div_le_div_iff₀ (pow_pos hLPos _) (pow_pos hLogBPos _)).mpr
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLogBPos.le hLogLe 14) (Nat.cast_nonneg _)

theorem prime_mem_of_dvd_primeProduct (P : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hPrime : ∀ q ∈ P, q.Prime) (hDiv : p ∣ P.prod id) : p ∈ P := by
  classical
  revert hPrime hDiv
  induction P using Finset.induction_on with
  | empty =>
      intro _ hDiv
      simp only [Finset.prod_empty] at hDiv
      exact False.elim (hp.ne_one (Nat.dvd_one.mp hDiv))
  | @insert q P hq ih =>
      intro hPrime hDiv
      rw [Finset.prod_insert hq, id_eq] at hDiv
      rcases hp.dvd_mul.mp hDiv with hqDiv | hPDiv
      · rcases (Nat.dvd_prime (hPrime q (Finset.mem_insert_self _ _))).mp hqDiv with hOne | hEq
        · exact False.elim (hp.ne_one hOne)
        · exact Finset.mem_insert.mpr (Or.inl hEq)
      · exact Finset.mem_insert_of_mem (ih
          (fun q hq => hPrime q (Finset.mem_insert_of_mem hq)) hPDiv)

theorem eventually_construction_completion_primes (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ, P ⊆ constructionPrimeBand N →
      ∀ p : ℕ, p.Prime → p ∣ P.prod id →
        C < p ∧ (Real.log (constructionBoundary N)) ^ 13 < (p : ℝ) := by
  have hConstant := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (C : ℝ))
  have hLogPower := (tendsto_log_pow_div_nat_rpow 13 (1 / 20) (by norm_num)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hConstant, hLogPower, eventually_ge_atTop (1 : ℕ),
    tendsto_constructionBoundary.eventually (eventually_ge_atTop (1 : ℕ))]
    with N hConstantN hLogPowerN hN hB P hP p hp hDiv
  have hMem := prime_mem_of_dvd_primeProduct P p hp
    (fun q hq => (mem_constructionPrimeBand.mp (hP hq)).1) hDiv
  have hPrimeBound := (constructionPrimeBand_power_bounds (hP hMem)).1
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBPos : (0 : ℝ) < constructionBoundary N := by exact_mod_cast (by omega : 0 < constructionBoundary N)
  have hLogB : 0 ≤ Real.log (constructionBoundary N) :=
    Real.log_nonneg (by exact_mod_cast hB)
  have hLogLe : Real.log (constructionBoundary N) ≤ Real.log N :=
    Real.log_le_log hBPos (by exact_mod_cast constructionBoundary_le N)
  have hPower : (Real.log N) ^ 13 < (N : ℝ) ^ (1 / 20 : ℝ) :=
    (div_lt_one (Real.rpow_pos_of_pos hNPos _)).mp hLogPowerN
  exact ⟨by exact_mod_cast hConstantN.trans hPrimeBound,
    (pow_le_pow_left₀ hLogB hLogLe 13).trans_lt (hPower.trans hPrimeBound)⟩

end Erdos319Sharp
