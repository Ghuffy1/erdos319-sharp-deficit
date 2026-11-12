import Erdos319Sharp.PrimeBlock

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem exists_primeBlockProduct_log_bound :
    ∃ U : ℝ, 0 < U ∧ ∀ X : ℕ, 1 ≤ X → primeBlockProduct X ≤ U * Real.log (2 * X) := by
  obtain ⟨U, hU, hUpper⟩ := weak_mertens_third_upper_all
  refine ⟨U, hU, ?_⟩
  intro X hX
  have hTwo : (2 : ℝ) ≤ (2 * X : ℕ) := by exact_mod_cast (show 2 ≤ 2 * X by omega)
  have h := hUpper (((2 * X : ℕ) : ℝ)) hTwo
  have hLog : 0 ≤ Real.log ((2 * X : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hClean : partial_euler_product (2 * X) ≤ U * Real.log ((2 * X : ℕ) : ℝ) := by
    simpa only [Nat.floor_natCast, Real.norm_of_nonneg
      (zero_le_one.trans partial_euler_trivial_lower_bound), Real.norm_of_nonneg hLog] using h
  change primeBlockProduct X ≤ U * Real.log ((2 * X : ℕ) : ℝ) at hClean
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hClean

theorem coarse_prime_block_expression_bound (x L ell U P : ℝ)
    (hx : 1 ≤ x) (hL : 1 ≤ L) (hEll : 1 ≤ ell)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (hUpper : P ≤ U * Real.log (2 * x)) :
    ((200 * ((2 * x) ^ (2 / 3 : ℝ) * L / ell ^ (2 / 3 : ℝ)) + 1) / x) * P ≤
      (4812 * U) * L / x ^ (1 / 6 : ℝ) := by
  have hxPos : 0 < x := by linarith
  have hLPos : 0 < L := by linarith
  have hEllPow : 1 ≤ ell ^ (2 / 3 : ℝ) := Real.one_le_rpow hEll (by norm_num)
  have hXPow : 1 ≤ x ^ (2 / 3 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hSixth : 0 < x ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hxPos _
  have hTwo23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hTwo16 : (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 / 6 : ℝ) ≤ 1)
  have hPower : (2 * x) ^ (2 / 3 : ℝ) ≤ 2 * x ^ (2 / 3 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxPos.le]
    exact mul_le_mul_of_nonneg_right hTwo23 (Real.rpow_nonneg hxPos.le _)
  have hThreshold : 200 * ((2 * x) ^ (2 / 3 : ℝ) * L / ell ^ (2 / 3 : ℝ)) ≤
      400 * x ^ (2 / 3 : ℝ) * L := by
    calc
      _ ≤ 200 * ((2 * x) ^ (2 / 3 : ℝ) * L) :=
        mul_le_mul_of_nonneg_left (div_le_self (by positivity) hEllPow) (by norm_num)
      _ ≤ 200 * ((2 * x ^ (2 / 3 : ℝ)) * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPower hLPos.le) (by norm_num)
      _ = _ := by ring
  have hOne : 1 ≤ x ^ (2 / 3 : ℝ) * L := by
    calc
      1 ≤ 1 * L := by simpa using hL
      _ ≤ x ^ (2 / 3 : ℝ) * L := mul_le_mul_of_nonneg_right hXPow hLPos.le
  have hNumerator : 200 * ((2 * x) ^ (2 / 3 : ℝ) * L / ell ^ (2 / 3 : ℝ)) + 1 ≤
      401 * x ^ (2 / 3 : ℝ) * L := by nlinarith only [hThreshold, hOne]
  have hLog : Real.log (2 * x) ≤ 12 * x ^ (1 / 6 : ℝ) := by
    have h := Real.log_le_rpow_div (by positivity : 0 ≤ 2 * x)
      (by norm_num : (0 : ℝ) < 1 / 6)
    have hp : (2 * x) ^ (1 / 6 : ℝ) ≤ 2 * x ^ (1 / 6 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxPos.le]
      exact mul_le_mul_of_nonneg_right hTwo16 hSixth.le
    linarith
  have hPUpper : P ≤ U * (12 * x ^ (1 / 6 : ℝ)) :=
    hUpper.trans (mul_le_mul_of_nonneg_left hLog hU)
  have hIdentity : x ^ (2 / 3 : ℝ) * x ^ (1 / 6 : ℝ) * x ^ (1 / 6 : ℝ) = x := by
    rw [← Real.rpow_add hxPos, ← Real.rpow_add hxPos]
    norm_num
  have hScaled := congrArg (fun t : ℝ => (4812 * U) * t) hIdentity
  calc
    _ ≤ (401 * x ^ (2 / 3 : ℝ) * L / x) * P :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hNumerator hxPos.le) hP
    _ ≤ (401 * x ^ (2 / 3 : ℝ) * L / x) * (U * (12 * x ^ (1 / 6 : ℝ))) :=
      mul_le_mul_of_nonneg_left hPUpper (by positivity)
    _ = (4812 * U) * L / x ^ (1 / 6 : ℝ) := by
      apply (eq_div_iff hSixth.ne').mpr
      field_simp [hxPos.ne']
      nlinarith only [hScaled]

/-- A deliberately coarser power majorant makes the full prime tail geometric. -/
theorem exists_uniform_prime_block_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : ℕ in atTop, ∀ (A : Finset ℕ) (X : ℕ),
      2 ≤ X → (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, X ≤ n.maxPrimeFac ∧ n.maxPrimeFac < 2 * X) →
      (reciprocalSum A : ℝ) ≤ C * Real.log q / (X : ℝ) ^ (1 / 6 : ℝ) := by
  obtain ⟨U, hU, hEuler⟩ := exists_primeBlockProduct_log_bound
  refine ⟨4812 * U, by positivity, ?_⟩
  filter_upwards [eventually_prime_block_mass_bound,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with q hBlock hL hEll
  intro A X hX hCop hFree hRange
  have hXReal : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hEulerPos : 0 ≤ primeBlockProduct X :=
    zero_le_one.trans (partial_euler_trivial_lower_bound (n := 2 * X))
  exact (hBlock A X hX hCop hFree hRange).trans
    (coarse_prime_block_expression_bound X (Real.log q) (Real.log (Real.log q)) U
      (primeBlockProduct X) hXReal hL hEll hU.le hEulerPos (hEuler X (by omega)))

end Erdos319Sharp
