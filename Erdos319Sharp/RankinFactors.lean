import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

def rankinGap : ℝ := 1 - (2 : ℝ) ^ (-(3 / 4 : ℝ))

def weightedPrimeProduct (P : Finset ℕ) (θ : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ) ^ (θ - 1))⁻¹

theorem rankinGap_pos : 0 < rankinGap := by
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

theorem rankin_factor_gap (x θ : ℝ) (hx : 2 ≤ x) (hθ : θ ≤ 1 / 4) :
    rankinGap ≤ 1 - x ^ (θ - 1) := by
  have hPower : x ^ (θ - 1) ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
    calc
      x ^ (θ - 1) ≤ x ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
  dsimp [rankinGap]
  linarith

theorem rankin_power_increment (x θ : ℝ) (hx : 0 < x)
    (hθ : 0 ≤ θ) (hLog : 0 ≤ Real.log x) (hScale : θ * Real.log x ≤ 1) :
    x ^ θ - 1 ≤ Real.exp 1 * θ * Real.log x := by
  have hz : 0 ≤ θ * Real.log x := mul_nonneg hθ hLog
  calc
    x ^ θ - 1 = Real.exp (θ * Real.log x) - 1 := by rw [Real.rpow_def_of_pos hx, mul_comm]
    _ ≤ (θ * Real.log x) * Real.exp (θ * Real.log x) := exp_sub_one_le_mul_exp _
    _ ≤ (θ * Real.log x) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hScale) hz
    _ = _ := by ring

theorem rankin_euler_factor_bound (x θ : ℝ) (hx : 2 ≤ x)
    (hθ : 0 ≤ θ) (hθUpper : θ ≤ 1 / 4) (hScale : θ * Real.log x ≤ 1) :
    (1 - x ^ (θ - 1))⁻¹ ≤
      (1 - x⁻¹)⁻¹ * Real.exp ((Real.exp 1 / rankinGap) * θ * Real.log x / x) := by
  have hxPos : 0 < x := by linarith
  have hLog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hGap := rankin_factor_gap x θ hx hθUpper
  have hDen : 0 < 1 - x ^ (θ - 1) := rankinGap_pos.trans_le hGap
  have hPlain : 0 < 1 - x⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  let E := (Real.exp 1 / rankinGap) * θ * Real.log x / x
  have hE : 0 ≤ E := by
    exact div_nonneg (mul_nonneg (mul_nonneg
      (div_nonneg (Real.exp_nonneg 1) rankinGap_pos.le) hθ) hLog) hxPos.le
  have hPower := rankin_power_increment x θ hxPos hθ hLog hScale
  have hDifference : x ^ (θ - 1) - x⁻¹ ≤ rankinGap * E := by
    rw [Real.rpow_sub_one hxPos.ne']
    have h := div_le_div_of_nonneg_right hPower hxPos.le
    have hLeft : x ^ θ / x - x⁻¹ = (x ^ θ - 1) / x := by ring
    rw [hLeft]
    have hRight : Real.exp 1 * θ * Real.log x / x = rankinGap * E := by
      dsimp [E]
      field_simp [rankinGap_pos.ne']
    rwa [hRight] at h
  have hIncrement : (x ^ (θ - 1) - x⁻¹) / (1 - x ^ (θ - 1)) ≤ E := by
    apply (div_le_iff₀ hDen).mpr
    exact hDifference.trans (by nlinarith only [mul_le_mul_of_nonneg_right hGap hE])
  have hRatioIdentity : (1 - x⁻¹) / (1 - x ^ (θ - 1)) =
      1 + (x ^ (θ - 1) - x⁻¹) / (1 - x ^ (θ - 1)) := by
    field_simp [hDen.ne']
    ring
  have hRatio : (1 - x⁻¹) / (1 - x ^ (θ - 1)) ≤ Real.exp E := by
    rw [hRatioIdentity]
    calc
      _ ≤ 1 + E := by linarith only [hIncrement]
      _ ≤ Real.exp E := by linarith only [Real.add_one_le_exp E]
  calc
    (1 - x ^ (θ - 1))⁻¹ = (1 - x⁻¹)⁻¹ * ((1 - x⁻¹) / (1 - x ^ (θ - 1))) := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hPlain.ne', one_mul]
    _ ≤ (1 - x⁻¹)⁻¹ * Real.exp E :=
      mul_le_mul_of_nonneg_left hRatio (inv_nonneg.mpr hPlain.le)

theorem weightedPrimeProduct_le_comparison (P : Finset ℕ) (θ : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hθ : 0 ≤ θ) (hθUpper : θ ≤ 1 / 4)
    (hScale : ∀ p ∈ P, θ * Real.log p ≤ 1) :
    weightedPrimeProduct P θ ≤ (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) *
      Real.exp ((Real.exp 1 / rankinGap) * θ * ∑ p ∈ P, Real.log p / p) := by
  have hEach : ∀ p ∈ P, (1 - (p : ℝ) ^ (θ - 1))⁻¹ ≤
      (1 - (p : ℝ)⁻¹)⁻¹ * Real.exp ((Real.exp 1 / rankinGap) * θ * Real.log p / p) := by
    intro p hp
    exact rankin_euler_factor_bound p θ (by exact_mod_cast (hP p hp).two_le)
      hθ hθUpper (hScale p hp)
  calc
    weightedPrimeProduct P θ ≤ ∏ p ∈ P, ((1 - (p : ℝ)⁻¹)⁻¹ *
        Real.exp ((Real.exp 1 / rankinGap) * θ * Real.log p / p)) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have h := rankin_factor_gap p θ (by exact_mod_cast (hP p hp).two_le) hθUpper
        exact inv_nonneg.mpr (rankinGap_pos.le.trans h)
      · exact hEach
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end Erdos319Sharp
