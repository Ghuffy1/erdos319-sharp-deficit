import Erdos319Sharp.Baseline

set_option autoImplicit false

noncomputable section

namespace Erdos319Sharp

theorem minority_side_bound (N x y d E M t : ℝ)
    (hx : 0 ≤ x) (hxt : x ≤ t) (ht : t < 1)
    (hError : 0 ≤ d + E) (hSide : M ≤ N * x + E)
    (hMixed : N * (1 - x) * (1 - y) ≤ d + E) :
    M ≤ N * (x * y) + (t / (1 - t)) * (d + E) + E := by
  have hxOne : x < 1 := hxt.trans_lt ht
  have hDenX : 0 < 1 - x := sub_pos.mpr hxOne
  have hDenT : 0 < 1 - t := sub_pos.mpr ht
  have hPart : N * x * (1 - y) ≤ (x / (1 - x)) * (d + E) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hDenX).mpr
    have h := mul_le_mul_of_nonneg_left hMixed hx
    nlinarith only [h]
  have hRatio : x / (1 - x) ≤ t / (1 - t) := by
    apply (div_le_div_iff₀ hDenX hDenT).mpr
    nlinarith only [hxt]
  calc
    M ≤ N * x + E := hSide
    _ = N * (x * y) + N * x * (1 - y) + E := by ring
    _ ≤ N * (x * y) + (x / (1 - x)) * (d + E) + E := by linarith only [hPart]
    _ ≤ N * (x * y) + (t / (1 - t)) * (d + E) + E := by
      have h := mul_le_mul_of_nonneg_right hRatio hError
      linarith only [h]

theorem minority_minimum_bound (N x y d E P M : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hProduct : x * y < 1)
    (hError : 0 ≤ d + E) (hPos : P ≤ N * y + E) (hNeg : M ≤ N * x + E)
    (hMixed : N * (1 - x) * (1 - y) ≤ d + E) :
    min P M ≤ N * (x * y) +
      (Real.sqrt (x * y) / (1 - Real.sqrt (x * y))) * (d + E) + E := by
  have ht : Real.sqrt (x * y) < 1 := by
    simpa using Real.sqrt_lt_sqrt (mul_nonneg hx hy) hProduct
  by_cases hxy : x ≤ y
  · have hSquare : x ^ 2 ≤ x * y := by
      have h := mul_le_mul_of_nonneg_left hxy hx
      nlinarith only [h]
    have hxt : x ≤ Real.sqrt (x * y) := by
      simpa only [Real.sqrt_sq hx] using Real.sqrt_le_sqrt hSquare
    exact (min_le_right P M).trans
      (minority_side_bound N x y d E M (Real.sqrt (x * y)) hx hxt ht hError hNeg hMixed)
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hSquare : y ^ 2 ≤ x * y := by
      have h := mul_le_mul_of_nonneg_left hyx hy
      nlinarith only [h]
    have hyt : y ≤ Real.sqrt (x * y) := by
      simpa only [Real.sqrt_sq hy] using Real.sqrt_le_sqrt hSquare
    have hSwap : N * (1 - y) * (1 - x) ≤ d + E := by nlinarith only [hMixed]
    have h := minority_side_bound N y x d E P (Real.sqrt (x * y)) hy hyt ht hError hPos hSwap
    exact (min_le_left P M).trans (by simpa only [mul_comm y x] using h)

end Erdos319Sharp
