import Erdos319Sharp.LocalizationPrimeBands

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def packetDensity (N : ℕ) : ℝ := (Real.log N) ^ (-7 / 25 : ℝ)

theorem packetDensity_pos {N : ℕ} (hL : 0 < Real.log N) : 0 < packetDensity N :=
  Real.rpow_pos_of_pos hL _

theorem eventually_euler_ratio_power_bound :
    ∀ᶠ N : ℕ in atTop,
      4 * (partial_euler_product N / partial_euler_product (localizationRoughBound N)) ≤
        (Real.log N) ^ (21 / 100 : ℝ) := by
  obtain ⟨C, hC, hRatio⟩ := exists_euler_ratio_log_bound
  have hSmall := (tendsto_stretchedExponent (1 / 100) 2 (16 * C)
    (by norm_num) (by positivity)).eventually (eventually_ge_atTop (1 : ℝ))
  have hGrowth := (tendsto_localizationPower_div_loglog_pow 2).eventually
    (eventually_ge_atTop (4 * Real.log 2))
  filter_upwards [hSmall, hGrowth, eventually_localizationRoughBound_le,
    tendsto_localizationRoughBound.eventually (eventually_ge_atTop 2),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hSmallN hGrowthN hYN hYTwo hL hLL
  have hLLPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le zero_lt_one hLL
  have hU : 0 < localizationPower N := Real.rpow_pos_of_pos hL _
  have hGrowth' : 4 * Real.log 2 * (Real.log (Real.log N)) ^ 2 ≤ localizationPower N :=
    (le_div_iff₀ (pow_pos hLLPos 2)).mp hGrowthN
  have hYLower := (localizationRough_log_bounds N hLL hGrowth').1
  have hLogY : 0 < Real.log (localizationRoughBound N) := (by positivity :
    (0 : ℝ) < localizationPower N / (4 * (Real.log (Real.log N)) ^ 2)).trans_le hYLower
  let R := partial_euler_product N / partial_euler_product (localizationRoughBound N)
  have hR : 0 < R := div_pos
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
  have hUpper : R * Real.log (localizationRoughBound N) ≤ C * Real.log N :=
    (le_div_iff₀ hLogY).mp (hRatio N _ hYTwo hYN)
  have hScaled : R * localizationPower N ≤
      (C * Real.log N) * (4 * (Real.log (Real.log N)) ^ 2) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (Real.log (Real.log N)) ^ 2)).mp
    simpa only [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hYLower hR.le).trans hUpper
  change 1 ≤ (Real.log N) ^ (1 / 100 : ℝ) /
    (16 * C * (Real.log (Real.log N)) ^ 2) at hSmallN
  have hSmall' : 16 * C * (Real.log (Real.log N)) ^ 2 ≤
      (Real.log N) ^ (1 / 100 : ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ (by positivity)).mp hSmallN
  have hPowers : Real.log N * (Real.log N) ^ (1 / 100 : ℝ) =
      (Real.log N) ^ (21 / 100 : ℝ) * localizationPower N := by
    unfold localizationPower
    calc
      Real.log N * (Real.log N) ^ (1 / 100 : ℝ) =
          (Real.log N) ^ (1 : ℝ) * (Real.log N) ^ (1 / 100 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log N) ^ ((1 : ℝ) + 1 / 100) := (Real.rpow_add hL _ _).symm
      _ = (Real.log N) ^ ((21 / 100 : ℝ) + 4 / 5) := by congr 1 <;> norm_num
      _ = (Real.log N) ^ (21 / 100 : ℝ) * (Real.log N) ^ (4 / 5 : ℝ) :=
        Real.rpow_add hL _ _
  have hCompare : (4 * R) * localizationPower N ≤
      (Real.log N) ^ (21 / 100 : ℝ) * localizationPower N := by
    calc
      (4 * R) * localizationPower N = 4 * (R * localizationPower N) := by ring
      _ ≤ 4 * ((C * Real.log N) * (4 * (Real.log (Real.log N)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hScaled (by norm_num)
      _ = Real.log N * (16 * C * (Real.log (Real.log N)) ^ 2) := by ring
      _ ≤ Real.log N * (Real.log N) ^ (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hSmall' hL.le
      _ = (Real.log N) ^ (21 / 100 : ℝ) * localizationPower N := hPowers
  exact (mul_le_mul_iff_of_pos_right hU).mp hCompare

theorem packet_density_from_lower_bounds {N : ℕ} {c η : ℝ} (hL : 0 < Real.log N)
    (hc : (Real.log N) ^ (-3 / 100 : ℝ) ≤ c)
    (hη : (Real.log N) ^ (-1 / 25 : ℝ) ≤ η)
    (hRatio : 4 * (partial_euler_product N /
      partial_euler_product (localizationRoughBound N)) ≤ (Real.log N) ^ (21 / 100 : ℝ)) :
    packetDensity N ≤ c * (η / (4 * (partial_euler_product N /
      partial_euler_product (localizationRoughBound N)))) := by
  let R := partial_euler_product N / partial_euler_product (localizationRoughBound N)
  have hR : 0 < R := div_pos
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
  have hcPos : 0 < c := (Real.rpow_pos_of_pos hL _).trans_le hc
  have hProduct : (Real.log N) ^ (-7 / 100 : ℝ) ≤ c * η := by
    calc
      (Real.log N) ^ (-7 / 100 : ℝ) =
          (Real.log N) ^ (-3 / 100 : ℝ) * (Real.log N) ^ (-1 / 25 : ℝ) := by
        rw [← Real.rpow_add hL]
        norm_num
      _ ≤ c * η := mul_le_mul hc hη (by positivity) hcPos.le
  have hCompare : packetDensity N * (4 * R) ≤ c * η := by
    calc
      packetDensity N * (4 * R) ≤ packetDensity N * (Real.log N) ^ (21 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hRatio (packetDensity_pos hL).le
      _ = (Real.log N) ^ (-7 / 100 : ℝ) := by
        unfold packetDensity
        rw [← Real.rpow_add hL]
        norm_num
      _ ≤ c * η := hProduct
  have hResult := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * R)).mpr hCompare
  simpa only [mul_div_assoc] using hResult

end Erdos319Sharp
