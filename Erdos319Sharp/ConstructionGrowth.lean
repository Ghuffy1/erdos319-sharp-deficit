import Erdos319Sharp.ConstructionPrimeBand
import Erdos319Sharp.Uniform

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem tendsto_constructionMass : Tendsto constructionMass atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (Real.exp_pos Real.eulerMascheroniConstant)
    tendsto_constructionMass_ratio tendsto_log_log_coe_at_top
  apply h.congr'
  filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
    with N hLog
  exact div_mul_cancel₀ _ hLog.ne'

theorem tendsto_constructionMass_div_log :
    Tendsto (fun N : ℕ => constructionMass N / Real.log N) atTop (𝓝 0) := by
  have hSmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_coe_at_top
  have h := tendsto_constructionMass_ratio.mul hSmall
  apply (show Tendsto (fun N : ℕ =>
      (constructionMass N / Real.log (Real.log N)) *
        (Real.log (Real.log N) / Real.log N)) atTop (𝓝 0) from
    by simpa only [Function.comp_def, id_eq, mul_zero] using h).congr'
  filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLoglog hLog
  field_simp [hLoglog.ne', hLog.ne']

theorem tendsto_constructionMass_div_power (s : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => constructionMass N / (N : ℝ) ^ s) atTop (𝓝 0) := by
  have h := tendsto_constructionMass_div_log.mul (tendsto_log_pow_div_nat_rpow 1 s hs)
  apply (show Tendsto (fun N : ℕ =>
      (constructionMass N / Real.log N) * (Real.log N / (N : ℝ) ^ s)) atTop (𝓝 0) from
    by simpa only [pow_one, mul_zero] using h).congr'
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hLog hN
  have hPow : (N : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hN) s).ne'
  field_simp [hLog.ne', hPow]

theorem tendsto_constructionMass_div_primeBase :
    Tendsto (fun N : ℕ => constructionMass N / constructionPrimeBase N) atTop (𝓝 0) := by
  have h := (tendsto_constructionMass_div_power (1 / 20) (by norm_num)).mul
    tendsto_constructionPrimeBase_inverse_ratio
  apply (show Tendsto (fun N : ℕ =>
      (constructionMass N / (N : ℝ) ^ (1 / 20 : ℝ)) *
        ((N : ℝ) ^ (1 / 20 : ℝ) / constructionPrimeBase N)) atTop (𝓝 0) from
    by simpa only [zero_mul] using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))] with N hN hB
  have hPow : (N : ℝ) ^ (1 / 20 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) _).ne'
  have hBZero : (constructionPrimeBase N : ℝ) ≠ 0 := by exact_mod_cast (by omega : constructionPrimeBase N ≠ 0)
  field_simp [hPow, hBZero]

theorem tendsto_constructionModulus_mass_div_primeBase :
    Tendsto (fun N : ℕ => (constructionModulus N : ℝ) * constructionMass N /
      constructionPrimeBase N) atTop (𝓝 0) := by
  have hUpper := (tendsto_constructionMass_div_power (1 / 25) (by norm_num)).mul
    tendsto_constructionPrimeBase_inverse_ratio
  apply squeeze_zero'
    (Eventually.of_forall (fun N => div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (le_trans (by norm_num) (constructionMass_one_le N)))
      (Nat.cast_nonneg _))) ?_
    (show Tendsto (fun N : ℕ =>
      (constructionMass N / (N : ℝ) ^ (1 / 25 : ℝ)) *
        ((N : ℝ) ^ (1 / 20 : ℝ) / constructionPrimeBase N)) atTop (𝓝 0) from
      by simpa only [zero_mul] using hUpper)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))] with N hN hB
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBPos : (0 : ℝ) < constructionPrimeBase N := by exact_mod_cast (by omega : 0 < constructionPrimeBase N)
  have hMass : 0 ≤ constructionMass N := le_trans (by norm_num) (constructionMass_one_le N)
  have hPower : (N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) ^ (1 / 25 : ℝ) =
      (N : ℝ) ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add hNPos]
    norm_num
  calc
    (constructionModulus N : ℝ) * constructionMass N / constructionPrimeBase N ≤
        (N : ℝ) ^ (1 / 100 : ℝ) * constructionMass N / constructionPrimeBase N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (constructionModulus_power_bound N hN) hMass) hBPos.le
    _ = (constructionMass N / (N : ℝ) ^ (1 / 25 : ℝ)) *
        ((N : ℝ) ^ (1 / 20 : ℝ) / constructionPrimeBase N) := by
      rw [← hPower]
      field_simp [hBPos.ne', (Real.rpow_pos_of_pos hNPos (1 / 25 : ℝ)).ne']
      <;> ring

theorem construction_divisor_sum (N : ℕ) :
    ((∑ n ∈ (constructionModulus N).divisors, constructionModulus N / n : ℕ) : ℝ) =
      (constructionModulus N : ℝ) * constructionMass N := by
  rw [Nat.cast_sum]
  calc
    (∑ n ∈ (constructionModulus N).divisors, ((constructionModulus N / n : ℕ) : ℝ)) =
        ∑ n ∈ (constructionModulus N).divisors, (n : ℝ) :=
      Nat.sum_div_divisors (constructionModulus N) (fun n => (n : ℝ))
    _ = constructionMass N * constructionModulus N :=
      (divisorReciprocalMass_mul _ (constructionModulus_pos N).ne').symm
    _ = (constructionModulus N : ℝ) * constructionMass N := mul_comm _ _

theorem eventually_construction_divisor_sum_lt_primeBase :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ (constructionModulus N).divisors, constructionModulus N / n) + 1 <
        constructionPrimeBase N := by
  have hInverse : Tendsto (fun N : ℕ => (1 : ℝ) / constructionPrimeBase N) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_constructionPrimeBase)
  have hSmall := (tendsto_constructionModulus_mass_div_primeBase.add hInverse).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1))
  filter_upwards [hSmall,
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))] with N hN hB
  have hBPos : (0 : ℝ) < constructionPrimeBase N := by exact_mod_cast (by omega : 0 < constructionPrimeBase N)
  have hRatio : ((constructionModulus N : ℝ) * constructionMass N + 1) /
      constructionPrimeBase N < 1 := by simpa only [add_div] using hN
  have hBound := (div_lt_one hBPos).mp hRatio
  rw [← construction_divisor_sum N] at hBound
  exact_mod_cast hBound

end Erdos319Sharp
