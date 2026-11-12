import Erdos319Sharp.MinorityDensity

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem minorityPrimeBand_card_le (N : ℕ) :
    (minorityPrimeBand N).card ≤ minorityUpper N := by
  have hSub : minorityPrimeBand N ⊆ Finset.Icc 1 (minorityUpper N) := by
    intro p hp
    have h := mem_primeInterval.mp hp
    exact Finset.mem_Icc.mpr ⟨h.1.one_le, h.2.2⟩
  simpa using Finset.card_le_card hSub

theorem minorityPrimeBand_prod_le_pow (N : ℕ) :
    (minorityPrimeBand N).prod id ≤ (minorityUpper N) ^ (minorityPrimeBand N).card := by
  calc
    (minorityPrimeBand N).prod id ≤ ∏ _p ∈ minorityPrimeBand N, minorityUpper N := by
      exact Finset.prod_le_prod (fun p hp => (mem_primeInterval.mp hp).2.2)
    _ = (minorityUpper N) ^ (minorityPrimeBand N).card := by simp

theorem eventually_minority_period_bound :
    ∀ᶠ N : ℕ in atTop, (((minorityPrimeBand N).prod id : ℕ) : ℝ) ≤ Real.sqrt N := by
  filter_upwards [eventually_loglog_sq_le_log_power (1 / 100) (by norm_num),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_minorityUpper.eventually (eventually_ge_atTop (2 : ℕ)),
    eventually_gt_atTop (0 : ℕ)] with N hLLsq hL hLL hUpper hN
  have hLpos : 0 < Real.log N := zero_lt_one.trans_le hL
  have hUpperPos : (0 : ℝ) < minorityUpper N := by exact_mod_cast (by omega : 0 < minorityUpper N)
  have hUpperOne : (1 : ℝ) ≤ minorityUpper N := by exact_mod_cast (by omega : 1 ≤ minorityUpper N)
  have hCap : (minorityUpper N : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hLpos.le _)
  have hLogCap : Real.log (minorityUpper N) ≤ (1 / 100 : ℝ) * Real.log (Real.log N) := by
    have h := Real.log_le_log hUpperPos hCap
    rwa [Real.log_rpow hLpos] at h
  have hCardUpper : ((minorityPrimeBand N).card : ℝ) ≤ minorityUpper N := by
    exact_mod_cast minorityPrimeBand_card_le N
  have hCardCap : ((minorityPrimeBand N).card : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ) :=
    hCardUpper.trans hCap
  have hProdPos : (0 : ℝ) < ((minorityPrimeBand N).prod id : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (mem_primeInterval.mp hp).1.pos)
  have hPow := minorityPrimeBand_prod_le_pow N
  have hPowReal : (((minorityPrimeBand N).prod id : ℕ) : ℝ) ≤
      (minorityUpper N : ℝ) ^ (minorityPrimeBand N).card := by exact_mod_cast hPow
  have hLog := Real.log_le_log hProdPos hPowReal
  rw [Real.log_pow] at hLog
  have hLogProd : Real.log (((minorityPrimeBand N).prod id : ℕ) : ℝ) ≤
      (Real.log N) ^ (1 / 100 : ℝ) * ((1 / 100 : ℝ) * Real.log (Real.log N)) := by
    exact hLog.trans (mul_le_mul hCardCap hLogCap (Real.log_nonneg hUpperOne)
      (Real.rpow_nonneg hLpos.le _))
  have hLLcap : Real.log (Real.log N) ≤ (Real.log N) ^ (1 / 100 : ℝ) := by
    nlinarith only [hLLsq, hLL]
  have hSmallPower : (Real.log N) ^ (2 / 100 : ℝ) ≤ Real.log N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (2 / 100 : ℝ) ≤ 1)
  have hSquare : ((Real.log N) ^ (1 / 100 : ℝ)) ^ 2 = (Real.log N) ^ (2 / 100 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hLogHalf : Real.log (((minorityPrimeBand N).prod id : ℕ) : ℝ) ≤ Real.log N / 2 := by
    have hMul := mul_le_mul_of_nonneg_left hLLcap (Real.rpow_nonneg hLpos.le (1 / 100))
    rw [← pow_two, hSquare] at hMul
    nlinarith only [hLogProd, hMul, hSmallPower, hL]
  have hExp := Real.exp_le_exp.mpr hLogHalf
  rw [Real.exp_log hProdPos] at hExp
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hN)]
  simpa only [div_eq_mul_inv, one_mul] using hExp

theorem eventually_minority_error_bound :
    ∀ᶠ N : ℕ in atTop, minorityBandError (minorityPrimeBand N) N ≤
      (N : ℝ) * (Real.log N) ^ (-(1 / 100 : ℝ)) + 3 * Real.sqrt N := by
  filter_upwards [eventually_minority_period_bound,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hPeriod hL
  have hCardUpper : ((minorityPrimeBand N).card : ℝ) ≤ minorityUpper N := by
    exact_mod_cast minorityPrimeBand_card_le N
  have hCard : ((minorityPrimeBand N).card : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ) :=
    hCardUpper.trans (Nat.floor_le (Real.rpow_nonneg hL.le _))
  have hMul := mul_le_mul_of_nonneg_right hCard
    (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hL.le (-(1 / 50 : ℝ))))
  have hPowers : (Real.log N) ^ (1 / 100 : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)) =
      (Real.log N) ^ (-(1 / 100 : ℝ)) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hCount : ((minorityPrimeBand N).card : ℝ) *
      ((N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ))) ≤
      (N : ℝ) * (Real.log N) ^ (-(1 / 100 : ℝ)) := by
    calc
      _ ≤ (Real.log N) ^ (1 / 100 : ℝ) *
          ((N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ))) := hMul
      _ = (N : ℝ) * (Real.log N) ^ (-(1 / 100 : ℝ)) := by
        rw [mul_left_comm, hPowers]
  exact add_le_add hCount (mul_le_mul_of_nonneg_left hPeriod (by norm_num))

theorem tendsto_minority_error_ratio_zero :
    Tendsto (fun N : ℕ => minorityBandError (minorityPrimeBand N) N /
      ((N : ℝ) * minorityScale N)) atTop (𝓝 0) := by
  have hFirst : Tendsto (fun N : ℕ =>
      (Real.log N) ^ (-(1 / 100 : ℝ)) * Real.log (Real.log N)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).tendsto_div_nhds_zero.comp
      tendsto_log_coe_at_top
    apply (show Tendsto (fun N : ℕ => Real.log (Real.log N) / (Real.log N) ^ (1 / 100 : ℝ))
      atTop (𝓝 0) by simpa only [Function.comp_def] using h).congr'
    filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ))] with N hL
    rw [Real.rpow_neg hL]
    ring
  have hSecond : Tendsto (fun N : ℕ => 3 * Real.log N / Real.sqrt N) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow, mul_div_assoc, mul_zero] using
      (((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop).const_mul 3)
  apply squeeze_zero' ?_ ?_ (by simpa only [zero_add] using hFirst.add hSecond)
  · filter_upwards [eventually_positive_scale,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hL
    apply div_nonneg
    · exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    · exact mul_nonneg hN.1.le (div_pos hN.2.2 hN.2.1).le
  · filter_upwards [eventually_minority_error_bound, eventually_positive_scale,
      tendsto_logloglog_nat.eventually (eventually_ge_atTop (1 : ℝ)),
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with N hBound hN hMu hL
    have hRoot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN.1
    have hScale : 0 < minorityScale N := div_pos hN.2.2 hN.2.1
    have hLL : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hL.le
    calc
      minorityBandError (minorityPrimeBand N) N / ((N : ℝ) * minorityScale N) ≤
          ((N : ℝ) * (Real.log N) ^ (-(1 / 100 : ℝ)) + 3 * Real.sqrt N) /
            ((N : ℝ) * minorityScale N) :=
        div_le_div_of_nonneg_right hBound (mul_pos hN.1 hScale).le
      _ = ((Real.log N) ^ (-(1 / 100 : ℝ)) + 3 / Real.sqrt N) *
          Real.log (Real.log N) / Real.log (Real.log (Real.log N)) := by
        dsimp [minorityScale]
        field_simp [hN.1.ne', hRoot.ne', hN.2.1.ne', hN.2.2.ne']
        nlinarith only [Real.sq_sqrt hN.1.le]
      _ ≤ ((Real.log N) ^ (-(1 / 100 : ℝ)) + 3 / Real.sqrt N) *
          Real.log (Real.log N) :=
        div_le_self (mul_nonneg (add_nonneg (Real.rpow_nonneg hL.le _) (by positivity)) hN.2.1.le) hMu
      _ = (Real.log N) ^ (-(1 / 100 : ℝ)) * Real.log (Real.log N) +
          3 * (Real.log (Real.log N) / Real.sqrt N) := by ring
      _ ≤ (Real.log N) ^ (-(1 / 100 : ℝ)) * Real.log (Real.log N) +
          3 * (Real.log N / Real.sqrt N) := by
        have h := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hLL hRoot.le) (by norm_num : (0 : ℝ) ≤ 3)
        linarith only [h]
      _ = (Real.log N) ^ (-(1 / 100 : ℝ)) * Real.log (Real.log N) +
          3 * Real.log N / Real.sqrt N := by ring

end Erdos319Sharp
