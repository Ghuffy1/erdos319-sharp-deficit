import Erdos319Sharp.ConstructionParameters

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem tendsto_constructionPrimeBase : Tendsto constructionPrimeBase atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp tendsto_natCast_atTop_atTop)

theorem constructionPrimeBase_le_power (N : ℕ) :
    (constructionPrimeBase N : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem tendsto_constructionPrimeBase_ratio :
    Tendsto (fun N : ℕ => (constructionPrimeBase N : ℝ) / (N : ℝ) ^ (1 / 20 : ℝ))
      atTop (𝓝 1) := by
  exact tendsto_nat_floor_div_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp tendsto_natCast_atTop_atTop)

theorem tendsto_constructionPrimeBase_inverse_ratio :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 20 : ℝ) / constructionPrimeBase N)
      atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using tendsto_constructionPrimeBase_ratio.inv₀ (by norm_num)

theorem mem_constructionPrimeBand {N p : ℕ} :
    p ∈ constructionPrimeBand N ↔
      p.Prime ∧ constructionPrimeBase N < p ∧ p ≤ constructionPrimeBase N ^ 2 :=
  mem_primeInterval

theorem constructionPrimeBand_card_le (N : ℕ) :
    (constructionPrimeBand N).card ≤ constructionPrimeBase N ^ 2 := by
  have hSub : constructionPrimeBand N ⊆ Icc 1 (constructionPrimeBase N ^ 2) := by
    intro p hp
    have h := mem_constructionPrimeBand.mp hp
    exact mem_Icc.mpr ⟨h.1.one_le, h.2.2⟩
  simpa using Finset.card_le_card hSub

theorem constructionPrimeBand_power_bounds {N p : ℕ} (hp : p ∈ constructionPrimeBand N) :
    (N : ℝ) ^ (1 / 20 : ℝ) < p ∧ (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
  have h := mem_constructionPrimeBand.mp hp
  constructor
  · exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) _)).mp h.2.1
  · have hpUpper : (p : ℝ) ≤ (constructionPrimeBase N : ℝ) ^ 2 := by exact_mod_cast h.2.2
    calc
      (p : ℝ) ≤ (constructionPrimeBase N : ℝ) ^ 2 := hpUpper
      _ ≤ ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (constructionPrimeBase_le_power N) _
      _ = (N : ℝ) ^ (1 / 10 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
        norm_num

theorem tendsto_constructionPrimeBand_mass :
    Tendsto (fun N : ℕ => ∑ p ∈ constructionPrimeBand N, (1 : ℝ) / p)
      atTop (𝓝 (Real.log 2)) := by
  have h := (primeReciprocalPowerBand_limit 1 2 (by norm_num) (by norm_num)).comp
    tendsto_constructionPrimeBase
  apply (show Tendsto (fun N : ℕ =>
      primeReciprocalSum (constructionPrimeBase N ^ 2) -
        primeReciprocalSum (constructionPrimeBase N)) atTop (𝓝 (Real.log 2)) from
    by simpa only [pow_one, Nat.cast_one, Nat.cast_ofNat, Real.log_one, sub_zero,
      Function.comp_def] using h).congr'
  filter_upwards [tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))]
    with N hB
  exact (primeInterval_reciprocal_sum _ _ (by nlinarith :
    constructionPrimeBase N ≤ constructionPrimeBase N ^ 2)).symm

end Erdos319Sharp
