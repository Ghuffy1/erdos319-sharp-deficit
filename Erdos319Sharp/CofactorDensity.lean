import Erdos319Sharp.InverseDensity
import Erdos319Sharp.ExcessGroups
import Erdos319Sharp.TailDivisibility

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_small_scale_cofactor_room :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → (m : ℝ) ≤ smoothCutoff 6 N →
      (harmonicPrimeCutoff N : ℝ) ^ (2 * Real.log (harmonicPrimeCutoff N : ℝ)) ≤
        ((N / m : ℕ) : ℝ) := by
  have hRatio : Tendsto (fun N : ℕ =>
      338 * (Real.log (Real.log N)) ^ 2 / (Real.log N) ^ (4 / 5 : ℝ))
      atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 4 / 5)).tendsto_div_nhds_zero.comp
        tendsto_log_coe_at_top).const_mul 338
    simpa only [Function.comp_def, Real.rpow_two, mul_div_assoc, mul_zero] using h
  have hY : Tendsto (fun N : ℕ => (harmonicPrimeCutoff N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_harmonicPrimeCutoff
  filter_upwards [hRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_log_harmonicPrimeCutoff_bound,
    (Real.tendsto_log_atTop.comp hY).eventually (eventually_ge_atTop (4 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hSmall hLogUpper hLogLower hLogN hN
  intro m hm hmS
  let Y : ℝ := harmonicPrimeCutoff N
  let x : ℝ := (Real.log N) ^ (4 / 5 : ℝ)
  let T : ℝ := Y ^ (2 * Real.log Y)
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmPos : (0 : ℝ) < m := by exact_mod_cast hm
  have hYLog : 4 ≤ Real.log Y := hLogLower
  have hYOne : 1 < Y := (Real.log_pos_iff (Nat.cast_nonneg _)).mp (by linarith)
  have hYPos : 0 < Y := zero_lt_one.trans hYOne
  have hxOne : 1 ≤ x := Real.one_le_rpow hLogN (by norm_num)
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hSmall' : 338 * (Real.log (Real.log N)) ^ 2 ≤ x := by
    simpa only [one_mul] using ((div_lt_iff₀ hxPos).mp hSmall).le
  have hSquare : (Real.log Y) ^ 2 ≤ 169 * (Real.log (Real.log N)) ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log Y) hLogUpper 2
    nlinarith only [h]
  have hT : T ≤ Real.exp x := by
    dsimp [T]
    rw [Real.rpow_def_of_pos hYPos]
    apply Real.exp_le_exp.mpr
    nlinarith only [hSquare, hSmall']
  have hTOne : 1 ≤ T := Real.one_le_rpow hYOne.le (by linarith)
  have hExponential : 2 * T ≤ Real.exp (6 * x) := by
    have hExpTwo : 2 ≤ Real.exp x := by
      have h := Real.add_one_le_exp x
      linarith only [h, hxOne]
    calc
      2 * T ≤ 2 * Real.exp x := mul_le_mul_of_nonneg_left hT (by norm_num)
      _ ≤ Real.exp x * Real.exp x :=
        mul_le_mul_of_nonneg_right hExpTwo (Real.exp_nonneg _)
      _ = Real.exp (2 * x) := by rw [← Real.exp_add]; congr 1 <;> ring
      _ ≤ Real.exp (6 * x) := Real.exp_le_exp.mpr (by linarith only [hxPos])
  have hQuotient : (N : ℝ) / smoothCutoff 6 N = Real.exp (6 * x) := by
    change (N : ℝ) / ((N : ℝ) * Real.exp (-6 * x)) = Real.exp (6 * x)
    rw [show -6 * x = -(6 * x) by ring, Real.exp_neg]
    field_simp
  have hLower : 2 * T ≤ (N : ℝ) / m :=
    hExponential.trans (hQuotient ▸
      div_le_div_of_nonneg_left hNPos.le hmPos hmS)
  have hFloor : (N : ℝ) / m < ((N / m : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using Nat.lt_floor_add_one ((N : ℝ) / m)
  change T ≤ ((N / m : ℕ) : ℝ)
  linarith only [hLower, hFloor, hTOne]

theorem eventually_small_scale_excess_group_card (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (D b : ℕ) (A : Finset ℕ),
      D ≠ 0 → 0 < b → b ≤ N → A ⊆ Finset.Icc 1 N →
      InverseZeroSumFree b (excessCofactors D b A) →
      (excessScale D b : ℝ) ≤ smoothCutoff 6 N →
      ((excessGroup D b A).card : ℝ) ≤ ε * (N : ℝ) / excessScale D b := by
  filter_upwards [eventually_small_scale_cofactor_room,
    eventually_inverse_zero_free_card_bound ε hε] with N hRoom hSparse
  intro D b A hD hb hbN hA hFree hScale
  have hPositive : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  have hScalePos : 0 < excessScale D b :=
    Nat.pos_of_ne_zero (excessScale_ne_zero D b hD hb.ne')
  have hBound := hSparse b (N / excessScale D b) (excessCofactors D b A) hb hbN
    (excessCofactors_subset D b N A hD hA)
    (excessCofactors_coprime D b A hD hPositive) hFree
    (hRoom (excessScale D b) hScalePos hScale)
  have hDivide : ((N / excessScale D b : ℕ) : ℝ) ≤ (N : ℝ) / excessScale D b := by
    have h := prefix_multiples_card_le N (excessScale D b) hScalePos
    rwa [prefix_multiples_card] at h
  calc
    ((excessGroup D b A).card : ℝ) = (excessCofactors D b A).card := by
      exact_mod_cast (excessCofactors_card D b A hD hPositive).symm
    _ ≤ ε * ((N / excessScale D b : ℕ) : ℝ) := hBound
    _ ≤ ε * ((N : ℝ) / excessScale D b) := mul_le_mul_of_nonneg_left hDivide hε.le
    _ = ε * (N : ℝ) / excessScale D b := by ring

end Erdos319Sharp
