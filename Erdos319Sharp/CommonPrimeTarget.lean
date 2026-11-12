import Erdos319Sharp.QuantitativeCleaning
import Erdos319Sharp.ExactSubset
import Erdos319Sharp.ModularTarget

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_loglog_sq_le_log_power (r : ℝ) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, (Real.log (Real.log N)) ^ 2 ≤ (Real.log N) ^ r := by
  have hLimit : Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ 2 / (Real.log N) ^ r)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two] using
      ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hr).tendsto_div_nhds_zero.comp tendsto_log_coe_at_top)
  filter_upwards [hLimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℕ)] with N hBound hN
  have hPos : 0 < (Real.log N) ^ r := Real.rpow_pos_of_pos
    (Real.log_pos (by exact_mod_cast hN)) r
  simpa only [one_mul] using (div_le_iff₀ hPos).mp hBound.le

theorem eventually_common_prime_target :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (p : ℕ),
      A ⊆ Finset.Icc 1 N → p.Prime →
      (Real.log (Real.log N)) ^ 2 ≤ (p : ℝ) → (p : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ) →
      4 * (N : ℝ) / (Real.log (Real.log N)) ^ 2 ≤ A.card →
      (N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)) ≤
        ((A.filter (fun n => p ∣ n)).card : ℝ) →
      ∃ B ⊆ A, B.Nonempty ∧ B ≠ A ∧ reciprocalSum B = (1 : ℚ) / p := by
  filter_upwards [eventually_quantitative_regular_subset, eventually_exact_subset_from_mass_bounds 1,
    eventually_loglog_sq_le_log_power (1 / 40) (by norm_num),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with N hClean hExact hLLBound hL hLL hN
  intro A p hA hp hpLower hpUpper hCard hFiber
  let L : ℝ := Real.log N
  let H : ℝ := (Real.log (Real.log N)) ^ 2
  let c : ℝ := L ^ (-3 / 100 : ℝ)
  have hLPos : 0 < L := by dsimp [L]; linarith
  have hLOne : 1 ≤ L := hL.le
  have hHPos : 0 < H := by dsimp [H]; positivity
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc : 0 < c := Real.rpow_pos_of_pos hLPos _
  have hcOne : c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hLOne (by norm_num)
  have hLossInv : L ^ (-(1 / 40 : ℝ)) ≤ 1 / H := by
    have h := one_div_le_one_div_of_le hHPos hLLBound
    simpa only [one_div, Real.rpow_neg hLPos.le] using h
  have hHLeL : H ≤ L := hLLBound.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hLOne (by norm_num : (1 / 40 : ℝ) ≤ 1))
  obtain ⟨F, hFA, hMin, hSmooth, hMult, hRich, hLoss⟩ := hClean A hA
  have hFPrefix : F ⊆ Finset.Icc 1 N := hFA.trans hA
  have hCount : ((A \ F).card : ℝ) + F.card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hFA
  have hLossMass : ((A \ F).card : ℝ) ≤ (N : ℝ) / H := by
    exact hLoss.trans (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hLossInv hNPos.le)
  have hFCard : 3 * (N : ℝ) / H ≤ F.card := by
    change 4 * (N : ℝ) / H ≤ A.card at hCard
    rw [mul_div_assoc] at hCard ⊢
    linarith only [hCard, hCount, hLossMass]
  have hMassF : 3 / H ≤ (reciprocalSum F : ℝ) := by
    have h := hFCard.trans (card_le_N_mul_reciprocalSum hFPrefix)
    rw [← reciprocalSum_eq_baseline] at h
    apply (mul_le_mul_iff_of_pos_left hNPos).mp
    convert h using 1 <;> ring
  have hMassA : 4 / H ≤ (reciprocalSum A : ℝ) := by
    have h := hCard.trans (card_le_N_mul_reciprocalSum hA)
    rw [← reciprocalSum_eq_baseline] at h
    apply (mul_le_mul_iff_of_pos_left hNPos).mp
    convert h using 1 <;> ring
  have hCardEnough : (N : ℝ) / (Real.log N) ^ (1 : ℕ) ≤ F.card := by
    have hOne : (N : ℝ) / L ≤ (N : ℝ) / H := div_le_div_of_nonneg_left hNPos.le hHPos hHLeL
    have hThree : (N : ℝ) / H ≤ 3 * (N : ℝ) / H := by
      have hNonneg : 0 ≤ (N : ℝ) / H := div_nonneg hNPos.le hHPos.le
      rw [mul_div_assoc]
      nlinarith
    simpa only [pow_one] using hOne.trans (hThree.trans hFCard)
  have hpSurvives : ∃ n ∈ F, p ∣ n := by
    by_contra hNone
    have hSub : A.filter (fun n => p ∣ n) ⊆ A \ F := by
      intro n hn
      obtain ⟨hnA, hpn⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_sdiff.mpr ⟨hnA, fun hnF => hNone ⟨n, hnF, hpn⟩⟩
    have hCountFiber : ((A.filter (fun n => p ∣ n)).card : ℝ) ≤ (A \ F).card := by
      exact_mod_cast Finset.card_le_card hSub
    have hStrict : (N : ℝ) * L ^ (-(1 / 40 : ℝ)) < (N : ℝ) * L ^ (-(1 / 50 : ℝ)) :=
      mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_lt hL (by norm_num)) hNPos
    exact (not_lt_of_ge (hFiber.trans (hCountFiber.trans hLoss))) hStrict
  obtain ⟨n, hn, hpn⟩ := hpSurvives
  have hpDvd : p ∣ F.lcm id := hpn.trans (Finset.dvd_lcm hn)
  let r : ℚ := (1 : ℚ) / p
  have hr : 0 < r := div_pos (by norm_num) (by exact_mod_cast hp.pos)
  have hrReal : (r : ℝ) = 1 / (p : ℝ) := by dsimp [r]; push_cast; rfl
  have hTargetLower : (1 + 1 / Real.log N) * (r : ℝ) ≤ (reciprocalSum F : ℝ) := by
    rw [hrReal]
    have hLInv : 1 / L ≤ 1 := (div_le_one hLPos).mpr hLOne
    have hpInv : (1 : ℝ) / p ≤ 1 / H := one_div_le_one_div_of_le hHPos hpLower
    have hFirst : (1 + 1 / L) * (1 / (p : ℝ)) ≤ 2 * (1 / H) :=
      (mul_le_mul_of_nonneg_right (by linarith : 1 + 1 / L ≤ 2) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpInv (by norm_num))
    have hSecond : 2 * (1 / H) ≤ 3 / H := by
      calc
        2 * (1 / H) ≤ 3 * (1 / H) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = 3 / H := by ring
    exact hFirst.trans (hSecond.trans hMassF)
  have hTargetUpper : (reciprocalSum F : ℝ) ≤ Real.log N * (r : ℝ) := by
    have hFCount : (F.card : ℝ) ≤ N := by exact_mod_cast
      (show F.card ≤ N by simpa using Finset.card_le_card hFPrefix)
    have hMass := reciprocalSum_le_card_div_min F (c * N) (mul_pos hc hNPos) hMin
    rw [← reciprocalSum_eq_baseline] at hMass
    have hUpper : (reciprocalSum F : ℝ) ≤ 1 / c := by
      calc
        _ ≤ F.card / (c * N) := hMass
        _ ≤ (N : ℝ) / (c * N) := div_le_div_of_nonneg_right hFCount (mul_pos hc hNPos).le
        _ = 1 / c := by field_simp
    have hInv : 1 / c = L ^ (3 / 100 : ℝ) := by
      dsimp [c]
      rw [show (-3 / 100 : ℝ) = -(3 / 100 : ℝ) by norm_num, Real.rpow_neg hLPos.le]
      simp
    have hProduct : L ^ (3 / 100 : ℝ) * (p : ℝ) ≤ L := by
      calc
        _ ≤ L ^ (3 / 100 : ℝ) * L ^ (1 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hpUpper (Real.rpow_nonneg hLPos.le _)
        _ = L ^ (1 / 25 : ℝ) := by rw [← Real.rpow_add hLPos]; norm_num
        _ ≤ L := by simpa using Real.rpow_le_rpow_of_exponent_le hLOne (by norm_num : (1 / 25 : ℝ) ≤ 1)
    rw [hInv] at hUpper
    rw [hrReal]
    exact hUpper.trans (by simpa only [mul_one_div] using (le_div_iff₀ hpPos).mpr hProduct)
  obtain ⟨B, hBF, hSum⟩ := hExact c ((Real.log N) ^ (-(1 / 25 : ℝ))) F hc hcOne le_rfl (by norm_num)
    hFPrefix hMin hSmooth hMult hRich hCardEnough r hr ((nat_quotient_den_dvd 1 p).trans hpDvd)
    hTargetLower hTargetUpper
  have hBne : B.Nonempty := by
    by_contra hEmpty
    have hBEq : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    simp [hBEq, reciprocalSum] at hSum
    exact hr.ne' hSum.symm
  have hProper : B ≠ A := by
    intro hEq
    have hRA : (reciprocalSum A : ℝ) = 1 / (p : ℝ) := by rw [← hEq, hSum, hrReal]
    have hpInv : (1 : ℝ) / p ≤ 1 / H := one_div_le_one_div_of_le hHPos hpLower
    have hPos : 0 < 1 / H := one_div_pos.mpr hHPos
    rw [hRA] at hMassA
    rw [show (4 : ℝ) / H = 4 * (1 / H) by ring] at hMassA
    nlinarith only [hMassA, hpInv, hPos]
  exact ⟨B, hBF.trans hFA, hBne, hProper, hSum⟩

end Erdos319Sharp
