import Erdos319Sharp.MissingMassLower
import Erdos319Sharp.OmissionCounting
import Erdos319Sharp.LowerBoundScales
import Erdos319Sharp.Reduction

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_bounded_primitive_deficit_lower (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ →
      ((N - A.card : ℕ) : ℝ) ≤ K * ((N : ℝ) * minorityScale N) →
      (Real.exp (-Real.eulerMascheroniConstant) - ε) * ((N : ℝ) * minorityScale N) ≤
        ((N - A.card : ℕ) : ℝ) := by
  obtain ⟨a, θ, ha, hMass, hθ, hW, hClose⟩ := exists_lower_bound_parameters ε hε
  have hError := (tendsto_lowerOmissionError_ratio_zero a).eventually
    (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [eventually_dense_core_missing_mass_lower a K θ θ ha hMass hθ hθ,
    eventually_core_omission_count θ hθ, eventually_smoothCutoff_le_div_log,
    eventually_primePowerTail_log_rate, hError, eventually_positive_scale,
    eventually_gt_atTop (0 : ℕ)] with N hCore hCounting hCutoff hTail hErrorSmall hScale hN
  intro A δ hA hPrimitive hDeficit
  obtain ⟨τ, F, P, hτ, hF, hSmooth, hPrune, hCard, hRho, hP, hPMass, hPCard,
    hFree, hRhoLower⟩ := hCore A δ hA hPrimitive hDeficit
  let ρ : ℝ := (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ)
  let W : ℝ := 1 - 2 * a - θ - 2 * θ * Real.exp (2 * θ)
  let d : ℝ := ((N - A.card : ℕ) : ℝ)
  have hρ : 0 ≤ ρ := by
    have h : (0 : ℚ) ≤ reciprocalSum (firstMissingPowers (F.lcm id) N) :=
      Finset.sum_nonneg (fun n _ => by positivity)
    change (0 : ℝ) ≤ (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ)
    exact_mod_cast h
  have hScalePos : 0 < (N : ℝ) * minorityScale N :=
    mul_pos hScale.1 (div_pos hScale.2.2 hScale.2.1)
  have hD : F.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by
    intro n hn
    have hPrefix := tailInterval_subset a N ((Finset.mem_inter.mp (hF hn)).2)
    exact (show 0 < n from (Finset.mem_Icc.mp hPrefix).1).ne')
  have hOmission := hCounting a A τ F P ha.le (small_tail_parameter a ha hMass) hA hF hD hFree
  have hSquare : (N : ℝ) * ρ ^ 2 ≤ θ * ((N : ℝ) * ρ) := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRho hρ) (Nat.cast_nonneg N)
    nlinarith only [h]
  have hExp : Real.exp (2 * ρ) ≤ Real.exp (2 * θ) := Real.exp_le_exp.mpr (by linarith)
  have hBad := mul_le_mul_of_nonneg_left hExp
    (show 0 ≤ 2 * θ * (N : ℝ) * ρ by positivity)
  have hMain : W * ((N : ℝ) * ρ) ≤ d + 4 * smoothCutoff 6 N +
      2 * (N : ℝ) * primePowerTail N (smoothCutoff 6 N) +
        (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) +
          (N : ℝ) * ((Real.log (1 / a) + 1) / Real.log N) := by
    dsimp [W, d]
    change (1 - 2 * a) * (N : ℝ) * ρ - (N : ℝ) * ρ ^ 2 -
      4 * smoothCutoff 6 N - 2 * (N : ℝ) * primePowerTail N (smoothCutoff 6 N) ≤
        ((N - A.card : ℕ) : ℝ) + (((negativePart A τ ∩ tailInterval a N) \ F).card : ℝ) +
          P.card + 2 * θ * (N : ℝ) * ρ * Real.exp (2 * ρ) at hOmission
    nlinarith only [hOmission, hPrune, hPCard, hSquare, hBad]
  have hTotalError : 4 * smoothCutoff 6 N +
      2 * (N : ℝ) * primePowerTail N (smoothCutoff 6 N) +
        (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) +
          (N : ℝ) * ((Real.log (1 / a) + 1) / Real.log N) ≤
            (N : ℝ) * lowerOmissionError a N := by
    have hCutoffFour := mul_le_mul_of_nonneg_left hCutoff (by norm_num : (0 : ℝ) ≤ 4)
    have hTailTwo := mul_le_mul_of_nonneg_left hTail (show 0 ≤ 2 * (N : ℝ) by positivity)
    simp only [lowerOmissionError, Real.rpow_neg_one, div_eq_mul_inv] at hCutoffFour ⊢
    nlinarith only [hCutoffFour, hTailTwo]
  have hRate : lowerOmissionError a N ≤ (ε / 2) * minorityScale N :=
    ((div_lt_iff₀ (div_pos hScale.2.2 hScale.2.1)).mp hErrorSmall).le
  have hErrorBound := mul_le_mul_of_nonneg_left hRate (Nat.cast_nonneg N)
  have hRhoScaled : (Real.exp (-Real.eulerMascheroniConstant) - θ) *
      ((N : ℝ) * minorityScale N) ≤ (N : ℝ) * ρ := by
    have hMult := mul_le_mul_of_nonneg_left hRhoLower (Nat.cast_nonneg N)
    have hDiv : ((Real.exp (-Real.eulerMascheroniConstant) - θ) * (N : ℝ) *
        Real.log (Real.log (Real.log N))) / Real.log (Real.log N) ≤ (N : ℝ) * ρ :=
      (div_le_iff₀ hScale.2.1).mpr (by nlinarith only [hMult])
    calc
      _ = ((Real.exp (-Real.eulerMascheroniConstant) - θ) * (N : ℝ) *
          Real.log (Real.log (Real.log N))) / Real.log (Real.log N) := by
        unfold minorityScale
        ring
      _ ≤ (N : ℝ) * ρ := hDiv
  have hWeighted := mul_le_mul_of_nonneg_left hRhoScaled hW.le
  have hCloseScaled := mul_lt_mul_of_pos_right hClose hScalePos
  change (Real.exp (-Real.eulerMascheroniConstant) - ε) * ((N : ℝ) * minorityScale N) ≤ d
  change (Real.exp (-Real.eulerMascheroniConstant) - ε / 2) * ((N : ℝ) * minorityScale N) <
    W * (Real.exp (-Real.eulerMascheroniConstant) - θ) * ((N : ℝ) * minorityScale N) at hCloseScaled
  nlinarith only [hMain, hTotalError, hErrorBound, hWeighted, hCloseScaled]

theorem sharpLowerBound_proved : SharpLowerBound := by
  intro ε hε
  let c := Real.exp (-Real.eulerMascheroniConstant)
  let K := c + 1
  filter_upwards [eventually_bounded_primitive_deficit_lower K (ε / 2) (by linarith),
    eventually_positive_scale] with N hBound hScale
  intro A hA hPrimitive
  obtain ⟨δ, hδ⟩ := hPrimitive
  let d : ℝ := ((N - A.card : ℕ) : ℝ)
  let scale : ℝ := (N : ℝ) * minorityScale N
  have hScalePos : 0 < scale := mul_pos hScale.1 (div_pos hScale.2.2 hScale.2.1)
  have hStrict : (c - ε) * scale < d := by
    by_cases hSmall : d ≤ K * scale
    · have hLower := hBound A δ hA hδ hSmall
      have hGap : 0 < (ε / 2) * scale := mul_pos (by linarith) hScalePos
      change (c - ε / 2) * scale ≤ d at hLower
      nlinarith only [hLower, hGap]
    · have hLarge : K * scale < d := lt_of_not_ge hSmall
      have hCoefficient : c - ε < K := by dsimp [K]; linarith
      exact (mul_lt_mul_of_pos_right hCoefficient hScalePos).trans hLarge
  have hCard : A.card ≤ N := by simpa using Finset.card_le_card hA
  have hIdentity : normalizedOmissions N A.card = d / scale := by
    unfold normalizedOmissions
    dsimp [d, scale, minorityScale]
    rw [Nat.cast_sub hCard]
    field_simp [hScale.1.ne', hScale.2.1.ne', hScale.2.2.ne']
  change c - ε < normalizedOmissions N A.card
  rw [hIdentity]
  exact (lt_div_iff₀ hScalePos).mpr hStrict

end Erdos319Sharp
