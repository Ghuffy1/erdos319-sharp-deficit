import Erdos319Sharp.DenseSigning
import Erdos319Sharp.Harmonic
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem reciprocalSum_lower_of_omission_bound {N : ℕ} {B : Finset ℕ}
    (hB : B ⊆ Finset.Icc 1 N) (x : ℝ) (hx : 1 ≤ x)
    (hMissing : ((N - B.card : ℕ) : ℝ) ≤ x) :
    Real.log N - 1 - Real.log x ≤ (reciprocalSum B : ℝ) := by
  have hFirst : Real.log N ≤ (harmonic N : ℝ) := by
    simpa using log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
  have hLast : (harmonic (N - B.card) : ℝ) ≤ 1 + Real.log x := by
    by_cases hZero : N - B.card = 0
    · simp only [hZero, harmonic_zero, Rat.cast_zero]
      have := Real.log_nonneg hx
      linarith
    · have hPos : (0 : ℝ) < (N - B.card : ℕ) := by
        exact_mod_cast Nat.pos_of_ne_zero hZero
      have hLog := Real.log_le_log hPos hMissing
      have hHarmonic := harmonic_le_one_add_log (N - B.card)
      linarith only [hLog, hHarmonic]
  have hMass : (harmonic N : ℝ) - (harmonic (N - B.card) : ℝ) ≤
      (reciprocalSum B : ℝ) := by
    exact_mod_cast harmonic_omission_lower_bound hB
  linarith only [hFirst, hLast, hMass]

theorem eventually_scaled_minorityScale_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) * minorityScale N := by
  filter_upwards [eventually_positive_scale,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_logloglog_nat.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hScale hLog hTriple
  have hDouble : Real.log (Real.log N) ≤ (N : ℝ) := by
    have hFirst := Real.log_le_sub_one_of_pos hScale.1
    have hSecond := Real.log_le_sub_one_of_pos hLog
    linarith
  have hNumerator : Real.log (Real.log N) ≤
      (N : ℝ) * Real.log (Real.log (Real.log N)) :=
    hDouble.trans (by nlinarith only [hTriple, hScale.1.le])
  have hRatio : (1 : ℝ) ≤ (N : ℝ) * Real.log (Real.log (Real.log N)) /
      Real.log (Real.log N) :=
    (le_div_iff₀ hScale.2.1).mpr (by simpa only [one_mul] using hNumerator)
  simpa only [minorityScale, mul_div_assoc] using hRatio

theorem eventually_dense_reciprocal_lower (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ,
      B ⊆ Finset.Icc 1 N →
      ((Finset.Icc 1 N \ B).card : ℝ) ≤ C * ((N : ℝ) * minorityScale N) →
      (1 - ε) * Real.log (Real.log (Real.log N)) ≤ (reciprocalSum B : ℝ) := by
  have hLogSmall : Tendsto (fun N : ℕ =>
      Real.log (Real.log (Real.log (Real.log N))) /
        Real.log (Real.log (Real.log N))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_logloglog_nat
  have hConstant : Tendsto (fun N : ℕ =>
      (1 + Real.log C) / Real.log (Real.log (Real.log N))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_logloglog_nat).const_mul (1 + Real.log C)
  have hError : Tendsto (fun N : ℕ =>
      (1 + Real.log C + Real.log (Real.log (Real.log (Real.log N)))) /
        Real.log (Real.log (Real.log N))) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using hConstant.add hLogSmall
  filter_upwards [eventually_positive_scale, eventually_scaled_minorityScale_ge_one,
    hError.eventually (Iio_mem_nhds hε)] with N hScale hUnit hSmall
  intro B hB hMissing
  have hCPos : 0 < C := zero_lt_one.trans_le hC
  have hX : 1 ≤ C * ((N : ℝ) * minorityScale N) := by
    have hMult := mul_le_mul_of_nonneg_right hC (zero_le_one.trans hUnit)
    nlinarith only [hMult, hUnit]
  have hMissing' : ((N - B.card : ℕ) : ℝ) ≤ C * ((N : ℝ) * minorityScale N) := by
    simpa only [Finset.card_sdiff_of_subset hB, Nat.card_Icc, Nat.sub_zero,
      Nat.add_sub_cancel] using hMissing
  have hMass := reciprocalSum_lower_of_omission_bound hB
    (C * ((N : ℝ) * minorityScale N)) hX hMissing'
  have hRewrite : C * ((N : ℝ) * minorityScale N) =
      (C * N * Real.log (Real.log (Real.log N))) / Real.log (Real.log N) := by
    unfold minorityScale
    ring
  have hLogX : Real.log (C * ((N : ℝ) * minorityScale N)) =
      Real.log C + Real.log N + Real.log (Real.log (Real.log (Real.log N))) -
        Real.log (Real.log (Real.log N)) := by
    rw [hRewrite, Real.log_div
      (mul_ne_zero (mul_ne_zero hCPos.ne' hScale.1.ne') hScale.2.2.ne') hScale.2.1.ne',
      Real.log_mul (mul_ne_zero hCPos.ne' hScale.1.ne') hScale.2.2.ne',
      Real.log_mul hCPos.ne' hScale.1.ne']
  rw [hLogX] at hMass
  have hErrorBound := (div_lt_iff₀ hScale.2.2).mp hSmall
  linarith only [hMass, hErrorBound]

theorem eventually_primitive_common_mass_lower (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ →
      ((N - A.card : ℕ) : ℝ) ≤ K * ((N : ℝ) * minorityScale N) →
      (1 - ε) * Real.log (Real.log (Real.log N)) ≤
        (reciprocalSum (positivePart A δ) : ℝ) ∧
      (1 - ε) * Real.log (Real.log (Real.log N)) ≤
        (reciprocalSum (negativePart A δ) : ℝ) := by
  have hC : (1 : ℝ) ≤ 201 + 2 * |K| := by
    have := abs_nonneg K
    linarith
  filter_upwards [eventually_minority_bound 1 (by norm_num),
    eventually_dense_reciprocal_lower (201 + 2 * |K|) ε hC hε,
    eventually_positive_scale] with N hMinority hDense hScale
  intro A δ hA hPrimitive hDeficit
  have hScaleNonneg : 0 ≤ (N : ℝ) * minorityScale N :=
    mul_nonneg hScale.1.le (div_nonneg hScale.2.2.le hScale.2.1.le)
  have hDeficitAbs : ((N - A.card : ℕ) : ℝ) ≤ |K| * ((N : ℝ) * minorityScale N) :=
    hDeficit.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hScaleNonneg)
  have hMin : min ((positivePart A δ).card : ℝ) ((negativePart A δ).card : ℝ) ≤
      (201 + |K|) * ((N : ℝ) * minorityScale N) := by
    have h := hMinority A δ hA hPrimitive
    norm_num only [one_mul] at h
    nlinarith only [h, hDeficitAbs]
  obtain ⟨B, hChoice, hB, hMissing⟩ :=
    exists_dense_sign_part N A δ ((201 + |K|) * ((N : ℝ) * minorityScale N)) hA hMin
  have hBound : ((Finset.Icc 1 N \ B).card : ℝ) ≤
      (201 + 2 * |K|) * ((N : ℝ) * minorityScale N) := by
    nlinarith only [hMissing, hDeficitAbs]
  have hMass := hDense B hB hBound
  have hEqual : (reciprocalSum (positivePart A δ) : ℝ) =
      (reciprocalSum (negativePart A δ) : ℝ) := by
    exact_mod_cast balanced_parts_equal hPrimitive.1
  rcases hChoice with rfl | rfl
  · exact ⟨hMass, hEqual ▸ hMass⟩
  · exact ⟨hEqual.symm ▸ hMass, hMass⟩

end Erdos319Sharp
