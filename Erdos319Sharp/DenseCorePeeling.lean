import Erdos319Sharp.CommonMass
import Erdos319Sharp.DenseDeletion
import Erdos319Sharp.UniformWeightedMass

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem negativePart_reverse (A : Finset ℕ) (δ : ℕ → ℤˣ) :
    negativePart A (reverseSigning δ) = positivePart A δ := by
  ext n
  simp [negativePart, positivePart, reverseSigning, neg_eq_iff_eq_neg]

theorem positivePart_reverse (A : Finset ℕ) (δ : ℕ → ℤˣ) :
    positivePart A (reverseSigning δ) = negativePart A δ := by
  ext n
  simp [negativePart, positivePart, reverseSigning, neg_eq_iff_eq_neg]

theorem exists_signing_with_negative_part {A B : Finset ℕ} {δ : ℕ → ℤˣ}
    (hPrimitive : IsPrimitiveSigning A δ)
    (hChoice : B = positivePart A δ ∨ B = negativePart A δ) :
    ∃ τ : ℕ → ℤˣ, IsPrimitiveSigning A τ ∧ negativePart A τ = B := by
  rcases hChoice with hPos | hNeg
  · exact ⟨reverseSigning δ, isPrimitiveSigning_reverse hPrimitive,
      (negativePart_reverse A δ).trans hPos.symm⟩
  · exact ⟨δ, hPrimitive, hNeg.symm⟩

/-- An oriented dense core and one peeled positive set satisfy the weighted
mass comparison needed for the sharp omission bound. -/
theorem eventually_dense_core_peeling (a K ε κ : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ →
      ((N - A.card : ℕ) : ℝ) ≤ K * ((N : ℝ) * minorityScale N) →
      ∃ (τ : ℕ → ℤˣ) (F P : Finset ℕ),
        IsPrimitiveSigning A τ ∧ F ⊆ negativePart A τ ∩ tailInterval a N ∧
        (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
        (((negativePart A τ ∩ tailInterval a N) \ F).card : ℝ) ≤
          (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) ∧
        (N : ℝ) / 2 ≤ F.card ∧
        (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) ≤ κ ∧
        P ⊆ positivePart A τ ∧
        (reciprocalSum P : ℝ) < (Real.log (1 / a) + 1) / Real.log N ∧
        (P.card : ℝ) < (N : ℝ) * ((Real.log (1 / a) + 1) / Real.log N) ∧
        (∀ b : ℕ, 0 < b →
          InverseZeroSumFree b (excessCofactors (F.lcm id) b (positivePart A τ \ P))) ∧
        (1 - ε) * Real.log (Real.log (Real.log N)) ≤
          C + (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log N) *
            (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) +
              (Real.log (1 / a) + 1) / Real.log N := by
  obtain ⟨C, ρ₀, hρ₀, hWeighted⟩ := eventually_uniform_weighted_mass ε hε
  have hThreshold : Tendsto (fun N : ℕ => (Real.log (1 / a) + 1) / Real.log N)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top).const_mul (Real.log (1 / a) + 1)
  refine ⟨C, ?_⟩
  filter_upwards [hWeighted,
    eventually_dense_sign_core_with_deletion a K (min ρ₀ κ) ha hMass (lt_min hρ₀ hκ),
    eventually_primitive_common_mass_lower K ε hε,
    eventually_primitive_common_mass_lower K (1 / 2) (by norm_num),
    hThreshold.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_logloglog_nat.eventually (eventually_ge_atTop (4 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)]
    with N hBound hCore hCommon hHalfMass hThresholdSmall hTriple hLog hN
  intro A δ hA hPrimitive hDeficit
  obtain ⟨B, hChoice, F, hF, hSmooth, hPrune, hLoss, hCard, hApprox, hRho, hTargets⟩ :=
    hCore A δ hA hPrimitive hDeficit
  obtain ⟨τ, hτ, hNegative⟩ := exists_signing_with_negative_part hPrimitive hChoice
  have hFNegative : F ⊆ negativePart A τ ∩ tailInterval a N := by
    rw [hNegative]
    exact hF
  have hFPrefix : F ⊆ Finset.Icc 1 N :=
    (hF.trans Finset.inter_subset_right).trans (tailInterval_subset a N)
  have hD : F.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by
    intro n hn
    exact (show 0 < n from (Finset.mem_Icc.mp (hFPrefix hn)).1).ne')
  let η : ℝ := (Real.log (1 / a) + 1) / Real.log N
  have hη : 0 < η := div_pos (by linarith) hLog
  have hMassLower := (hHalfMass A τ hA hτ hDeficit).1
  have hEnough : η + 1 ≤ (reciprocalSum (positivePart A τ) : ℝ) := by
    change (Real.log (1 / a) + 1) / Real.log N + 1 ≤ _
    nlinarith only [hMassLower, hTriple, hThresholdSmall]
  have hRepresent : ∀ r : ℚ, r.den ∣ F.lcm id → η ≤ (r : ℝ) → (r : ℝ) < η + 1 →
      ∃ U ⊆ negativePart A τ, reciprocalSum U = r := by
    intro r hDen hLower hUpper
    have hUpperTwo : (r : ℝ) ≤ 2 := by
      change (r : ℝ) < (Real.log (1 / a) + 1) / Real.log N + 1 at hUpper
      linarith only [hUpper, hThresholdSmall]
    obtain ⟨U, hUF, hSum⟩ := hTargets r hDen hLower hUpperTwo
    exact ⟨U, hUF.trans (hFNegative.trans Finset.inter_subset_left), hSum⟩
  obtain ⟨P, hP, hPCompatible, hPMass, hPCard, hFree⟩ :=
    hτ.exists_peeled_inverse_free_groups N (F.lcm id) hN hD hA η hη hEnough hRepresent
  have hRemaining : positivePart A τ \ P ⊆ Finset.Icc 1 N :=
    Finset.sdiff_subset.trans ((Finset.filter_subset _ _).trans hA)
  have hWeightedMass := hBound (F.lcm id) (positivePart A τ \ P) hD hRemaining hFree
    (hRho.trans (min_le_left _ _))
  have hSplitQ : reciprocalSum (positivePart A τ \ P) + reciprocalSum P =
      reciprocalSum (positivePart A τ) := Finset.sum_sdiff hP
  have hSplit : (reciprocalSum (positivePart A τ \ P) : ℝ) + (reciprocalSum P : ℝ) =
      (reciprocalSum (positivePart A τ) : ℝ) := by exact_mod_cast hSplitQ
  have hCommonMass := (hCommon A τ hA hτ hDeficit).1
  have hPruneNegative : (((negativePart A τ ∩ tailInterval a N) \ F).card : ℝ) ≤
      (N : ℝ) * (Real.log N) ^ (-(1 / 40 : ℝ)) := by
    rw [hNegative]
    exact hPrune
  refine ⟨τ, F, P, hτ, hFNegative, hSmooth, hPruneNegative, hCard,
    hRho.trans (min_le_right _ _), hP, hPMass, hPCard, hFree, ?_⟩
  change (1 - ε) * Real.log (Real.log (Real.log N)) ≤
    C + (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log N) *
      (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) + η
  linarith only [hCommonMass, hSplit, hWeightedMass, hPMass]

end Erdos319Sharp
