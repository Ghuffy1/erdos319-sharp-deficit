import Erdos319Sharp.WeightedGroupMass
import Erdos319Sharp.PrimitivePeeling

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_uniform_weighted_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ (D : ℕ) (A : Finset ℕ),
      D ≠ 0 → A ⊆ Finset.Icc 1 N →
      (∀ b : ℕ, 0 < b → InverseZeroSumFree b (excessCofactors D b A)) →
      (reciprocalSum (firstMissingPowers D N) : ℝ) ≤ δ →
      (reciprocalSum A : ℝ) ≤ C + (Real.exp Real.eulerMascheroniConstant + ε) *
        Real.log (Real.log N) * (reciprocalSum (firstMissingPowers D N) : ℝ) := by
  let a : ℝ := Real.exp Real.eulerMascheroniConstant
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hCoefficient : Tendsto (fun k => (a + u k) * (1 + u k) ^ 2) atTop (𝓝 a) := by
    have hLeft : Tendsto (fun k => a + u k) atTop (𝓝 (a + 0)) := tendsto_const_nhds.add hu
    have hRight : Tendsto (fun k => 1 + u k) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hu
    simpa only [add_zero, one_pow, mul_one] using hLeft.mul (hRight.pow 2)
  obtain ⟨k, hk⟩ := (hCoefficient.eventually (Iio_mem_nhds (by linarith : a < a + ε))).exists
  let η := u k
  have hη : 0 < η := by dsimp [η, u]; positivity
  have hCoef : (a + η) * (1 + η) ^ 2 ≤ a + ε := hk.le
  obtain ⟨Y₀, hY₀, hWeighted⟩ := eventually_weighted_excess_mass η hη
  have hInv : Tendsto (fun Y : ℕ => (Y : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hGapLimit : Tendsto (fun Y : ℕ => (1 - (Y : ℝ)⁻¹)⁻¹) atTop (𝓝 1) := by
    have hSub : Tendsto (fun Y : ℕ => 1 - (Y : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hInv
    have h := hSub.inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa only [sub_zero, inv_one] using h
  obtain ⟨Y, hYGap, hY⟩ := ((hGapLimit.eventually
    (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + η))).and (eventually_ge_atTop Y₀)).exists
  let δ := Real.log (1 + η) / 2
  let C := 3 * weightedPrimeProduct Y.primesLE (1 / 2)
  have hδ : 0 < δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  refine ⟨C, δ, hδ, ?_⟩
  filter_upwards [hWeighted Y hY,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ))] with N hMain hLogLog
  intro D A hD hA hFree hSmall
  let ρ : ℝ := (reciprocalSum (firstMissingPowers D N) : ℝ)
  have hρ : 0 ≤ ρ := by
    have h : (0 : ℚ) ≤ reciprocalSum (firstMissingPowers D N) :=
      Finset.sum_nonneg (fun n _ => by positivity)
    change (0 : ℝ) ≤ (reciprocalSum (firstMissingPowers D N) : ℝ)
    exact_mod_cast h
  have hExp : Real.exp (2 * ρ) ≤ 1 + η := by
    calc
      Real.exp (2 * ρ) ≤ Real.exp (Real.log (1 + η)) := by
        apply Real.exp_le_exp.mpr
        change ρ ≤ Real.log (1 + η) / 2 at hSmall
        linarith
      _ = 1 + η := Real.exp_log (by linarith)
  have hAη : 0 ≤ a + η := by dsimp [a]; positivity
  have hCoefficientBound : (a + η) * (1 - (Y : ℝ)⁻¹)⁻¹ * Real.exp (2 * ρ) ≤ a + ε := by
    calc
      _ ≤ ((a + η) * (1 + η)) * (1 + η) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hYGap.le hAη) hExp
          (Real.exp_nonneg _) (mul_nonneg hAη (by linarith))
      _ = (a + η) * (1 + η) ^ 2 := by ring
      _ ≤ a + ε := hCoef
  have hBound := hMain D A hD hA hFree
  change (reciprocalSum A : ℝ) ≤ C + (a + η) * Real.log (Real.log N) *
    (1 - (Y : ℝ)⁻¹)⁻¹ * Real.exp (2 * ρ) * ρ at hBound
  have hProduct := mul_le_mul_of_nonneg_right hCoefficientBound (mul_nonneg hLogLog hρ)
  change (reciprocalSum A : ℝ) ≤ C + (a + ε) * Real.log (Real.log N) * ρ
  nlinarith only [hBound, hProduct]

theorem eventually_primitive_positive_mass_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (A : Finset ℕ) (sign : ℕ → ℤˣ) (D : ℕ) (η : ℝ),
        A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A sign → D ≠ 0 → 0 < η →
        η + 1 ≤ (reciprocalSum (positivePart A sign) : ℝ) →
        (∀ r : ℚ, r.den ∣ D → η ≤ (r : ℝ) → (r : ℝ) < η + 1 →
          ∃ U ⊆ negativePart A sign, reciprocalSum U = r) →
        (reciprocalSum (firstMissingPowers D N) : ℝ) ≤ δ₀ →
        (reciprocalSum (positivePart A sign) : ℝ) ≤
          C + (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log N) *
            (reciprocalSum (firstMissingPowers D N) : ℝ) + η := by
  obtain ⟨C, δ₀, hδ₀, hWeighted⟩ := eventually_uniform_weighted_mass ε hε
  refine ⟨C, δ₀, hδ₀, ?_⟩
  filter_upwards [hWeighted, eventually_gt_atTop (0 : ℕ)] with N hBound hN
  intro A sign D η hA hPrimitive hD hη hMass hRepresent hSmall
  obtain ⟨P, hP, hCompatible, hPMass, hPCard, hFree⟩ :=
    hPrimitive.exists_peeled_inverse_free_groups N D hN hD hA η hη hMass hRepresent
  have hRemaining : positivePart A sign \ P ⊆ Finset.Icc 1 N :=
    (Finset.sdiff_subset).trans ((Finset.filter_subset _ _).trans hA)
  have hMassRemaining := hBound D (positivePart A sign \ P) hD hRemaining hFree hSmall
  have hSplitQ : reciprocalSum (positivePart A sign \ P) + reciprocalSum P =
      reciprocalSum (positivePart A sign) := Finset.sum_sdiff hP
  have hSplit : (reciprocalSum (positivePart A sign \ P) : ℝ) + (reciprocalSum P : ℝ) =
      (reciprocalSum (positivePart A sign) : ℝ) := by exact_mod_cast hSplitQ
  linarith

end Erdos319Sharp
