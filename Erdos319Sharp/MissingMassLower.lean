import Erdos319Sharp.DenseCorePeeling

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_dense_core_missing_mass_lower (a K ε κ : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) (hε : 0 < ε) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
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
        (Real.exp (-Real.eulerMascheroniConstant) - ε) * Real.log (Real.log (Real.log N)) ≤
          Real.log (Real.log N) * (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) := by
  let E : ℝ := Real.exp Real.eulerMascheroniConstant
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hE : 0 < E := Real.exp_pos _
  have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hNumerator : Tendsto (fun k => 1 - 2 * u k) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hu.const_mul 2)
  have hDenominator : Tendsto (fun k => E + u k) atTop (𝓝 E) := by
    simpa only [add_zero] using tendsto_const_nhds.add hu
  have hRatio : Tendsto (fun k => (1 - 2 * u k) / (E + u k)) atTop (𝓝 E⁻¹) := by
    simpa only [one_div, Pi.div_def] using hNumerator.div hDenominator hE.ne'
  have hLower : Real.exp (-Real.eulerMascheroniConstant) - ε < E⁻¹ := by
    dsimp [E]
    rw [Real.exp_neg]
    linarith only [hε]
  obtain ⟨k, hk⟩ := (hRatio.eventually (Ioi_mem_nhds hLower)).exists
  let θ := u k
  have hθ : 0 < θ := by dsimp [θ, u]; positivity
  obtain ⟨C, hPrep⟩ := eventually_dense_core_peeling a K θ κ ha hMass hθ hκ
  have hThreshold : Tendsto (fun N : ℕ => (Real.log (1 / a) + 1) / Real.log N)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top).const_mul (Real.log (1 / a) + 1)
  filter_upwards [hPrep,
    tendsto_logloglog_nat.eventually (eventually_ge_atTop ((C + 1) / θ)),
    hThreshold.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_positive_scale] with N hPrepared hLarge hThresholdSmall hScale
  intro A δ hA hPrimitive hDeficit
  obtain ⟨τ, F, P, hτ, hF, hSmooth, hPrune, hCard, hRho, hP, hPMass, hPCard,
    hFree, hComparison⟩ := hPrepared A δ hA hPrimitive hDeficit
  refine ⟨τ, F, P, hτ, hF, hSmooth, hPrune, hCard, hRho, hP, hPMass, hPCard, hFree, ?_⟩
  let μ := Real.log (Real.log (Real.log N))
  let loglog := Real.log (Real.log N)
  let ρ : ℝ := (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ)
  have hConstant : C + 1 ≤ θ * μ := by
    have h := (div_le_iff₀ hθ).mp hLarge
    simpa only [mul_comm] using h
  have hMain : (1 - 2 * θ) * μ ≤ (E + θ) * (loglog * ρ) := by
    change (1 - θ) * μ ≤ C + (E + θ) * loglog * ρ +
      (Real.log (1 / a) + 1) / Real.log N at hComparison
    nlinarith only [hComparison, hConstant, hThresholdSmall]
  have hDenPos : 0 < E + θ := add_pos hE hθ
  change (Real.exp (-Real.eulerMascheroniConstant) - ε) * μ ≤ loglog * ρ
  calc
    (Real.exp (-Real.eulerMascheroniConstant) - ε) * μ ≤
        ((1 - 2 * θ) / (E + θ)) * μ :=
      mul_le_mul_of_nonneg_right hk.le hScale.2.2.le
    _ = ((1 - 2 * θ) * μ) / (E + θ) := by ring
    _ ≤ loglog * ρ := (div_le_iff₀ hDenPos).mpr (by nlinarith only [hMain])

end Erdos319Sharp
