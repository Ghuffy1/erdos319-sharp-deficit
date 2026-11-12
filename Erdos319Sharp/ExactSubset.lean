import Erdos319Sharp.CorrectedRepresentation

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem selection_probability_of_mass_bounds (L R r : ℝ) (hL : 2 ≤ L) (hr : 0 < r)
    (hLower : (1 + 1 / L) * r ≤ R) (hUpper : R ≤ L * r) :
    0 < R ∧ (0 ≤ r / R ∧ r / R ≤ 1) ∧ 1 / L ^ 3 ≤ (r / R) * (1 - r / R) := by
  have hLPos : 0 < L := by linarith
  have hRPos : 0 < R := (mul_pos (by positivity) hr).trans_le hLower
  have hpPos : 0 < r / R := div_pos hr hRPos
  have hpLower : 1 / L ≤ r / R := by
    apply (le_div_iff₀ hRPos).mpr
    have h := div_le_div_of_nonneg_right hUpper hLPos.le
    have hEq : (L * r) / L = r := by field_simp [hLPos.ne']
    rw [hEq] at h
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h
  have hCross : r * (L + 1) ≤ L * R := by
    have h := mul_le_mul_of_nonneg_left hLower hLPos.le
    have hEq : L * ((1 + 1 / L) * r) = r * (L + 1) := by
      field_simp [hLPos.ne']
    rwa [hEq] at h
  have hpUpper : r / R ≤ L / (L + 1) := (div_le_div_iff₀ hRPos (by linarith)).mpr hCross
  have hpOne : r / R ≤ 1 := hpUpper.trans ((div_le_one (by linarith)).mpr (by linarith))
  have hComplement : 1 / (2 * L) ≤ 1 - r / R := by
    have hGap : 1 / (L + 1) ≤ 1 - r / R := by
      have hEq : L / (L + 1) + 1 / (L + 1) = 1 := by field_simp
      linarith
    exact (one_div_le_one_div_of_le (by linarith : 0 < L + 1) (by linarith)).trans hGap
  have hProduct : (1 / L) * (1 / (2 * L)) ≤ (r / R) * (1 - r / R) :=
    mul_le_mul hpLower hComplement (by positivity) hpPos.le
  have hCube : 2 * L ^ 2 ≤ L ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hL (sq_nonneg L)
    nlinarith only [h]
  refine ⟨hRPos, ⟨hpPos.le, hpOne⟩, ?_⟩
  calc
    1 / L ^ 3 ≤ 1 / (2 * L ^ 2) := one_div_le_one_div_of_le (by positivity) hCube
    _ = (1 / L) * (1 / (2 * L)) := by ring
    _ ≤ (r / R) * (1 - r / R) := hProduct

/-- The quantitative exact-subsum consequence needed by the sharp proof.
The total reciprocal mass lies between `(1 + 1/log N) r` and `(log N) r`. -/
theorem eventually_exact_subset_from_mass_bounds (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c η : ℝ, ∀ A : Finset ℕ,
      0 < c → c ≤ 1 →
      (Real.log N) ^ (-3 / 100 : ℝ) ≤ c → (Real.log N) ^ (-1 / 25 : ℝ) ≤ η →
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ divisorPrimePowers N A,
        η ≤ (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) →
      (N : ℝ) / (Real.log N) ^ m ≤ (A.card : ℝ) →
      ∀ r : ℚ, 0 < r → r.den ∣ A.lcm id →
      (1 + 1 / Real.log N) * (r : ℝ) ≤ (reciprocalSum A : ℝ) →
      (reciprocalSum A : ℝ) ≤ Real.log N * (r : ℝ) →
      ∃ B ⊆ A, reciprocalSum B = r := by
  filter_upwards [eventually_exact_target_with_log_mass 3 m,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ))]
    with N hExact hL c η A hc hcOne hcLower hηLower hA hMin hSmooth hMult hMass hCard
      r hr hDen hLower hUpper
  have hLPos : 0 < Real.log N := by linarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨hR, hp, hVar⟩ := selection_probability_of_mass_bounds (Real.log N)
    (reciprocalSum A : ℝ) (r : ℝ) hL hrR hLower hUpper
  let p : ℕ → ℝ := fun _ => (r : ℝ) / (reciprocalSum A : ℝ)
  have hRealSum : (reciprocalSum A : ℝ) = ∑ n ∈ A, (1 : ℝ) / n := by
    rw [reciprocalSum_eq_baseline]
    exact Erdos319Formal.reciprocalSum_real A
  have hMean : (∑ n ∈ A, p n / n) = (r : ℝ) := by
    calc
      (∑ n ∈ A, p n / n) = ((r : ℝ) / (reciprocalSum A : ℝ)) * (∑ n ∈ A, (1 : ℝ) / n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [p]
        ring
      _ = ((r : ℝ) / (reciprocalSum A : ℝ)) * (reciprocalSum A : ℝ) := by rw [← hRealSum]
      _ = (r : ℝ) := div_mul_cancel₀ _ hR.ne'
  exact hExact c (1 / (Real.log N) ^ 3) η A hc hcOne (by positivity) hcLower le_rfl hηLower
    hA hMin hSmooth hMult hMass hCard r hr.le hDen p (fun _ _ => hp) (fun _ _ => hVar) hMean

end Erdos319Sharp
