import Erdos319Sharp.QuantitativeLocalization
import Erdos319Sharp.Representation

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- Exact rational representation with the varying minimum denominator,
variance and prime-power fiber masses used in the sharp-deficit argument. -/
theorem eventually_exact_target_with_log_mass (l m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c τ η : ℝ, ∀ A : Finset ℕ,
      0 < c → c ≤ 1 → 0 < τ →
      (Real.log N) ^ (-3 / 100 : ℝ) ≤ c → 1 / (Real.log N) ^ l ≤ τ →
      (Real.log N) ^ (-1 / 25 : ℝ) ≤ η →
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ divisorPrimePowers N A,
        η ≤ (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) →
      (N : ℝ) / (Real.log N) ^ m ≤ (A.card : ℝ) →
      ∀ r : ℚ, 0 ≤ r → r.den ∣ A.lcm id →
      ∀ p : ℕ → ℝ, (∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) →
      (∀ n ∈ A, τ ≤ p n * (1 - p n)) →
      (∑ n ∈ A, p n / n) = (r : ℝ) →
      ∃ B ⊆ A, reciprocalSum B = r := by
  filter_upwards [eventually_exact_target_of_localization 1 l m,
    eventually_rareDivisorSet_localization_with_log_mass l,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hExact hLocal hL c τ η A hc hcOne hτ hcLower hτLower hηLower
      hA hMin hSmooth hMult hMass hCard
  have hcNat : 1 / (Real.log N) ^ 1 ≤ c := by
    calc
      _ = (Real.log N) ^ (-1 : ℝ) := by simp [Real.rpow_neg_one]
      _ ≤ (Real.log N) ^ (-3 / 100 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ c := hcLower
  exact hExact c τ A hc hcOne hτ hcNat hτLower hA hMin hSmooth hMult hCard
    (fun h => hLocal c τ η A h hc hcOne hτ hcLower hτLower hηLower hA hMin hSmooth hMult hMass)

end Erdos319Sharp
