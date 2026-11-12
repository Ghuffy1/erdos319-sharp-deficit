import Erdos319Sharp.ConstructionSupport

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def constructionCoreError (η : ℝ) (N : ℕ) : ℝ :=
  constructionMass N / constructionPrimeBase N +
    (constructionTarget η N + 1 / constructionPrimeBase N) / constructionPrimeBase N

theorem tendsto_constructionCoreError (η : ℝ) :
    Tendsto (constructionCoreError η) atTop (𝓝 0) := by
  have hInverse : Tendsto (fun N : ℕ => (1 : ℝ) / constructionPrimeBase N) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_constructionPrimeBase)
  have hProduct : Tendsto (fun N : ℕ =>
      (constructionTarget η N + 1 / constructionPrimeBase N) / constructionPrimeBase N)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_div, one_mul, zero_add, mul_zero] using
      ((tendsto_constructionTarget η).add hInverse).mul hInverse
  change Tendsto (fun N : ℕ => constructionMass N / constructionPrimeBase N +
    (constructionTarget η N + 1 / constructionPrimeBase N) / constructionPrimeBase N)
      atTop (𝓝 0)
  simpa only [zero_add] using tendsto_constructionMass_div_primeBase.add hProduct

theorem constructionCore_mass_window (η : ℝ) (N : ℕ) (ρ e : ℝ)
    (hBase : 0 < constructionPrimeBase N)
    (hLowerP : constructionTarget η N ≤ ρ)
    (hUpperP : ρ < constructionTarget η N + 1 / constructionPrimeBase N)
    (hLowerE : constructionMass N * ρ ≤ e)
    (hUpperE : e ≤ constructionMass N * ρ + ρ / constructionPrimeBase N) :
    η ≤ e - Real.log (constructionMass N) ∧
      e - Real.log (constructionMass N) < η + constructionCoreError η N := by
  have hMassPos : 0 < constructionMass N := lt_of_lt_of_le (by norm_num) (constructionMass_one_le N)
  have hBasePos : (0 : ℝ) < constructionPrimeBase N := by exact_mod_cast hBase
  have hTarget : constructionMass N * constructionTarget η N = Real.log (constructionMass N) + η := by
    unfold constructionTarget
    field_simp [hMassPos.ne']
  have hLower := mul_le_mul_of_nonneg_left hLowerP hMassPos.le
  rw [hTarget] at hLower
  have hFirst := mul_lt_mul_of_pos_left hUpperP hMassPos
  have hSecond := div_le_div_of_nonneg_right hUpperP.le hBasePos.le
  have hUpper := hUpperE.trans_lt (add_lt_add_of_lt_of_le hFirst hSecond)
  have hExpression : constructionMass N * (constructionTarget η N + 1 / constructionPrimeBase N) +
      (constructionTarget η N + 1 / constructionPrimeBase N) / constructionPrimeBase N =
      Real.log (constructionMass N) + η + constructionCoreError η N := by
    rw [mul_add, hTarget]
    unfold constructionCoreError
    ring
  rw [hExpression] at hUpper
  constructor <;> linarith

theorem eventually_exists_constructionCore_window (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∃ P E : Finset ℕ,
      P ⊆ constructionPrimeBand N ∧ 2 ≤ P.card ∧
      constructionTarget η N ≤ (∑ p ∈ P, (1 : ℝ) / p) ∧
      (∑ p ∈ P, (1 : ℝ) / p) < constructionTarget η N + 1 / constructionPrimeBase N ∧
      MinimalCore (P.prod id) E ∧ E ⊆ Icc 1 N ∧
      (∀ n ∈ E, (n : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ)) ∧
      η ≤ (reciprocalSum E : ℝ) - Real.log (constructionMass N) ∧
      (reciprocalSum E : ℝ) - Real.log (constructionMass N) < η + constructionCoreError η N := by
  filter_upwards [eventually_exists_constructionCore η hη,
    tendsto_constructionPrimeBase.eventually (eventually_ge_atTop (1 : ℕ))] with N hN hB
  obtain ⟨P, E, hP, hCard, hLowerP, hUpperP, hCore, hE, hSmall, hLowerE, hUpperE⟩ := hN
  have hWindow := constructionCore_mass_window η N (∑ p ∈ P, (1 : ℝ) / p) (reciprocalSum E)
    (by omega) hLowerP hUpperP hLowerE hUpperE
  exact ⟨P, E, hP, hCard, hLowerP, hUpperP, hCore, hE, hSmall, hWindow⟩

end Erdos319Sharp
