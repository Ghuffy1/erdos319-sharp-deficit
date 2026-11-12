import Erdos319Sharp.Baseline

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- The lcm estimate is uniform over all sets with the stated smoothness cutoff. -/
theorem eventually_uniform_smooth_lcm_growth (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff a N) n) →
      ((A.lcm id : ℕ) : ℝ) ≤ Real.exp (((c * N) ^ 2 / N) / 4) ∧
        Real.log 4 < ((c * N) ^ 2 / N) / 4 := by
  have hC : 0 < c ^ 2 / 4 := by positivity
  have hsmall := (tendsto_log_times_smooth_factor a ha).eventually (Iio_mem_nhds hC)
  have hsize : ∀ᶠ N : ℕ in atTop, Real.log 4 < (c ^ 2 / 4) * N :=
    ((tendsto_const_mul_atTop_of_pos hC).mpr tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (Real.log 4))
  filter_upwards [hsmall, hsize, eventually_gt_atTop (0 : ℕ),
    (tendsto_smoothCutoff a).eventually (eventually_ge_atTop (1 : ℝ))]
      with N hsmallN hsizeN hN hS A hSmooth
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hSpos := smoothCutoff_pos a hN
  have hlogS : Real.log (smoothCutoff a N) ≤ Real.log N :=
    Real.log_le_log hSpos (smoothCutoff_le a ha.le N)
  have hexponent : smoothCutoff a N * Real.log (smoothCutoff a N) ≤
      (c ^ 2 / 4) * N := by
    calc
      _ ≤ smoothCutoff a N * Real.log N :=
        mul_le_mul_of_nonneg_left hlogS hSpos.le
      _ = (Real.log N * Real.exp (-a * (Real.log N) ^ (4 / 5 : ℝ))) * N := by
        unfold smoothCutoff
        ring
      _ ≤ (c ^ 2 / 4) * N := mul_le_mul_of_nonneg_right hsmallN.le hNR.le
  have heq : ((c * N) ^ 2 / (N : ℝ)) / 4 = (c ^ 2 / 4) * N := by
    field_simp [hNR.ne']
  rw [heq]
  exact ⟨(smooth_lcm_le_exp A (smoothCutoff a N) hS hSmooth).trans
    (Real.exp_le_exp.mpr hexponent), hsizeN⟩

/-- A pointwise uniform form of the existing exact-target Fourier argument.

The ambient size and rational target can both vary with an external parameter.
All lower bounds on density and Bernoulli variance in this theorem are fixed.
-/
theorem eventually_uniform_exact_target (c α τ : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hα : 0 < α) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ divisorPrimePowers N A, 1 / (Real.log (Real.log N)) ^ 2 ≤
        (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) →
      α * N ≤ (A.card : ℝ) →
      ∀ r : ℚ, 0 ≤ r → r.den ∣ A.lcm id →
      ∀ p : ℕ → ℝ, (∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) →
      (∀ n ∈ A, τ ≤ p n * (1 - p n)) →
      (∑ n ∈ A, p n / n) = (r : ℝ) →
      ∃ B ⊆ A, reciprocalSum B = r := by
  filter_upwards [eventually_uniform_smooth_lcm_growth 6 c (by norm_num) hc,
    eventually_major_parameters c hc,
    eventually_middle_parameters α τ hα hτ,
    eventually_large_frequency_bound_regular c τ hc hc1 hτ,
    eventually_gt_atTop (0 : ℕ)]
      with N hGrowth hMajor hMiddle hLarge hN A hA hmin hSmooth hMult hMass hCard
        r hr hDen p hp hVar hMean
  let Q := A.lcm id
  have hPos : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  have hQPos : 0 < Q :=
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos n hn).ne'))
  letI : NeZero Q := ⟨hQPos.ne'⟩
  obtain ⟨x, hx⟩ := exists_numerator_over_common (Q := Q) r hr hDen
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hAne : A.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos hα hNR).trans_le hCard
  have hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q := by
    rw [hMean]
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) hx
  have hMN : c * (N : ℝ) ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hNR.le
  have hDiv : ∀ n ∈ A, n ∣ Q := fun n hn => Finset.dvd_lcm hn
  have hLargeN := hLarge Q x A p rfl hAne hA hmin hSmooth hMult hMass hp hVar
  have hGrowthN := hGrowth A hSmooth
  obtain ⟨B, hB, hSum⟩ := exact_subset_of_large_frequency_bound A p
    ((N : ℝ) ^ (3 / 5 : ℝ)) (c * N) τ hN (mul_pos hc hNR) hMN
    (Real.rpow_nonneg hNR.le _) hMajor.1 hA hmin hDiv hp hτ.le hVar hExpected
    hMajor.2.1 hMajor.2.2 (hMiddle A.card hCard) hLargeN hGrowthN.1 hGrowthN.2
  exact ⟨B, hB, hSum.trans hx.symm⟩

theorem selection_probability_variance_bound {β R r : ℝ}
    (hβ : 0 < β) (hR : β / 2 ≤ R ∧ R ≤ 1)
    (hr : β / 8 ≤ r ∧ r ≤ β / 4) :
    0 ≤ r / R ∧ r / R ≤ 1 ∧ β / 16 ≤ (r / R) * (1 - r / R) := by
  have hRpos : 0 < R := lt_of_lt_of_le (by linarith) hR.1
  have hlo : β / 8 ≤ r / R := by
    apply (le_div_iff₀ hRpos).mpr
    have := mul_le_mul_of_nonneg_left hR.2 (show 0 ≤ β / 8 by linarith)
    linarith
  have hhi : r / R ≤ 1 / 2 := by
    apply (div_le_iff₀ hRpos).mpr
    linarith [hR.1, hr.2]
  have hp : 0 ≤ r / R := by linarith
  refine ⟨hp, by linarith, ?_⟩
  have hproduct := mul_nonneg hp (show 0 ≤ 1 / 2 - r / R by linarith)
  nlinarith

/-- The fixed-density exact-target conclusion used on a dyadic interval. -/
theorem eventually_uniform_dyadic_target (c β : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ divisorPrimePowers N A, 1 / (Real.log (Real.log N)) ^ 2 ≤
        (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) →
      (β / 2) * N ≤ (A.card : ℝ) →
      β / 2 ≤ (reciprocalSum A : ℝ) → (reciprocalSum A : ℝ) ≤ 1 →
      ∀ r : ℚ, β / 8 ≤ (r : ℝ) → (r : ℝ) ≤ β / 4 → r.den ∣ A.lcm id →
      ∃ B ⊆ A, reciprocalSum B = r := by
  filter_upwards [eventually_uniform_exact_target c (β / 2) (β / 16)
    hc hc1 (by linarith) (by linarith)] with N hExact
  intro A hA hmin hSmooth hMult hMass hCard hRlo hRhi r hrlo hrhi hDen
  have hRpos : 0 < (reciprocalSum A : ℝ) := by linarith
  have hprob := selection_probability_variance_bound hβ ⟨hRlo, hRhi⟩ ⟨hrlo, hrhi⟩
  apply hExact A hA hmin hSmooth hMult hMass hCard r
    (by exact_mod_cast (show 0 ≤ (r : ℝ) by linarith)) hDen
    (fun _ => (r : ℝ) / (reciprocalSum A : ℝ))
    (fun _ _ => ⟨hprob.1, hprob.2.1⟩) (fun _ _ => hprob.2.2)
  exact constant_probability_mean A (r : ℝ) hRpos

end Erdos319Sharp
