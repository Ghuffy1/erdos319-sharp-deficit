import Erdos319

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- Finite large-frequency estimate with explicit localization hypotheses.

The proof uses the classification argument in the pinned density-one source,
H0W4RD-dev/erdos319-density-one at 3c1e1c6f349b6b5628fdc01386a6ac5ed55b7b61.
Its parameters may vary with the ambient size. The localization hypothesis
must still be established at those parameters.
-/
theorem large_frequency_bound_of_localization {Q x N : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (c τ : ℝ)
    (hN : 0 < N) (hc : 0 < c) (hc1 : c ≤ 1) (hτ : 0 < τ)
    (hLL : 0 < Real.log (Real.log N))
    (hQ : Q = A.lcm id) (hAne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hmin : ∀ n ∈ A, c * N ≤ (n : ℝ))
    (hMult : ∀ n ∈ A,
      (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2)
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1)
    (hVar : ∀ n ∈ A, τ ≤ p n * (1 - p n))
    (hLocal : ∀ h : ℤ, ∃ y : ℤ,
      |(y : ℝ) - h| < localizationWidth c N / 2 ∧
        ∀ q ∈ rareDivisorSet c τ N A h, (q : ℤ) ∣ y)
    (hSmall : classificationMajorant N < 1 / 4) :
    ‖∑ h ∈ Finset.univ.filter (fun h : ZMod Q => c * N / 2 < |(h.valMinAbs : ℝ)|),
      fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h‖ ≤ 1 / 4 := by
  classical
  let T := divisorPrimePowers N A
  let F := Finset.univ.filter (fun z : ZMod Q => c * N / 2 < |(z.valMinAbs : ℝ)|)
  let missing := fun z : ZMod Q => T \ rareDivisorSet c τ N A z.valMinAbs
  let f := fun z : ZMod Q => fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) z
  have hTsub : T ⊆ Finset.Icc 1 N := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hTpos : ∀ q ∈ T, 0 < q := fun q hq => (Finset.mem_Icc.mp (hTsub hq)).1
  have hTN : ∀ q ∈ T, q ≤ N := fun q hq => (Finset.mem_Icc.mp (hTsub hq)).2
  have hTcard : T.card ≤ N := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hTsub
  have hQPrime : Q = T.lcm id := hQ.trans (divisorPrimePowers_lcm N A hA).symm
  have hDiv : ∀ n ∈ A, n ∣ Q := by
    intro n hn
    rw [hQ]
    exact Finset.dvd_lcm hn
  have hKmin : localizationWidth c N ≤ c * N := by
    have hU : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
    exact mul_le_of_le_one_right (mul_nonneg hc.le (Nat.cast_nonneg N))
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hU))
  have hMQ : c * (N : ℝ) ≤ Q := by
    obtain ⟨n, hn⟩ := hAne
    have hnQ : n ≤ Q := Nat.le_of_dvd (NeZero.pos Q) (hDiv n hn)
    exact (hmin n hn).trans (by exact_mod_cast hnQ)
  have hKQ := hKmin.trans hMQ
  have hKN := localizationWidth_le c N hc.le hc1
  have hLocalA : ∀ h : ℤ, ∃ y : ℤ, |(y : ℝ) - h| < localizationWidth c N / 2 ∧
      ∀ q ∈ rareDivisorSet c τ N A h, (q : ℤ) ∣ y :=
    hLocal
  have hMissing : ∀ z ∈ F, missing z ⊆ T ∧ (missing z).Nonempty := by
    intro z hz
    refine ⟨Finset.sdiff_subset, ?_⟩
    by_contra hEmpty
    have hSub : T ⊆ rareDivisorSet c τ N A z.valMinAbs := by
      intro q hq
      by_contra hNot
      exact hEmpty ⟨q, Finset.mem_sdiff.mpr ⟨hq, hNot⟩⟩
    obtain ⟨y, hy, hyDiv⟩ := hLocalA z.valMinAbs
    have hyQ : (Q : ℤ) ∣ y := by
      rw [hQPrime]
      exact nat_lcm_dvd_int T y (fun q hq => hyDiv q (hSub hq))
    exact no_large_frequency_with_full_lcm z y (localizationWidth c N) (c * N) hKQ hKmin
      hy hyQ (Finset.mem_filter.mp hz).2
  have hCount : ∀ B ∈ T.powerset.erase ∅,
      (F.filter (fun z => missing z = B)).card ≤ (2 * N + 1) * N ^ B.card := by
    intro B hB
    let D := T \ B
    have hBT : B ⊆ T := Finset.mem_powerset.mp (Finset.mem_erase.mp hB).2
    have hDiff : T \ D = B := by
      ext q
      simp only [D, Finset.mem_sdiff]
      constructor
      · rintro ⟨hqT, hqNotD⟩
        by_contra hqNotB
        exact hqNotD ⟨hqT, hqNotB⟩
      · intro hqB
        exact ⟨hBT hqB, fun hh => hh.2 hqB⟩
    have hClassLocal : ∀ z ∈ F.filter (fun z => missing z = B),
        ∃ y : ℤ, |(y : ℝ) - z.valMinAbs| < localizationWidth c N / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ y := by
      intro z hz
      have hzi := Finset.mem_filter.mp hz
      obtain ⟨y, hy, hyDiv⟩ := hLocalA z.valMinAbs
      refine ⟨y, hy, ?_⟩
      intro q hq
      apply hyDiv q
      by_contra hNot
      have hqMissing : q ∈ missing z := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1, hNot⟩
      rw [hzi.2] at hqMissing
      exact (Finset.mem_sdiff.mp hq).2 hqMissing
    have hC := card_localized_frequency_class N (localizationWidth c N) T D _ hQPrime
      Finset.sdiff_subset hTpos hTN hKN hClassLocal
    rw [hDiff] at hC
    exact hC
  have hNorm : ∀ z ∈ F, ‖f z‖ ≤ (Real.exp (-100 * Real.log N)) ^ (missing z).card := by
    intro z hz
    have hBad : ∀ q ∈ missing z, localizationRarity c τ N ≤
        ((((A.filter (fun n => q ∣ n)).filter
          (fun n => localizationWidth c N / 2 ≤ |((z.valMinAbs : ZMod n).valMinAbs : ℝ)|)).card : ℝ)) := by
      intro q hq
      have hqi := Finset.mem_sdiff.mp hq
      apply le_of_not_gt
      intro hRare
      exact hqi.2 (Finset.mem_filter.mpr ⟨hqi.1, hRare⟩)
    have hh := fourierTerm_norm_of_many_bad_groups (x := x) A (missing z) p z.valMinAbs c τ hN hc hτ hLL
      hA hDiv hp hVar hMult Finset.sdiff_subset hBad
    simpa only [f, ZMod.coe_valMinAbs] using hh
  have hBound := frequency_sum_le_classificationMajorant F T f missing N hTcard hMissing hCount hNorm
  exact hBound.trans hSmall.le


/-- The rarity cost is uniform for density and variance bounded below by
fixed inverse powers of the logarithm. -/
theorem eventually_localization_cost_of_log_bounds (k l : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c τ : ℝ,
      0 < c → 0 < τ →
      1 / (Real.log N) ^ k ≤ c → 1 / (Real.log N) ^ l ≤ τ →
      ∀ q : ℕ, (q : ℝ) ≤ smoothCutoff 6 N →
        (q : ℝ) * localizationRarity c τ N / (c * N) ≤
          1 / (2 * (Real.log (Real.log N)) ^ 2) := by
  have hLimit : Tendsto (fun N : ℕ =>
      50 * (Real.log N) ^ (l + 3 * k + 1) *
        (Real.log (Real.log N)) ^ 4 * Real.exp (-4 * localizationPower N))
      atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_log_pow_loglog_pow_exp_neg_localizationPower
        (l + 3 * k + 1) 4 4 (by norm_num)).const_mul 50
  filter_upwards [hLimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hSmall hL hLL hN c τ hc hτ hcLower hτLower q hq
  have hBase : 0 < (1 / (Real.log N) ^ l) * (1 / (Real.log N) ^ k) ^ 3 := by positivity
  have hProduct : (1 / (Real.log N) ^ l) * (1 / (Real.log N) ^ k) ^ 3 ≤ τ * c ^ 3 := by
    exact mul_le_mul hτLower (pow_le_pow_left₀ (by positivity) hcLower 3)
      (by positivity) hτ.le
  have hInverse : 50 / (τ * c ^ 3) ≤
      50 / ((1 / (Real.log N) ^ l) * (1 / (Real.log N) ^ k) ^ 3) :=
    div_le_div_of_nonneg_left (by norm_num) hBase hProduct
  have hIdentity : 50 / ((1 / (Real.log N) ^ l) * (1 / (Real.log N) ^ k) ^ 3) =
      50 * (Real.log N) ^ (l + 3 * k) := by
    rw [pow_add, Nat.mul_comm 3 k, pow_mul]
    field_simp [hL.ne']
  rw [hIdentity] at hInverse
  have hBound := localizationRarity_scaled_cost c τ N q hc hτ hN hq
  have hUpper : (Real.log (Real.log N)) ^ 2 *
      ((q : ℝ) * localizationRarity c τ N / (c * N)) ≤
        50 * (Real.log N) ^ (l + 3 * k + 1) *
          (Real.log (Real.log N)) ^ 4 * Real.exp (-4 * localizationPower N) := by
    calc
      _ ≤ (50 / (τ * c ^ 3)) * Real.log N *
          (Real.log (Real.log N)) ^ 4 * Real.exp (-4 * localizationPower N) := hBound
      _ ≤ (50 * (Real.log N) ^ (l + 3 * k)) * Real.log N *
          (Real.log (Real.log N)) ^ 4 * Real.exp (-4 * localizationPower N) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (Real.log N)) ^ 2)).mpr
  nlinarith only [hUpper, hSmall]

end Erdos319Sharp
