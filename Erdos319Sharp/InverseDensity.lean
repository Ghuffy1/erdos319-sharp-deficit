import Erdos319Sharp.PrefixDensity

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem tendsto_harmonicPrimeCutoff : Tendsto harmonicPrimeCutoff atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_pow_atTop (by norm_num : (12 : ℕ) ≠ 0)).comp
    tendsto_log_coe_at_top)

/-- A uniform cardinality estimate with an explicit lower bound on the cofactor scale. -/
theorem eventually_inverse_zero_free_card_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (q t : ℕ) (A : Finset ℕ),
      0 < q → q ≤ N → A ⊆ Finset.Icc 1 t →
      (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (harmonicPrimeCutoff N : ℝ) ^ (2 * Real.log (harmonicPrimeCutoff N : ℝ)) ≤ t →
      (A.card : ℝ) ≤ ε * t := by
  classical
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp
    (eventually_large_factor_dyadic_density (ε / 4) (by linarith))
  obtain ⟨C, hC, hSmooth⟩ := exists_smooth_prefix_density_bound
  have hInv : Tendsto (fun Y : ℕ => (1 : ℝ) / Y) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hLogRatio : Tendsto (fun Y : ℕ => Real.log Y / Y) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hCoefficient : Tendsto (fun Y : ℕ => (1 : ℝ) / Y + C * Real.log Y / Y)
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero, zero_add] using hInv.add (hLogRatio.const_mul C)
  have hY : Tendsto (fun N : ℕ => (harmonicPrimeCutoff N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_harmonicPrimeCutoff
  filter_upwards [(hCoefficient.comp tendsto_harmonicPrimeCutoff).eventually
      (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2)),
    (Real.tendsto_log_atTop.comp hY).eventually (eventually_ge_atTop (4 : ℝ)),
    hY.eventually (eventually_ge_atTop ((Q : ℝ) / ε)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hCoefficientSmall hLogY hQScale hLogN
  intro q t A hq hqN hA hCop hFree hScale
  let Y := harmonicPrimeCutoff N
  have hYLog : 4 ≤ Real.log (Y : ℝ) := hLogY
  have hYOne : 1 < (Y : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith)
  have hYt : (Y : ℝ) ≤ t := by
    have hPower : (Y : ℝ) ^ (1 : ℝ) ≤ (Y : ℝ) ^ (2 * Real.log (Y : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hYOne.le (by linarith)
    simpa only [Real.rpow_one] using hPower.trans hScale
  have hPos : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  by_cases hSmallQ : q < Q
  · have hLength : (A.card : ℝ) < q := by
      exact_mod_cast InverseZeroSumFree.card_lt hq hPos hFree
    have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast hSmallQ.le
    have hCutoff : (Q : ℝ) ≤ ε * Y := by
      have h := (div_le_iff₀ hε).mp hQScale
      simpa only [mul_comm] using h
    exact (hLength.le.trans hqQ).trans (hCutoff.trans
      (mul_le_mul_of_nonneg_left hYt hε.le))
  · let High : Finset ℕ := A.filter (fun n : ℕ => ∃ p : ℕ, p.Prime ∧ Real.log q ≤ (p : ℝ) ∧ p ∣ n)
    let Small : Finset ℕ := A.filter (fun n : ℕ => ¬ ∃ p : ℕ, p.Prime ∧ Real.log q ≤ (p : ℝ) ∧ p ∣ n)
    have hHighA : High ⊆ A := Finset.filter_subset _ _
    have hSmallA : Small ⊆ A := Finset.filter_subset _ _
    have hHighCard : (High.card : ℝ) ≤ 2 * (ε / 4) * t := by
      apply card_le_of_dyadic_density (ε / 4) (by linarith) t High (hHighA.trans hA)
      exact hQ q (le_of_not_gt hSmallQ) High (fun n hn => hPos n (hHighA hn))
        (fun n hn => hCop n (hHighA hn)) (ZeroSumFree.mono hFree hHighA)
        (fun n hn => (Finset.mem_filter.mp hn).2)
    have hLogCutoff : Real.log N ≤ (Y : ℝ) := by
      have hPower : Real.log N ≤ (Real.log N) ^ 12 := by
        simpa only [pow_one] using pow_le_pow_right₀ hLogN (by norm_num : 1 ≤ 12)
      exact hPower.trans (Nat.le_ceil _)
    have hLogQ : Real.log q ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqN)
    have hSmoothSmall : ∀ n ∈ Small, n.maxPrimeFac ≤ Y := by
      intro n hn
      by_contra hNot
      have hPrimeLarge : (Y : ℝ) < n.maxPrimeFac := by
        exact_mod_cast (lt_of_not_ge hNot)
      have hPrimeOne : 1 < n.maxPrimeFac := by
        exact_mod_cast hYOne.trans hPrimeLarge
      have hPrime := Nat.prime_maxPrimeFac_of_one_lt (Nat.one_lt_maxPrimeFac_iff.mp hPrimeOne)
      exact (Finset.mem_filter.mp hn).2 ⟨n.maxPrimeFac, hPrime,
        (hLogQ.trans hLogCutoff).trans hPrimeLarge.le, Nat.maxPrimeFac_dvd⟩
    have hSmallCard := hSmooth Y t Small hYLog (hSmallA.trans hA) hSmoothSmall hScale
    have hSmallBound : (Small.card : ℝ) ≤ (ε / 2) * t :=
      hSmallCard.trans (mul_le_mul_of_nonneg_right hCoefficientSmall.le (Nat.cast_nonneg t))
    have hSplit : (High.card : ℝ) + Small.card = A.card := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := A)
        (fun n => ∃ p : ℕ, p.Prime ∧ Real.log q ≤ (p : ℝ) ∧ p ∣ n)
    nlinarith only [hHighCard, hSmallBound, hSplit]

end Erdos319Sharp
