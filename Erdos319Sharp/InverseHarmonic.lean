import Erdos319Sharp.RankinTail
import Erdos319Sharp.DyadicMass
import Erdos319Sharp.HarmonicSmallPrimes

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- The sharp uniform upper coefficient for reciprocal mass of inverse-zero-free
sets, for arbitrary sufficiently large composite or prime moduli. -/
theorem eventually_inverse_zero_free_harmonic_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) → (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (reciprocalSum A : ℝ) ≤
        (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log q) := by
  classical
  obtain ⟨C, hC, hRankin⟩ := exists_rankin_tail_at_harmonic_cutoff
  have hDecay : Tendsto (fun a : ℝ => C * Real.exp (-a)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul C
  obtain ⟨a, haSmall, ha⟩ := ((hDecay.eventually
    (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 4))).and
      (eventually_gt_atTop (0 : ℝ))).exists
  filter_upwards [hRankin, eventually_small_prime_harmonic_bound (ε / 4) (by linarith),
    eventually_bounded_large_factor_mass_small a (ε / 4) ha (by linarith),
    eventually_large_prime_tail_small (ε / 4) (by linarith),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ))]
    with q hRankinQ hSmallQ hBoundedQ hTailQ hLL hL
  intro A hPos hCop hFree
  let Y : ℕ := harmonicPrimeCutoff q
  let Small : Finset ℕ := A.filter (fun n : ℕ => (n.maxPrimeFac : ℝ) ≤ Real.log q)
  let Rest : Finset ℕ := A.filter (fun n : ℕ => ¬ (n.maxPrimeFac : ℝ) ≤ Real.log q)
  let Tail : Finset ℕ := Rest.filter (fun n : ℕ => Y ≤ n.maxPrimeFac)
  let Middle : Finset ℕ := Rest.filter (fun n : ℕ => ¬ Y ≤ n.maxPrimeFac)
  let Bounded : Finset ℕ := Middle.filter (fun n : ℕ => (n : ℝ) ≤ (Y : ℝ) ^ a)
  let SmoothTail : Finset ℕ := Middle.filter (fun n : ℕ => ¬ (n : ℝ) ≤ (Y : ℝ) ^ a)
  have hRestSub : Rest ⊆ A := Finset.filter_subset _ _
  have hTailSub : Tail ⊆ A := (Finset.filter_subset _ _).trans hRestSub
  have hMiddleSub : Middle ⊆ A := (Finset.filter_subset _ _).trans hRestSub
  have hBoundedSub : Bounded ⊆ A := (Finset.filter_subset _ _).trans hMiddleSub
  have hSmoothSub : SmoothTail ⊆ A := (Finset.filter_subset _ _).trans hMiddleSub
  have hSmallMass : (reciprocalSum Small : ℝ) ≤
      (Real.exp Real.eulerMascheroniConstant + ε / 4) * Real.log (Real.log q) := by
    apply hSmallQ Small
    intro n hn
    obtain ⟨hnA, hnSmall⟩ := Finset.mem_filter.mp hn
    exact ⟨hPos n hnA, hnSmall⟩
  have hTailMass : (reciprocalSum Tail : ℝ) ≤ (ε / 4) * Real.log (Real.log q) := by
    have h := hTailQ Tail (fun n hn => hCop n (hTailSub hn))
      (ZeroSumFree.mono hFree hTailSub) (fun n hn => (Finset.mem_filter.mp hn).2)
    have hCompare : ε / 4 ≤ (ε / 4) * Real.log (Real.log q) := by
      nlinarith only [mul_le_mul_of_nonneg_left hLL (show 0 ≤ ε / 4 by linarith)]
    exact h.trans hCompare
  have hBoundedPrime : ∀ n ∈ Bounded, ∃ p : ℕ,
      p.Prime ∧ Real.log q ≤ (p : ℝ) ∧ p ∣ n := by
    intro n hn
    have hnMiddle := (Finset.mem_filter.mp hn).1
    have hnRest := (Finset.mem_filter.mp hnMiddle).1
    have hLarge : Real.log q < (n.maxPrimeFac : ℝ) :=
      lt_of_not_ge (Finset.mem_filter.mp hnRest).2
    have hpOne : 1 < n.maxPrimeFac := by
      have h : (1 : ℝ) < n.maxPrimeFac := by linarith
      exact_mod_cast h
    exact ⟨n.maxPrimeFac, Nat.prime_maxPrimeFac_of_one_lt (Nat.one_lt_maxPrimeFac_iff.mp hpOne),
      hLarge.le, Nat.maxPrimeFac_dvd⟩
  have hBoundedMass : (reciprocalSum Bounded : ℝ) ≤ (ε / 4) * Real.log (Real.log q) :=
    hBoundedQ Bounded (fun n hn => hPos n (hBoundedSub hn))
      (fun n hn => hCop n (hBoundedSub hn)) (ZeroSumFree.mono hFree hBoundedSub)
      hBoundedPrime (fun n hn => (Finset.mem_filter.mp hn).2)
  have hSmoothMass : (reciprocalSum SmoothTail : ℝ) ≤ (ε / 4) * Real.log (Real.log q) := by
    have h := hRankinQ a SmoothTail (by
        intro n hn
        have hnMiddle := (Finset.mem_filter.mp hn).1
        have hnY : ¬ Y ≤ n.maxPrimeFac := (Finset.mem_filter.mp hnMiddle).2
        exact ⟨hPos n (hSmoothSub hn), (Nat.lt_of_not_ge hnY).le⟩)
      (fun n hn => (lt_of_not_ge (Finset.mem_filter.mp hn).2).le)
    exact h.trans (mul_le_mul_of_nonneg_right haSmall.le (by linarith))
  have hSplitOne : reciprocalSum Small + reciprocalSum Rest = reciprocalSum A :=
    Finset.sum_filter_add_sum_filter_not A _ _
  have hSplitTwo : reciprocalSum Tail + reciprocalSum Middle = reciprocalSum Rest :=
    Finset.sum_filter_add_sum_filter_not Rest _ _
  have hSplitThree : reciprocalSum Bounded + reciprocalSum SmoothTail = reciprocalSum Middle :=
    Finset.sum_filter_add_sum_filter_not Middle _ _
  have hSplitQ : reciprocalSum A = reciprocalSum Small + reciprocalSum Tail +
      reciprocalSum Bounded + reciprocalSum SmoothTail := by
    linarith only [hSplitOne, hSplitTwo, hSplitThree]
  have hSplit : (reciprocalSum A : ℝ) = (reciprocalSum Small : ℝ) + (reciprocalSum Tail : ℝ) +
      (reciprocalSum Bounded : ℝ) + (reciprocalSum SmoothTail : ℝ) := by exact_mod_cast hSplitQ
  nlinarith only [hSplit, hSmallMass, hTailMass, hBoundedMass, hSmoothMass]

end Erdos319Sharp
