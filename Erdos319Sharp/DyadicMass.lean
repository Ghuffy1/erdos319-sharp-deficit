import Erdos319Sharp.DyadicObstruction
import Erdos319Sharp.PrimeTailCutoff

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem reciprocal_mass_of_dyadic_density (A : Finset ℕ) (δ T : ℝ)
    (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hPos : ∀ n ∈ A, 0 < n)
    (hLog : ∀ n ∈ A, Real.log n ≤ T)
    (hDensity : ∀ (N : ℕ) (B : Finset ℕ), B ⊆ A → B ⊆ Finset.Ioc (N / 2) N →
      (B.card : ℝ) ≤ δ * N) :
    (reciprocalSum A : ℝ) ≤ 2 * δ * (T / Real.log 2 + 1) := by
  classical
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBins : ∀ n : ℕ, ∃ j : ℕ, n ∈ A → 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) := by
    intro n
    by_cases hn : n ∈ A
    · have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hPos n hn
      obtain ⟨j, hjLo, hjHi⟩ := exists_nat_pow_near hnOne (by norm_num : (1 : ℝ) < 2)
      exact ⟨j, fun _ => ⟨by exact_mod_cast hjLo, by exact_mod_cast hjHi⟩⟩
    · exact ⟨0, fun h => False.elim (hn h)⟩
  choose bin hBin using hBins
  let J := A.image bin
  have hEach : ∀ j ∈ J, (∑ n ∈ A.filter (fun n => bin n = j), (n : ℝ)⁻¹) ≤ 2 * δ := by
    intro j hj
    let N := 2 ^ (j + 1) - 1
    let B := A.filter (fun n => bin n = j)
    have hPower : 0 < 2 ^ j := by positivity
    have hBRange : B ⊆ Finset.Ioc (N / 2) N := by
      intro n hn
      obtain ⟨hnA, hnj⟩ := Finset.mem_filter.mp hn
      have hRange := hBin n hnA
      rw [hnj] at hRange
      have hPow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
      apply Finset.mem_Ioc.mpr
      dsimp [N]
      constructor <;> omega
    have hCard := hDensity N B (Finset.filter_subset _ _) hBRange
    have hMin : ∀ n ∈ B, ((2 ^ j : ℕ) : ℝ) ≤ n := by
      intro n hn
      obtain ⟨hnA, hnj⟩ := Finset.mem_filter.mp hn
      have hRange := hBin n hnA
      rw [hnj] at hRange
      exact_mod_cast hRange.1
    have hPowerReal : (0 : ℝ) < (2 ^ j : ℕ) := by exact_mod_cast hPower
    have hMass := reciprocalSum_le_card_div_min B ((2 ^ j : ℕ) : ℝ) hPowerReal hMin
    rw [reciprocalSum_real] at hMass
    simp only [one_div] at hMass
    have hN : (N : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
      have hNat : N ≤ 2 * 2 ^ j := by dsimp [N]; rw [pow_succ]; omega
      exact_mod_cast hNat
    calc
      (∑ n ∈ B, (n : ℝ)⁻¹) ≤ B.card / ((2 ^ j : ℕ) : ℝ) := hMass
      _ ≤ (δ * N) / ((2 ^ j : ℕ) : ℝ) := div_le_div_of_nonneg_right hCard hPowerReal.le
      _ ≤ (δ * (2 * ((2 ^ j : ℕ) : ℝ))) / ((2 ^ j : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN hδ) hPowerReal.le
      _ = 2 * δ := by field_simp
  have hRatio : 0 ≤ T / Real.log 2 := div_nonneg hT hLogTwo.le
  have hJSub : J ⊆ Finset.range (⌊T / Real.log 2⌋₊ + 1) := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
    have hLower : ((2 ^ bin n : ℕ) : ℝ) ≤ n := by exact_mod_cast (hBin n hn).1
    have h := (Real.log_le_log (by positivity : (0 : ℝ) < (2 ^ bin n : ℕ)) hLower).trans (hLog n hn)
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
    have hFloor : bin n ≤ ⌊T / Real.log 2⌋₊ :=
      (Nat.le_floor_iff hRatio).mpr ((le_div_iff₀ hLogTwo).mpr h)
    exact Finset.mem_range.mpr (by omega)
  have hJCard : (J.card : ℝ) ≤ T / Real.log 2 + 1 := by
    have hNat : J.card ≤ ⌊T / Real.log 2⌋₊ + 1 := by simpa using Finset.card_le_card hJSub
    have hReal : (J.card : ℝ) ≤ (⌊T / Real.log 2⌋₊ : ℝ) + 1 := by exact_mod_cast hNat
    have hFloor := Nat.floor_le hRatio
    linarith
  have hSplit : (∑ n ∈ A, (n : ℝ)⁻¹) =
      ∑ j ∈ J, ∑ n ∈ A.filter (fun n => bin n = j), (n : ℝ)⁻¹ :=
    (Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩) _).symm
  rw [reciprocalSum_eq_baseline, reciprocalSum_real]
  simp only [one_div]
  calc
    _ = ∑ j ∈ J, ∑ n ∈ A.filter (fun n => bin n = j), (n : ℝ)⁻¹ := hSplit
    _ ≤ ∑ _j ∈ J, 2 * δ := Finset.sum_le_sum hEach
    _ = (J.card : ℝ) * (2 * δ) := by simp
    _ ≤ (T / Real.log 2 + 1) * (2 * δ) :=
      mul_le_mul_of_nonneg_right hJCard (by positivity)
    _ = _ := by ring

theorem eventually_large_factor_dyadic_density (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) → (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, ∃ p : ℕ, p.Prime ∧ Real.log q ≤ (p : ℝ) ∧ p ∣ n) →
      ∀ (N : ℕ) (B : Finset ℕ), B ⊆ A → B ⊆ Finset.Ioc (N / 2) N →
        (B.card : ℝ) ≤ δ * N := by
  filter_upwards [eventually_sparse_large_prime_dyadic δ hδ] with q hSparse
  intro A hPos hCop hFree hPrime N B hBA hBRange
  by_cases hBne : B.Nonempty
  · obtain ⟨n, hn⟩ := hBne
    obtain ⟨p, hp, hLog, hpn⟩ := hPrime n (hBA hn)
    have hScale : Real.log q ≤ (N : ℝ) := by
      have hpN : p ≤ N := (Nat.le_of_dvd (hPos n (hBA hn)) hpn).trans
        (Finset.mem_Ioc.mp (hBRange hn)).2
      exact hLog.trans (by exact_mod_cast hpN)
    exact (hSparse N B hScale hBRange (fun n hn => hCop n (hBA hn))
      (ZeroSumFree.mono hFree hBA) (fun n hn => hPrime n (hBA hn))).le
  · have hEmpty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBne
    simp only [hEmpty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hδ.le (Nat.cast_nonneg N)

theorem eventually_bounded_large_factor_mass_small (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) → (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, ∃ p : ℕ, p.Prime ∧ Real.log q ≤ (p : ℝ) ∧ p ∣ n) →
      (∀ n ∈ A, (n : ℝ) ≤ (harmonicPrimeCutoff q : ℝ) ^ a) →
      (reciprocalSum A : ℝ) ≤ ε * Real.log (Real.log q) := by
  let K : ℝ := 13 * a / Real.log 2 + 1
  let δ : ℝ := ε / (2 * K)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [eventually_large_factor_dyadic_density δ hδ,
    eventually_log_harmonicPrimeCutoff_bound,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ))]
    with q hDensity hYLog hLL hL
  intro A hPos hCop hFree hPrime hSize
  have hLPos : 0 < Real.log q := by linarith
  have hYPos : (0 : ℝ) < harmonicPrimeCutoff q := by
    exact_mod_cast Nat.ceil_pos.mpr (pow_pos hLPos 12)
  have hYLogNonneg : 0 ≤ Real.log (harmonicPrimeCutoff q : ℝ) := by
    have hYOne : (1 : ℝ) ≤ harmonicPrimeCutoff q := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hYPos.ne'))
    exact Real.log_nonneg hYOne
  have hLogs : ∀ n ∈ A, Real.log n ≤ a * Real.log (harmonicPrimeCutoff q : ℝ) := by
    intro n hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hPos n hn
    have h := Real.log_le_log hnPos (hSize n hn)
    rwa [Real.log_rpow hYPos] at h
  have hMass := reciprocal_mass_of_dyadic_density A δ
    (a * Real.log (harmonicPrimeCutoff q : ℝ)) hδ.le (mul_nonneg ha.le hYLogNonneg)
    hPos hLogs (hDensity A hPos hCop hFree hPrime)
  have hCountBound : a * Real.log (harmonicPrimeCutoff q : ℝ) / Real.log 2 + 1 ≤
      K * Real.log (Real.log q) := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hYLog ha.le) hLogTwo.le
    calc
      _ ≤ a * (13 * Real.log (Real.log q)) / Real.log 2 + 1 := by linarith only [h]
      _ = (13 * a / Real.log 2) * Real.log (Real.log q) + 1 := by ring
      _ ≤ (13 * a / Real.log 2) * Real.log (Real.log q) + Real.log (Real.log q) := by
        linarith only [hLL]
      _ = _ := by dsimp [K]; ring
  calc
    (reciprocalSum A : ℝ) ≤ 2 * δ *
        (a * Real.log (harmonicPrimeCutoff q : ℝ) / Real.log 2 + 1) := hMass
    _ ≤ 2 * δ * (K * Real.log (Real.log q)) :=
      mul_le_mul_of_nonneg_left hCountBound (by positivity)
    _ = ε * Real.log (Real.log q) := by dsimp [δ]; field_simp

end Erdos319Sharp
