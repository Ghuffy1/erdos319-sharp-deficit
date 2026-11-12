import Erdos319Sharp.LocalizationSieve
import Erdos319Sharp.Localization

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_divisor_localization_with_log_mass :
    ∀ᶠ N : ℕ in atTop, ∀ c η : ℝ, 0 < c → c ≤ 1 →
      (Real.log N) ^ (-3 / 100 : ℝ) ≤ c →
      (Real.log N) ^ (-1 / 25 : ℝ) ≤ η →
      ∀ A D : Finset ℕ, ∀ h : ℤ,
        A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
        (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
        (∀ q ∈ D, 0 < q ∧ (q : ℝ) ≤ smoothCutoff 6 N ∧
          η ≤ (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ) ∧
          (q : ℝ) * (((A.filter (fun n => q ∣ n)).filter
            (fun n => localizationWidth c N / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ) /
              (c * N) ≤ η / 2) →
        ∃ x : ℤ, |(x : ℝ) - h| < localizationWidth c N / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ x := by
  filter_upwards [eventually_packet_sieve_budget, eventually_sieve_tail_le_packetDensity,
    eventually_common_sieve_count, eventually_common_sieve_support,
    eventually_euler_ratio_power_bound, eventually_common_prime_mass,
    eventually_localizationRoughBound_le,
    tendsto_localizationRoughBound.eventually (eventually_ge_atTop 1),
    tendsto_packetMediumBound.eventually (eventually_ge_atTop 1),
    tendsto_packetCommonBound.eventually (eventually_ge_atTop 1),
    tendsto_localizationPrimeLower.eventually (eventually_ge_atTop 1),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)]
    with N hBudget hTail hCount hSupport hRatio hCommon hYN hY hH hW hZ hL hLL hN
      c η hc hcOne hcLower hηLower A D h hA hMin hMult hD
  have hLPos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hL
  have hη : 0 < η := (Real.rpow_pos_of_pos hLPos _).trans_le hηLower
  have hK : 0 < localizationWidth c N := by
    unfold localizationWidth
    positivity
  let P := primeBand (packetMediumBound N) (localizationRoughBound N)
  let Q := primeBand (localizationPrimeLower N) (packetCommonBound N)
  have hP : ∀ p ∈ P, p.Prime ∧ packetMediumBound N ≤ p ∧ p ≤ localizationRoughBound N := by
    intro p hp
    have hMem := Finset.mem_filter.mp hp
    have hRange := Finset.mem_Icc.mp hMem.1
    exact ⟨hMem.2, Nat.le_of_succ_le hRange.1, hRange.2⟩
  have hQ : ∀ p ∈ Q, p.Prime ∧ localizationPrimeLower N ≤ p ∧ p ≤ packetCommonBound N := by
    intro p hp
    have hMem := Finset.mem_filter.mp hp
    have hRange := Finset.mem_Icc.mp hMem.1
    exact ⟨hMem.2, Nat.le_of_succ_le hRange.1, hRange.2⟩
  have hQN : ∀ p ∈ Q, p.Prime ∧ p ≤ N :=
    fun p hp => ⟨(hQ p hp).1, (hQ p hp).2.2.trans hCommon.2.1⟩
  have hMultNat : ∀ n ∈ A, primePowerMultiplicity N n ≤ ⌊(Real.log (Real.log N)) ^ 2⌋₊ := by
    intro n hn
    exact (Nat.le_floor_iff (sq_nonneg _)).mpr (hMult n hn)
  have hClose : localizationWidth c N ≤ ((localizationPrimeLower N ^ localizationPrimeLower N : ℕ) : ℝ) :=
    (localizationWidth_le c N hc.le hcOne).trans (localizationPrimeLower_power_gt N hL hLL).le
  apply divisor_localization_of_sieve_bounds A D P Q N (localizationRoughBound N)
    (packetMediumBound N) (packetCommonBound N) (localizationPrimeLower N)
    (sieveLevel N) ⌊(Real.log (Real.log N)) ^ 2⌋₊ (sieveLevel N)
    c η (localizationWidth c N) (packetDensity N) h hN hc hη hK hY hYN hH hW hZ
    (packetDensity_pos hLPos) (packet_density_from_lower_bounds hLPos hcLower hηLower hRatio)
    hA hMin hMultNat hP hQ (localizationWidth_size c N hc (by linarith)) hClose
    (hTail Q hQN) hCount hSupport
  · intro q hq
    have hData := hD q hq
    exact ⟨hData.1, hData.2.2.1, hData.2.2.2⟩
  · intro q hq
    exact hBudget c η hc hcLower hηLower q (hD q hq).2.1

theorem eventually_rareDivisorSet_localization_with_log_mass (l : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c τ η : ℝ, ∀ A : Finset ℕ, ∀ h : ℤ,
      0 < c → c ≤ 1 → 0 < τ →
      (Real.log N) ^ (-3 / 100 : ℝ) ≤ c → 1 / (Real.log N) ^ l ≤ τ →
      (Real.log N) ^ (-1 / 25 : ℝ) ≤ η →
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ divisorPrimePowers N A,
        η ≤ (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) →
      ∃ x : ℤ, |(x : ℝ) - h| < localizationWidth c N / 2 ∧
        ∀ q ∈ rareDivisorSet c τ N A h, (q : ℤ) ∣ x := by
  filter_upwards [eventually_divisor_localization_with_log_mass,
    eventually_localization_cost_with_log_mass 1 l 1,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)]
    with N hLocal hCost hL hN c τ η A h hc hcOne hτ hcLower hτLower hηLower hA hMin hSmooth hMult hMass
  have hcNat : 1 / (Real.log N) ^ 1 ≤ c := by
    calc
      _ = (Real.log N) ^ (-1 : ℝ) := by simp [Real.rpow_neg_one]
      _ ≤ (Real.log N) ^ (-3 / 100 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ c := hcLower
  have hηNat : 1 / (Real.log N) ^ 1 ≤ η := by
    calc
      _ = (Real.log N) ^ (-1 : ℝ) := by simp [Real.rpow_neg_one]
      _ ≤ (Real.log N) ^ (-1 / 25 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ η := hηLower
  apply hLocal c η hc hcOne hcLower hηLower A (rareDivisorSet c τ N A h) h hA hMin hMult
  intro q hq
  have hqi := Finset.mem_filter.mp hq
  have hqPP := Finset.mem_filter.mp hqi.1
  have hqAll := Finset.mem_filter.mp hqPP.1
  obtain ⟨n, hn, hqn⟩ := hqPP.2
  have hqS : (q : ℝ) ≤ smoothCutoff 6 N := hSmooth n hn q hqAll.2 hqn
  refine ⟨(Finset.mem_Icc.mp hqAll.1).1, hqS, hMass q hqi.1, ?_⟩
  calc
    _ ≤ (q : ℝ) * localizationRarity c τ N / (c * N) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hqi.2.le (Nat.cast_nonneg q)
    _ ≤ η / 2 := hCost c τ η hc hτ hcNat hτLower hηNat q hqS

end Erdos319Sharp
