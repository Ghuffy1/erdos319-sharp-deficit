import Erdos319Sharp.DivisorReciprocals

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def lcmEulerCorrection (s : ℕ) : ℝ :=
  ∏ p ∈ s.primesLE, (1 - 1 / (p : ℝ) ^ (p.log s + 1))

theorem product_one_sub_bounds (S : Finset ℕ) (f : ℕ → ℝ)
    (hNonneg : ∀ n ∈ S, 0 ≤ f n) (hOne : ∀ n ∈ S, f n ≤ 1) :
    1 - (∑ n ∈ S, f n) ≤ (∏ n ∈ S, (1 - f n)) ∧
      (∏ n ∈ S, (1 - f n)) ≤ 1 := by
  classical
  constructor
  · revert hNonneg hOne
    induction S using Finset.induction_on with
    | empty => intro hNonneg hOne; simp
    | @insert n S hn ih =>
        intro hNonneg hOne
        have hNonnegS : ∀ m ∈ S, 0 ≤ f m := fun m hm => hNonneg m (Finset.mem_insert_of_mem hm)
        have hOneS : ∀ m ∈ S, f m ≤ 1 := fun m hm => hOne m (Finset.mem_insert_of_mem hm)
        have hUpperS : (∏ m ∈ S, (1 - f m)) ≤ 1 := Finset.prod_le_one₀
          (fun m hm => sub_nonneg.mpr (hOneS m hm)) (fun m hm => by linarith [hNonnegS m hm])
        have hLowerS := ih hNonnegS hOneS
        have hProduct := mul_le_mul_of_nonneg_left hUpperS (hNonneg n (Finset.mem_insert_self _ _))
        rw [Finset.sum_insert hn, Finset.prod_insert hn]
        nlinarith
  · exact Finset.prod_le_one₀ (fun n hn => sub_nonneg.mpr (hOne n hn))
      (fun n hn => by linarith [hNonneg n hn])

theorem lcmEulerCorrection_bounds (s : ℕ) (hs : 0 < s) :
    1 - (s.primesLE.card : ℝ) / s ≤ lcmEulerCorrection s ∧ lcmEulerCorrection s ≤ 1 := by
  have hNonneg : ∀ p ∈ s.primesLE, 0 ≤ 1 / (p : ℝ) ^ (p.log s + 1) := by
    intro p hp
    positivity
  have hOne : ∀ p ∈ s.primesLE, 1 / (p : ℝ) ^ (p.log s + 1) ≤ 1 := by
    intro p hp
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hpOne)
  obtain ⟨hLower, hUpper⟩ := product_one_sub_bounds s.primesLE
    (fun p => 1 / (p : ℝ) ^ (p.log s + 1)) hNonneg hOne
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have hSum : (∑ p ∈ s.primesLE, 1 / (p : ℝ) ^ (p.log s + 1)) ≤
      (s.primesLE.card : ℝ) / s := by
    calc
      _ ≤ ∑ _p ∈ s.primesLE, (1 : ℝ) / s := by
        apply Finset.sum_le_sum
        intro p hp
        have hPower : (s : ℝ) ≤ (p : ℝ) ^ (p.log s + 1) := by
          exact_mod_cast (Nat.lt_pow_succ_log_self (Nat.prime_of_mem_primesLE hp).one_lt s).le
        exact one_div_le_one_div_of_le hsReal hPower
      _ = _ := by simp [div_eq_mul_inv]
  exact ⟨(by change _ ≤ _ at hLower; dsimp [lcmEulerCorrection]; linarith), hUpper⟩

theorem tendsto_lcmEulerCorrection :
    Tendsto lcmEulerCorrection atTop (𝓝 1) := by
  obtain ⟨C, hC, hCount⟩ := prime_counting_le_const_mul_div_log
  have hLog : Tendsto (fun s : ℕ => Real.log (s : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hError : Tendsto (fun s : ℕ => C / Real.log s) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hLog) :
        Tendsto (fun s : ℕ => C * (Real.log s)⁻¹) atTop (𝓝 (C * 0)))
  have hBounds : ∀ᶠ s : ℕ in atTop,
      0 ≤ 1 - lcmEulerCorrection s ∧ 1 - lcmEulerCorrection s ≤ C / Real.log s := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with s hs
    have hsPos : 0 < s := by omega
    have hsReal : (0 : ℝ) < s := by exact_mod_cast hsPos
    have hLogPos : 0 < Real.log s := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
    have hEstimate := hCount (s : ℝ)
    simp only [Nat.floor_natCast, Real.norm_of_nonneg (div_nonneg hsReal.le hLogPos.le)] at hEstimate
    rw [← Nat.primesLE_card_eq_primeCounting] at hEstimate
    have hCard : (s.primesLE.card : ℝ) / s ≤ C / Real.log s := by
      apply (div_le_iff₀ hsReal).mpr
      calc
        (s.primesLE.card : ℝ) ≤ C * ((s : ℝ) / Real.log s) := hEstimate
        _ = C / Real.log s * s := by ring
    obtain ⟨hLower, hUpper⟩ := lcmEulerCorrection_bounds s hsPos
    constructor <;> linarith
  have hGap : Tendsto (fun s : ℕ => 1 - lcmEulerCorrection s) atTop (𝓝 0) :=
    squeeze_zero' (hBounds.mono (fun _ h => h.1)) (hBounds.mono (fun _ h => h.2)) hError
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_zero, sub_sub_cancel] using hOne.sub hGap

theorem tendsto_lcm_divisorReciprocalMass_div_log :
    Tendsto (fun s : ℕ => divisorReciprocalMass (Nat.lcmUpto s) / Real.log s)
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have h := tendsto_lcmEulerCorrection.mul tendsto_inversePrimeProduct_div_log
  have hEqual : (fun s : ℕ => lcmEulerCorrection s * (inversePrimeProduct s / Real.log s)) =
      (fun s : ℕ => divisorReciprocalMass (Nat.lcmUpto s) / Real.log s) := by
    funext s
    rw [lcm_divisorReciprocalMass_product]
    unfold lcmEulerCorrection
    ring
  simpa only [hEqual, one_mul] using h

end Erdos319Sharp
