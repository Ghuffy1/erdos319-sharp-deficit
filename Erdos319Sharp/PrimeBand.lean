import Erdos319Sharp.PrimeSupply

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def primeInterval (a b : ℕ) : Finset ℕ := b.primesLE \ a.primesLE

theorem mem_primeInterval {a b p : ℕ} :
    p ∈ primeInterval a b ↔ p.Prime ∧ a < p ∧ p ≤ b := by
  simp only [primeInterval, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpb, hp⟩, ha⟩
    exact ⟨hp, lt_of_not_ge (fun hpa => ha ⟨hpa, hp⟩), hpb⟩
  · rintro ⟨hp, hap, hpb⟩
    exact ⟨⟨hpb, hp⟩, fun ha => (not_le_of_gt hap) ha.1⟩

theorem primeInterval_reciprocal_sum (a b : ℕ) (hab : a ≤ b) :
    (∑ p ∈ primeInterval a b, (1 : ℝ) / p) =
      primeReciprocalSum b - primeReciprocalSum a := by
  simpa only [primeInterval, primeReciprocalSum, Nat.primesLE_eq_filter_range] using
    (Finset.sum_sdiff_eq_sub (f := fun p : ℕ => (1 : ℝ) / p)
      (Nat.primesLE_mono hab))

theorem primeInterval_mass_card_bound (a b : ℕ) (ha : 0 < a) :
    (∑ p ∈ primeInterval a b, (1 : ℝ) / p) ≤
      (primeInterval a b).card / (a : ℝ) := by
  calc
    (∑ p ∈ primeInterval a b, (1 : ℝ) / p) ≤
        ∑ _p ∈ primeInterval a b, (1 : ℝ) / a := by
      apply Finset.sum_le_sum
      intro p hp
      have hpa := (mem_primeInterval.mp hp).2.1.le
      exact one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast hpa)
    _ = (primeInterval a b).card / (a : ℝ) := by simp [div_eq_mul_inv]

theorem primeReciprocalPowerBand_limit (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Tendsto (fun n : ℕ => primeReciprocalSum (n ^ l) - primeReciprocalSum (n ^ k))
      atTop (𝓝 (Real.log l - Real.log k)) := by
  apply primeReciprocalBand_limit
    (fun n : ℕ => n ^ k) (fun n : ℕ => n ^ l) (Real.log l - Real.log k)
    (tendsto_pow_atTop hk.ne') (tendsto_pow_atTop hl.ne')
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hnR).ne'
  simp only [Nat.cast_pow, Real.log_pow]
  rw [Real.log_mul (by exact_mod_cast hl.ne') hlog,
    Real.log_mul (by exact_mod_cast hk.ne') hlog]
  ring

/-- The broad prime band has enough room for a correction pool and a
polynomial-sized set of forbidden primes. -/
theorem eventually_primeInterval_card :
    ∀ᶠ n : ℕ in atTop, n ^ 11 + n ^ 10 ≤ (primeInterval (n ^ 12) (n ^ 13)).card := by
  let δ : ℝ := (Real.log 13 - Real.log 12) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    have hlog : Real.log 12 < Real.log 13 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  have hMass := (primeReciprocalPowerBand_limit 12 13 (by norm_num) (by norm_num)).eventually
    (Ioi_mem_nhds (show δ < Real.log 13 - Real.log 12 by
      have h := hδ
      dsimp [δ] at h ⊢
      linarith))
  have hSize : ∀ᶠ n : ℕ in atTop, 2 / δ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 / δ))
  filter_upwards [hMass, hSize, eventually_ge_atTop (1 : ℕ)] with n hMass hSize hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hOrder : n ^ 12 ≤ n ^ 13 := by
    exact Nat.pow_le_pow_right hn (by norm_num)
  rw [← primeInterval_reciprocal_sum _ _ hOrder] at hMass
  have hCard := hMass.trans_le (primeInterval_mass_card_bound (n ^ 12) (n ^ 13)
    (pow_pos (by omega) _))
  have hδn : 2 ≤ δ * n := by
    have := (div_le_iff₀ hδ).mp hSize
    nlinarith
  have hBase : (n : ℝ) ^ 11 + (n : ℝ) ^ 10 ≤ δ * (n : ℝ) ^ 12 := by
    have hPower : (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 11 :=
      pow_le_pow_right₀ hnR (by norm_num)
    have hMul := mul_le_mul_of_nonneg_right hδn (pow_nonneg hn0.le 11)
    calc
      (n : ℝ) ^ 11 + (n : ℝ) ^ 10 ≤ 2 * (n : ℝ) ^ 11 := by linarith
      _ ≤ δ * (n : ℝ) ^ 12 := by nlinarith only [hMul]
  have hCard' : δ * (n : ℝ) ^ 12 < (primeInterval (n ^ 12) (n ^ 13)).card := by
    simpa only [Nat.cast_pow] using (lt_div_iff₀ (by positivity : (0 : ℝ) < (n ^ 12 : ℕ))).mp hCard
  exact_mod_cast (hBase.trans hCard'.le)

theorem eventually_primeInterval_thinning :
    ∀ᶠ n : ℕ in atTop, ∀ F : Finset ℕ, F.card ≤ n ^ 11 →
      ∃ M ⊆ primeInterval (n ^ 12) (n ^ 13), M.card = n ^ 10 ∧ Disjoint M F := by
  filter_upwards [eventually_primeInterval_card] with n hn F hF
  have hRoom : n ^ 10 ≤ (primeInterval (n ^ 12) (n ^ 13) \ F).card := by
    have hDiff := Finset.le_card_sdiff F (primeInterval (n ^ 12) (n ^ 13))
    omega
  obtain ⟨M, hM, hCard⟩ := Finset.exists_subset_card_eq hRoom
  refine ⟨M, hM.trans Finset.sdiff_subset, hCard, ?_⟩
  exact Finset.disjoint_left.mpr (fun p hp hpF => (Finset.mem_sdiff.mp (hM hp)).2 hpF)

end Erdos319Sharp
