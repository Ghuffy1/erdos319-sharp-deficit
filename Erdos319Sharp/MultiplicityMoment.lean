import Erdos319Sharp.MultiplicityCount
import Erdos319Sharp.PrimeSupply

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def omegaWeight (n : ℕ) : ℝ := (3 / 2 : ℝ) ^ ArithmeticFunction.cardFactors n / n

theorem omegaWeight_mul (m n : ℕ) : omegaWeight (m * n) = omegaWeight m * omegaWeight n := by
  by_cases hm : m = 0
  · simp [hm, omegaWeight]
  by_cases hn : n = 0
  · simp [hn, omegaWeight]
  simp only [omegaWeight, ArithmeticFunction.cardFactors_mul hm hn, Nat.cast_mul, pow_add]
  ring

theorem omegaWeight_prime_power (p j : ℕ) (hp : p.Prime) :
    omegaWeight (p ^ j) = ((3 / 2 : ℝ) / p) ^ j := by
  simp only [omegaWeight, ArithmeticFunction.cardFactors_apply_prime_pow hp, Nat.cast_pow, div_pow]

theorem omegaWeight_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P => omegaWeight n)
      (∏ p ∈ P, (1 - (3 / 2 : ℝ) / p)⁻¹) := by
  have hGeom : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖omegaWeight (p ^ j)‖) := by
    intro p hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hr : (3 / 2 : ℝ) / p < 1 := (div_lt_one hpPos).mpr (by linarith)
    have hr0 : 0 ≤ (3 / 2 : ℝ) / p := by positivity
    apply (summable_geometric_of_lt_one hr0 hr).congr
    intro j
    rw [omegaWeight_prime_power p j hp, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 j)]
  have hSeries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := omegaWeight) (by norm_num [omegaWeight])
    (fun {m n} _ => omegaWeight_mul m n) hGeom P
  have hProduct : (∏ p ∈ P.filter Nat.Prime, ∑' j : ℕ, omegaWeight (p ^ j)) =
      ∏ p ∈ P, (1 - (3 / 2 : ℝ) / p)⁻¹ := by
    rw [Finset.filter_eq_self.mpr hP]
    apply Finset.prod_congr rfl
    intro p hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    simp_rw [omegaWeight_prime_power p _ (hP p hp)]
    exact tsum_geometric_of_lt_one (by positivity) ((div_lt_one hpPos).mpr (by linarith))
  rw [hProduct] at hSeries
  exact hSeries.2

theorem omegaWeight_sum_le (A P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers P) :
    (∑ n ∈ A, omegaWeight n) ≤ ∏ p ∈ P, (1 - (3 / 2 : ℝ) / p)⁻¹ := by
  classical
  let f : A → Nat.factoredNumbers P := fun n => ⟨n, hA n n.property⟩
  let T := A.attach.image f
  have hInjective : ∀ a ∈ A.attach, ∀ b ∈ A.attach, f a = f b → a = b := by
    intro a ha b hb hab
    apply Subtype.ext
    exact congrArg (fun n : Nat.factoredNumbers P => (n : ℕ)) hab
  have hSum : (∑ n ∈ T, omegaWeight n) = ∑ n ∈ A, omegaWeight n := by
    rw [Finset.sum_image hInjective]
    exact Finset.sum_attach A omegaWeight
  rw [← hSum]
  exact sum_le_hasSum T (fun n _ => by unfold omegaWeight; positivity) (omegaWeight_hasSum P hP)

theorem omega_euler_factor_bound (x : ℝ) (hx : 2 ≤ x) :
    (1 - (3 / 2 : ℝ) / x)⁻¹ ≤ Real.exp (6 / x) := by
  have hxPos : 0 < x := by linarith
  have hRatio : (3 / 2 : ℝ) / x ≤ 3 / 4 :=
    (div_le_iff₀ hxPos).mpr (by linarith)
  have hDen : 0 < 1 - (3 / 2 : ℝ) / x := by linarith
  have hFraction : ((3 / 2 : ℝ) / x) / (1 - (3 / 2 : ℝ) / x) ≤ 6 / x := by
    calc
      _ ≤ ((3 / 2 : ℝ) / x) / (1 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ = 6 / x := by ring
  calc
    (1 - (3 / 2 : ℝ) / x)⁻¹ = 1 + ((3 / 2 : ℝ) / x) / (1 - (3 / 2 : ℝ) / x) := by
      calc
        _ = ((1 - (3 / 2 : ℝ) / x) + (3 / 2 : ℝ) / x) * (1 - (3 / 2 : ℝ) / x)⁻¹ := by ring
        _ = (1 - (3 / 2 : ℝ) / x) * (1 - (3 / 2 : ℝ) / x)⁻¹ +
            ((3 / 2 : ℝ) / x) * (1 - (3 / 2 : ℝ) / x)⁻¹ := add_mul _ _ _
        _ = _ := by
          rw [mul_inv_cancel₀ hDen.ne']
          simp only [div_eq_mul_inv]
    _ ≤ Real.exp (((3 / 2 : ℝ) / x) / (1 - (3 / 2 : ℝ) / x)) := by
      linarith only [Real.add_one_le_exp (((3 / 2 : ℝ) / x) / (1 - (3 / 2 : ℝ) / x))]
    _ ≤ Real.exp (6 / x) := Real.exp_le_exp.mpr hFraction

theorem omega_euler_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - (3 / 2 : ℝ) / p)⁻¹) ≤ Real.exp (6 * ∑ p ∈ P, (1 : ℝ) / p) := by
  have hProduct : (∏ p ∈ P, (1 - (3 / 2 : ℝ) / p)⁻¹) ≤ ∏ p ∈ P, Real.exp (6 / p) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hpPos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
      apply inv_nonneg.mpr
      have h := (div_le_iff₀ hpPos).mpr (show (3 / 2 : ℝ) ≤ (3 / 4) * p by linarith)
      linarith
    · intro p hp
      exact omega_euler_factor_bound p (by exact_mod_cast (hP p hp).two_le)
  rw [← Real.exp_sum] at hProduct
  convert hProduct using 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem eventually_multiplicity_moment_bound :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (∑ n ∈ A, (3 / 2 : ℝ) ^ primePowerMultiplicity N n) ≤ (N : ℝ) * (Real.log N) ^ 12 := by
  obtain ⟨M, hM⟩ := exists_primeReciprocalSum_centered_limit
  filter_upwards [hM.eventually (Iio_mem_nhds (lt_add_one M)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (M + 1)),
    eventually_gt_atTop (1 : ℕ)] with N hRecip hLL hN
  intro A hA
  let P := (Finset.range (N + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hFactored : ∀ n ∈ A, n ∈ Nat.factoredNumbers P := by
    intro n hn
    have hnI := Finset.mem_Icc.mp (hA hn)
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have h := (Nat.le_of_dvd hnI.1 hpn).trans hnI.2
      omega), hp⟩
  have hPrimeSum : (∑ p ∈ P, (1 : ℝ) / p) ≤ 2 * Real.log (Real.log N) := by
    change primeReciprocalSum N ≤ _
    linarith
  have hWeighted := (omegaWeight_sum_le A P hP hFactored).trans (omega_euler_product_bound P hP)
  have hLog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hWeightedBound : (∑ n ∈ A, omegaWeight n) ≤ (Real.log N) ^ 12 := by
    have hExp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hPrimeSum (by norm_num : (0 : ℝ) ≤ 6))
    have hIdentity : Real.exp (6 * (2 * Real.log (Real.log N))) = (Real.log N) ^ 12 := by
      rw [show 6 * (2 * Real.log (Real.log N)) = (12 : ℕ) * Real.log (Real.log N) by ring,
        Real.exp_nat_mul, Real.exp_log hLog]
    exact hWeighted.trans (hExp.trans_eq hIdentity)
  calc
    (∑ n ∈ A, (3 / 2 : ℝ) ^ primePowerMultiplicity N n) =
        ∑ n ∈ A, (n : ℝ) * omegaWeight n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnI := Finset.mem_Icc.mp (hA hn)
      rw [primePowerMultiplicity_eq_cardFactors N n hnI.1 hnI.2]
      unfold omegaWeight
      have hnPos : (0 : ℝ) < n := by exact_mod_cast hnI.1
      field_simp
    _ ≤ ∑ n ∈ A, (N : ℝ) * omegaWeight n := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp (hA hn)).2)
      unfold omegaWeight
      positivity
    _ = (N : ℝ) * ∑ n ∈ A, omegaWeight n := (Finset.mul_sum _ _ _).symm
    _ ≤ (N : ℝ) * (Real.log N) ^ 12 := mul_le_mul_of_nonneg_left hWeightedBound (Nat.cast_nonneg N)

theorem eventually_high_multiplicity_card_bound (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      ((A.filter (fun n => (Real.log (Real.log N)) ^ 2 < (primePowerMultiplicity N n : ℝ))).card : ℝ) ≤
        (N : ℝ) * (Real.log N) ^ (-(m : ℝ)) := by
  have hLogBase : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_multiplicity_moment_bound,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop ((12 + (m : ℝ)) / Real.log (3 / 2 : ℝ))),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with N hMoment hLarge hLL hN
  intro A hA
  let B := A.filter (fun n => (Real.log (Real.log N)) ^ 2 < (primePowerMultiplicity N n : ℝ))
  have hLog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hPower : 0 < (3 / 2 : ℝ) ^ ((Real.log (Real.log N)) ^ 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hCount : (B.card : ℝ) * (3 / 2 : ℝ) ^ ((Real.log (Real.log N)) ^ 2) ≤
      (N : ℝ) * (Real.log N) ^ 12 := by
    calc
      _ = ∑ _n ∈ B, (3 / 2 : ℝ) ^ ((Real.log (Real.log N)) ^ 2) := by simp
      _ ≤ ∑ n ∈ B, (3 / 2 : ℝ) ^ primePowerMultiplicity N n := by
        apply Finset.sum_le_sum
        intro n hn
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3 / 2)
          (Finset.mem_filter.mp hn).2.le
        simpa only [Real.rpow_natCast] using h
      _ ≤ ∑ n ∈ A, (3 / 2 : ℝ) ^ primePowerMultiplicity N n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ ≤ _ := hMoment A hA
  have hExponent : (12 + (m : ℝ)) * Real.log (Real.log N) ≤
      (Real.log (Real.log N)) ^ 2 * Real.log (3 / 2 : ℝ) := by
    have h := (div_le_iff₀ hLogBase).mp hLarge
    nlinarith only [mul_le_mul_of_nonneg_right h hLL]
  have hRatio : (Real.log N) ^ 12 / (3 / 2 : ℝ) ^ ((Real.log (Real.log N)) ^ 2) ≤
      (Real.log N) ^ (-(m : ℝ)) := by
    have h := Real.exp_le_exp.mpr (show 12 * Real.log (Real.log N) -
        (Real.log (Real.log N)) ^ 2 * Real.log (3 / 2 : ℝ) ≤
        (-(m : ℝ)) * Real.log (Real.log N) by nlinarith only [hExponent])
    rw [Real.exp_sub] at h
    rw [Real.rpow_def_of_pos hLog, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have hTwelve : Real.exp (12 * Real.log (Real.log N)) = (Real.log N) ^ 12 := by
      rw [show (12 : ℝ) = (12 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hLog]
    rw [hTwelve] at h
    simpa only [mul_comm] using h
  exact ((le_div_iff₀ hPower).mpr hCount).trans (by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hRatio (Nat.cast_nonneg N))

end Erdos319Sharp
