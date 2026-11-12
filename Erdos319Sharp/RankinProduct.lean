import Erdos319Sharp.RankinFactors
import Erdos319Sharp.Mertens

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem weighted_factored_hasSum (P : Finset ℕ) (θ : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hθ : θ < 1) :
    HasSum (fun n : Nat.factoredNumbers P => ((n : ℕ) : ℝ) ^ (θ - 1))
      (weightedPrimeProduct P θ) := by
  have hTerm (p j : ℕ) : (((p ^ j : ℕ) : ℝ) ^ (θ - 1)) =
      ((p : ℝ) ^ (θ - 1)) ^ j := by
    rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg p)]
  have hGeom : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖((p ^ j : ℕ) : ℝ) ^ (θ - 1)‖) := by
    intro p hp
    have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hr : (p : ℝ) ^ (θ - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpOne (by linarith)
    have hr0 : 0 ≤ (p : ℝ) ^ (θ - 1) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    apply (summable_geometric_of_lt_one hr0 hr).congr
    intro j
    rw [hTerm, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 j)]
  have hSeries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n : ℝ) ^ (θ - 1)) (by simp)
    (fun {m n} _ => by rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)])
    hGeom P
  have hProduct : (∏ p ∈ P.filter Nat.Prime, ∑' j : ℕ, ((p ^ j : ℕ) : ℝ) ^ (θ - 1)) =
      weightedPrimeProduct P θ := by
    rw [Finset.filter_eq_self.mpr hP]
    apply Finset.prod_congr rfl
    intro p hp
    have hr : (p : ℝ) ^ (θ - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
    have hr0 : 0 ≤ (p : ℝ) ^ (θ - 1) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    calc
      (∑' j : ℕ, ((p ^ j : ℕ) : ℝ) ^ (θ - 1)) = ∑' j : ℕ, ((p : ℝ) ^ (θ - 1)) ^ j :=
        tsum_congr (hTerm p)
      _ = _ := tsum_geometric_of_lt_one hr0 hr
  rw [hProduct] at hSeries
  exact hSeries.2

theorem weighted_factored_sum_le (A P : Finset ℕ) (θ : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hθ : θ < 1)
    (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers P) :
    (∑ n ∈ A, (n : ℝ) ^ (θ - 1)) ≤ weightedPrimeProduct P θ := by
  classical
  let f : A → Nat.factoredNumbers P := fun n => ⟨n, hA n n.property⟩
  let T := A.attach.image f
  have hInjective : ∀ a ∈ A.attach, ∀ b ∈ A.attach, f a = f b → a = b := by
    intro a ha b hb hab
    apply Subtype.ext
    exact congrArg (fun n : Nat.factoredNumbers P => (n : ℕ)) hab
  have hSum : (∑ n ∈ T, ((n : ℕ) : ℝ) ^ (θ - 1)) = ∑ n ∈ A, (n : ℝ) ^ (θ - 1) := by
    rw [Finset.sum_image hInjective]
    exact Finset.sum_attach A (fun n => (n : ℝ) ^ (θ - 1))
  rw [← hSum]
  exact sum_le_hasSum T (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg (n : ℕ)) _)
    (weighted_factored_hasSum P θ hP hθ)

theorem exists_rankin_product_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 4 ≤ Real.log Y →
      weightedPrimeProduct ((Finset.Icc 1 Y).filter Nat.Prime) (1 / Real.log Y) ≤ C * Real.log Y := by
  obtain ⟨U, hU, hUpper⟩ := weak_mertens_third_upper_all
  let K : ℝ := Real.log 4 + 4
  let D : ℝ := (Real.exp 1 / rankinGap) * (1 + K / 4)
  refine ⟨U * Real.exp D, mul_pos hU (Real.exp_pos D), ?_⟩
  intro Y hLog
  let P : Finset ℕ := (Finset.Icc 1 Y).filter Nat.Prime
  let θ : ℝ := 1 / Real.log Y
  have hY : 2 ≤ Y := by
    by_contra h
    have hLe : Y ≤ 1 := by omega
    interval_cases Y <;> norm_num at hLog
  have hYReal : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hLogPos : 0 < Real.log Y := by linarith
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθUpper : θ ≤ 1 / 4 := by
    dsimp [θ]
    exact one_div_le_one_div_of_le (by norm_num) hLog
  have hCancel : θ * Real.log Y = 1 := by dsimp [θ]; field_simp
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hScale : ∀ p ∈ P, θ * Real.log p ≤ 1 := by
    intro p hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hpY : (p : ℝ) ≤ Y := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have h := mul_le_mul_of_nonneg_left (Real.log_le_log hpPos hpY) hθ
    rwa [hCancel] at h
  have hPSet : P = (Finset.range (Y + 1)).filter Nat.Prime := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp0, hpY⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpY, hp⟩
      exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  have hFirst : (∑ p ∈ P, Real.log p / p) ≤ Real.log Y + K := by
    rw [hPSet]
    exact Salt.Maynard.sum_log_div_prime_le (by omega)
  have hK : 0 ≤ K := by
    dsimp [K]
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hWeighted : θ * (∑ p ∈ P, Real.log p / p) ≤ 1 + K / 4 := by
    calc
      _ ≤ θ * (Real.log Y + K) := mul_le_mul_of_nonneg_left hFirst hθ
      _ = 1 + θ * K := by rw [mul_add, hCancel]
      _ ≤ 1 + K / 4 := by nlinarith only [mul_le_mul_of_nonneg_right hθUpper hK]
  have hExp : Real.exp ((Real.exp 1 / rankinGap) * θ * (∑ p ∈ P, Real.log p / p)) ≤
      Real.exp D := by
    apply Real.exp_le_exp.mpr
    dsimp [D]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hWeighted (div_nonneg (Real.exp_nonneg 1) rankinGap_pos.le)
  have hOrdinary : partial_euler_product Y ≤ U * Real.log Y := by
    simpa only [Nat.floor_natCast,
      Real.norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
      Real.norm_of_nonneg hLogPos.le] using hUpper (Y : ℝ) hYReal
  have hComparison := weightedPrimeProduct_le_comparison P θ hP hθ hθUpper hScale
  change weightedPrimeProduct P θ ≤ partial_euler_product Y *
    Real.exp ((Real.exp 1 / rankinGap) * θ * (∑ p ∈ P, Real.log p / p)) at hComparison
  calc
    weightedPrimeProduct P θ ≤ partial_euler_product Y *
        Real.exp ((Real.exp 1 / rankinGap) * θ * (∑ p ∈ P, Real.log p / p)) := hComparison
    _ ≤ (U * Real.log Y) * Real.exp D :=
      mul_le_mul hOrdinary hExp (Real.exp_nonneg _) (mul_nonneg hU.le hLogPos.le)
    _ = (U * Real.exp D) * Real.log Y := by ring

end Erdos319Sharp
