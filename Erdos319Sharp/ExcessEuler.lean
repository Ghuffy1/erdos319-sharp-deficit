import Erdos319Sharp.ExcessWeights
import Erdos319Sharp.RankinProduct

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def primeExcessMass (D p : ℕ) : ℝ :=
  (firstMissingPower D p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)

def excessEulerProduct (D : ℕ) (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + primeExcessMass D p)

theorem primeExcessMass_nonneg (D p : ℕ) (hp : p.Prime) : 0 ≤ primeExcessMass D p := by
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (sub_nonneg.mpr (inv_le_one_of_one_le₀ hpOne.le))

theorem hasSum_prime_excess_tail (D p : ℕ) (hD : D ≠ 0) (hp : p.Prime) :
    HasSum (fun k : ℕ => excessWeight D (p ^ (k + 1))) (primeExcessMass D p) := by
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hSum := (hasSum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
    (inv_lt_one_of_one_lt₀ hpOne)).mul_left (firstMissingPower D p : ℝ)⁻¹
  simpa only [primeExcessMass, div_eq_mul_inv, excessWeight_prime_pow_succ D p _ hD hp] using hSum

theorem hasSum_prime_excess (D p : ℕ) (hD : D ≠ 0) (hp : p.Prime) :
    HasSum (fun k : ℕ => excessWeight D (p ^ k)) (1 + primeExcessMass D p) := by
  have h := (hasSum_nat_add_iff (f := fun k : ℕ => excessWeight D (p ^ k)) 1).mp
    (hasSum_prime_excess_tail D p hD hp)
  simpa only [Finset.sum_range_one, pow_zero, excessWeight_one D hD, add_comm] using h

theorem primeExcessMass_le_two (D p : ℕ) (hp : p.Prime) :
    primeExcessMass D p ≤ 2 * (firstMissingPower D p : ℝ)⁻¹ := by
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hInv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hpTwo
  have hDen : 0 < 1 - (p : ℝ)⁻¹ := by linarith
  unfold primeExcessMass
  apply (div_le_iff₀ hDen).mpr
  have hNonneg : 0 ≤ (firstMissingPower D p : ℝ)⁻¹ := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hInv hNonneg]

theorem primeExcessMass_le_cutoff (D p Y : ℕ) (hY : 2 ≤ Y) (hYp : Y ≤ p) :
    primeExcessMass D p ≤ (1 - (Y : ℝ)⁻¹)⁻¹ * (firstMissingPower D p : ℝ)⁻¹ := by
  have hYOne : (1 : ℝ) < Y := by exact_mod_cast (by omega : 1 < Y)
  have hYPos : (0 : ℝ) < Y := by linarith
  have hYpReal : (Y : ℝ) ≤ p := by exact_mod_cast hYp
  have hGap : 0 < 1 - (Y : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hYOne)
  have hCompare : 1 - (Y : ℝ)⁻¹ ≤ 1 - (p : ℝ)⁻¹ := by
    exact sub_le_sub_left (inv_anti₀ hYPos hYpReal) 1
  have hInv := inv_anti₀ hGap hCompare
  unfold primeExcessMass
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right hInv (by positivity)

theorem excess_factored_hasSum (D : ℕ) (P : Finset ℕ) (hD : D ≠ 0)
    (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P => excessWeight D n) (excessEulerProduct D P) := by
  have hNorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖excessWeight D (p ^ k)‖) := by
    intro p hp
    exact (hasSum_prime_excess D p hD hp).summable.congr
      (fun k => (Real.norm_of_nonneg (excessWeight_nonneg D (p ^ k))).symm)
  have hSeries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (excessWeight_one D hD) (fun {m n} h => excessWeight_mul D m n hD h) hNorm P
  have hProduct : (∏ p ∈ P.filter Nat.Prime, ∑' k : ℕ, excessWeight D (p ^ k)) =
      excessEulerProduct D P := by
    rw [Finset.filter_eq_self.mpr hP]
    apply Finset.prod_congr rfl
    intro p hp
    exact (hasSum_prime_excess D p hD (hP p hp)).tsum_eq
  rw [hProduct] at hSeries
  exact hSeries.2

theorem factored_finite_sum_le {f : ℕ → ℝ} {c : ℝ} (A P : Finset ℕ)
    (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers P) (hNonneg : ∀ n, 0 ≤ f n)
    (hSeries : HasSum (fun n : Nat.factoredNumbers P => f n) c) :
    (∑ n ∈ A, f n) ≤ c := by
  classical
  let inclusion : A → Nat.factoredNumbers P := fun n => ⟨n, hA n n.property⟩
  let T := A.attach.image inclusion
  have hInjective : ∀ a ∈ A.attach, ∀ b ∈ A.attach, inclusion a = inclusion b → a = b := by
    intro a ha b hb hab
    apply Subtype.ext
    exact congrArg (fun n : Nat.factoredNumbers P => (n : ℕ)) hab
  have hSum : (∑ n ∈ T, f n) = ∑ n ∈ A, f n := by
    rw [Finset.sum_image hInjective]
    exact Finset.sum_attach A f
  rw [← hSum]
  exact sum_le_hasSum T (fun n _ => hNonneg n) hSeries

theorem excess_factored_sum_le (D : ℕ) (A P : Finset ℕ) (hD : D ≠ 0)
    (hP : ∀ p ∈ P, p.Prime) (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers P) :
    (∑ n ∈ A, excessWeight D n) ≤ excessEulerProduct D P :=
  factored_finite_sum_le A P hA (excessWeight_nonneg D) (excess_factored_hasSum D P hD hP)

theorem excessEulerProduct_le_exp (D : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    excessEulerProduct D P ≤ Real.exp (2 * ∑ p ∈ P, (firstMissingPower D p : ℝ)⁻¹) := by
  have hMass : (∑ p ∈ P, primeExcessMass D p) ≤ 2 * ∑ p ∈ P, (firstMissingPower D p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p hp => primeExcessMass_le_two D p (hP p hp))
  calc
    excessEulerProduct D P ≤ ∏ p ∈ P, Real.exp (primeExcessMass D p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        linarith [primeExcessMass_nonneg D p (hP p hp)]
      · intro p hp
        linarith [Real.add_one_le_exp (primeExcessMass D p)]
    _ = Real.exp (∑ p ∈ P, primeExcessMass D p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (2 * ∑ p ∈ P, (firstMissingPower D p : ℝ)⁻¹) := Real.exp_le_exp.mpr hMass

end Erdos319Sharp
