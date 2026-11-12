import Erdos319Sharp.TailDivisibility
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def divisorIncidence (Q : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ q ∈ Q, if q ∣ n then 1 else 0

theorem divisorIncidence_nonneg (Q : Finset ℕ) (n : ℕ) : 0 ≤ divisorIncidence Q n := by
  apply Finset.sum_nonneg
  intro q hq
  split_ifs <;> norm_num

theorem sum_divisorIncidence (A Q : Finset ℕ) :
    (∑ n ∈ A, divisorIncidence Q n) =
      ∑ q ∈ Q, ((A.filter (fun n => q ∣ n)).card : ℝ) := by
  unfold divisorIncidence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have h := Finset.sum_filter (s := A) (p := fun n => q ∣ n) (f := fun _ => (1 : ℝ))
  simpa using h.symm

theorem divisorIncidence_sq (Q : Finset ℕ) (n : ℕ) :
    (divisorIncidence Q n) ^ 2 =
      ∑ q ∈ Q, ∑ r ∈ Q, if q ∣ n ∧ r ∣ n then (1 : ℝ) else 0 := by
  unfold divisorIncidence
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hq : q ∣ n <;> by_cases hr : r ∣ n <;> simp [hq, hr]

theorem sum_divisorIncidence_sq (A Q : Finset ℕ) :
    (∑ n ∈ A, (divisorIncidence Q n) ^ 2) =
      ∑ q ∈ Q, ∑ r ∈ Q, ((A.filter (fun n => q ∣ n ∧ r ∣ n)).card : ℝ) := by
  simp_rw [divisorIncidence_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have h := Finset.sum_filter (s := A) (p := fun n => q ∣ n ∧ r ∣ n) (f := fun _ => (1 : ℝ))
  simpa using h.symm

theorem coprime_joint_multiples_card_le (N q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hCop : q.Coprime r) :
    (((Finset.Icc 1 N).filter (fun n => q ∣ n ∧ r ∣ n)).card : ℝ) ≤
      (N : ℝ) / ((q : ℝ) * r) := by
  have hEqual : (Finset.Icc 1 N).filter (fun n => q ∣ n ∧ r ∣ n) =
      (Finset.Icc 1 N).filter (fun n => q * r ∣ n) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hq, hr⟩
      exact ⟨hn, hCop.mul_dvd_of_dvd_of_dvd hq hr⟩
    · rintro ⟨hn, hqr⟩
      exact ⟨hn, (dvd_mul_right q r).trans hqr, (dvd_mul_left r q).trans hqr⟩
  rw [hEqual]
  simpa only [Nat.cast_mul] using prefix_multiples_card_le N (q * r) (Nat.mul_pos hq hr)

theorem pairwise_coprime_second_moment (N : ℕ) (Q : Finset ℕ)
    (hPos : ∀ q ∈ Q, 0 < q)
    (hCop : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r) :
    (∑ n ∈ Finset.Icc 1 N, (divisorIncidence Q n) ^ 2) ≤
      (N : ℝ) * ((reciprocalSum Q : ℝ) + (reciprocalSum Q : ℝ) ^ 2) := by
  have hPair : ∀ q ∈ Q, ∀ r ∈ Q,
      (((Finset.Icc 1 N).filter (fun n => q ∣ n ∧ r ∣ n)).card : ℝ) ≤
        (if q = r then (N : ℝ) / q else 0) + (N : ℝ) / ((q : ℝ) * r) := by
    intro q hq r hr
    by_cases hEq : q = r
    · subst r
      have hOne := prefix_multiples_card_le N q (hPos q hq)
      have hExtra : (0 : ℝ) ≤ (N : ℝ) / ((q : ℝ) * q) := by positivity
      simpa using hOne.trans (le_add_of_nonneg_right hExtra)
    · simpa only [ite_eq_right hEq, zero_add] using
        coprime_joint_multiples_card_le N q r (hPos q hq) (hPos r hr) (hCop q hq r hr hEq)
  have hRow : ∀ q ∈ Q,
      (∑ r ∈ Q, ((if q = r then (N : ℝ) / q else 0) + (N : ℝ) / ((q : ℝ) * r))) =
        (N : ℝ) / q + ((N : ℝ) / q) * (reciprocalSum Q : ℝ) := by
    intro q hq
    rw [Finset.sum_add_distrib]
    have hDiagonal : (∑ r ∈ Q, if q = r then (N : ℝ) / q else 0) = (N : ℝ) / q := by
      simp [hq]
    rw [hDiagonal]
    congr 1
    rw [reciprocalSum_eq_baseline, Erdos319Formal.reciprocalSum_real, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [div_eq_mul_inv, mul_inv, one_mul]
    ring
  have hLinear : (∑ q ∈ Q, (N : ℝ) / q) = (N : ℝ) * (reciprocalSum Q : ℝ) := by
    rw [reciprocalSum_eq_baseline, Erdos319Formal.reciprocalSum_real, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  calc
    (∑ n ∈ Finset.Icc 1 N, (divisorIncidence Q n) ^ 2) =
        ∑ q ∈ Q, ∑ r ∈ Q, (((Finset.Icc 1 N).filter (fun n => q ∣ n ∧ r ∣ n)).card : ℝ) :=
      sum_divisorIncidence_sq _ _
    _ ≤ ∑ q ∈ Q, ∑ r ∈ Q,
        ((if q = r then (N : ℝ) / q else 0) + (N : ℝ) / ((q : ℝ) * r)) :=
      Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (hPair q hq))
    _ = ∑ q ∈ Q, ((N : ℝ) / q + ((N : ℝ) / q) * (reciprocalSum Q : ℝ)) :=
      Finset.sum_congr rfl hRow
    _ = (N : ℝ) * ((reciprocalSum Q : ℝ) + (reciprocalSum Q : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hLinear]
      ring

end Erdos319Sharp
