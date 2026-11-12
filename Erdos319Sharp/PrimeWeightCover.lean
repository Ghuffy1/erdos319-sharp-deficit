import Erdos319Sharp.ExcessEuler

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem hasSum_nonzero_prime_excess (D p : ℕ) (hD : D ≠ 0) (hp : p.Prime) :
    HasSum (fun k : ℕ => if k = 0 then 0 else excessWeight D (p ^ k)) (primeExcessMass D p) := by
  have hTail : HasSum (fun k : ℕ => if k + 1 = 0 then 0 else excessWeight D (p ^ (k + 1)))
      (primeExcessMass D p) := by
    simpa using hasSum_prime_excess_tail D p hD hp
  have h := (hasSum_nat_add_iff (f := fun k : ℕ => if k = 0 then 0 else excessWeight D (p ^ k)) 1).mp hTail
  simpa using h

set_option maxHeartbeats 1000000 in
theorem hasSum_prime_divisible_excess (D p : ℕ) (P : Finset ℕ) (hD : D ≠ 0)
    (hP : ∀ q ∈ P, q.Prime) (hp : p.Prime) (hpNot : p ∉ P) :
    HasSum (fun n : Nat.factoredNumbers (insert p P) =>
      if p ∣ (n : ℕ) then excessWeight D n else 0)
      (primeExcessMass D p * excessEulerProduct D P) := by
  let g : ℕ → ℝ := fun k => if k = 0 then 0 else excessWeight D (p ^ k)
  have hLeft : HasSum g (primeExcessMass D p) := hasSum_nonzero_prime_excess D p hD hp
  have hRight := excess_factored_hasSum D P hD hP
  have hgNonneg : ∀ k, 0 ≤ g k := by
    intro k
    dsimp [g]
    split_ifs <;> first | exact le_rfl | exact excessWeight_nonneg D _
  have hNormLeft : Summable (fun k => ‖g k‖) := hLeft.summable.congr
    (fun k => (Real.norm_of_nonneg (hgNonneg k)).symm)
  have hNormRight : Summable (fun n : Nat.factoredNumbers P => ‖excessWeight D n‖) :=
    hRight.summable.congr (fun n => (Real.norm_of_nonneg (excessWeight_nonneg D n)).symm)
  have hPair : HasSum (fun z : ℕ × Nat.factoredNumbers P => g z.1 * excessWeight D z.2)
      (primeExcessMass D p * excessEulerProduct D P) :=
    hLeft.mul hRight (summable_mul_of_summable_norm hNormLeft hNormRight)
  let e := Nat.equivProdNatFactoredNumbers hp hpNot
  have hPoint (z : ℕ × Nat.factoredNumbers P) :
      (if p ∣ (e z : ℕ) then excessWeight D (e z) else 0) = g z.1 * excessWeight D z.2 := by
    rcases z with ⟨k, m⟩
    change (if p ∣ p ^ k * (m : ℕ) then excessWeight D (p ^ k * m) else 0) = g k * excessWeight D m
    have hCoprime : p.Coprime (m : ℕ) := hp.factoredNumbers_coprime hpNot m.property
    cases k with
    | zero =>
        have hNotDiv : ¬p ∣ (m : ℕ) := hp.coprime_iff_not_dvd.mp hCoprime
        simp [g, hNotDiv]
    | succ k =>
        have hDiv : p ∣ p ^ (k + 1) * (m : ℕ) :=
          (dvd_pow_self p (Nat.succ_ne_zero k)).trans (dvd_mul_right _ _)
        simp only [hDiv, ite_true, g, Nat.succ_ne_zero, ite_false]
        exact excessWeight_mul D _ _ hD (hCoprime.pow_left _)
  have hReindexed : HasSum (fun z : ℕ × Nat.factoredNumbers P =>
      if p ∣ (e z : ℕ) then excessWeight D (e z) else 0)
      (primeExcessMass D p * excessEulerProduct D P) := by
    rw [funext hPoint]
    exact hPair
  exact (e.hasSum_iff (f := fun n : Nat.factoredNumbers (insert p P) =>
    if p ∣ (n : ℕ) then excessWeight D n else 0)).mp hReindexed

theorem prime_divisible_excess_sum_le (D p : ℕ) (A P : Finset ℕ) (hD : D ≠ 0)
    (hP : ∀ q ∈ P, q.Prime) (hp : p ∈ P)
    (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers P) (hDiv : ∀ n ∈ A, p ∣ n) :
    (∑ n ∈ A, excessWeight D n) ≤ primeExcessMass D p * excessEulerProduct D (P.erase p) := by
  have hSeries := hasSum_prime_divisible_excess D p (P.erase p) hD
    (fun q hq => hP q (Finset.mem_of_mem_erase hq)) (hP p hp) (Finset.notMem_erase p P)
  rw [Finset.insert_erase hp] at hSeries
  calc
    (∑ n ∈ A, excessWeight D n) = ∑ n ∈ A, if p ∣ n then excessWeight D n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [hDiv n hn, ite_true]
    _ ≤ primeExcessMass D p * excessEulerProduct D (P.erase p) :=
      factored_finite_sum_le A P hA (fun n => by split_ifs <;> first | exact excessWeight_nonneg D n | exact le_rfl) hSeries

theorem prime_cover_excess_sum_le (D : ℕ) (A P H : Finset ℕ) (hD : D ≠ 0)
    (hP : ∀ p ∈ P, p.Prime) (hHP : H ⊆ P)
    (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers P) (hCover : ∀ n ∈ A, ∃ p ∈ H, p ∣ n) :
    (∑ n ∈ A, excessWeight D n) ≤ (∑ p ∈ H, primeExcessMass D p) *
      Real.exp (2 * ∑ p ∈ P, (firstMissingPower D p : ℝ)⁻¹) := by
  classical
  have hPoint : ∀ n ∈ A, excessWeight D n ≤ ∑ p ∈ H, if p ∣ n then excessWeight D n else 0 := by
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hCover n hn
    have h := Finset.single_le_sum
      (f := fun p => if p ∣ n then excessWeight D n else 0)
      (fun q hq => by split_ifs <;> first | exact excessWeight_nonneg D n | exact le_rfl) hp
    simpa only [hpn, ite_true] using h
  have hEach : ∀ p ∈ H, (∑ n ∈ A, if p ∣ n then excessWeight D n else 0) ≤
      primeExcessMass D p * Real.exp (2 * ∑ q ∈ P, (firstMissingPower D q : ℝ)⁻¹) := by
    intro p hp
    rw [← Finset.sum_filter]
    have hBound := prime_divisible_excess_sum_le D p (A.filter (fun n => p ∣ n)) P hD hP (hHP hp)
      (fun n hn => hA n (Finset.mem_filter.mp hn).1) (fun n hn => (Finset.mem_filter.mp hn).2)
    have hRho : (∑ q ∈ P.erase p, (firstMissingPower D q : ℝ)⁻¹) ≤
        ∑ q ∈ P, (firstMissingPower D q : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p P) (fun _ _ _ => by positivity)
    have hProduct : excessEulerProduct D (P.erase p) ≤
        Real.exp (2 * ∑ q ∈ P, (firstMissingPower D q : ℝ)⁻¹) :=
      (excessEulerProduct_le_exp D (P.erase p) (fun q hq => hP q (Finset.mem_of_mem_erase hq))).trans
        (Real.exp_le_exp.mpr (by linarith))
    exact hBound.trans (mul_le_mul_of_nonneg_left hProduct (primeExcessMass_nonneg D p (hP p (hHP hp))))
  calc
    (∑ n ∈ A, excessWeight D n) ≤ ∑ n ∈ A, ∑ p ∈ H, if p ∣ n then excessWeight D n else 0 :=
      Finset.sum_le_sum hPoint
    _ = ∑ p ∈ H, ∑ n ∈ A, if p ∣ n then excessWeight D n else 0 := Finset.sum_comm
    _ ≤ ∑ p ∈ H, primeExcessMass D p * Real.exp (2 * ∑ q ∈ P, (firstMissingPower D q : ℝ)⁻¹) :=
      Finset.sum_le_sum hEach
    _ = _ := (Finset.sum_mul _ _ _).symm

end Erdos319Sharp
