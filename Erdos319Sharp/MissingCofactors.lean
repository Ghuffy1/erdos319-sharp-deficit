import Erdos319Sharp.FirstMissingPowers

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem firstMissingPower_injective {D p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hEqual : firstMissingPower D p = firstMissingPower D q) : p = q := by
  by_contra hNe
  have hCop : (firstMissingPower D p).Coprime (firstMissingPower D q) :=
    (((Nat.coprime_primes hp hq).mpr hNe).pow_left _).pow_right _
  rw [hEqual] at hCop
  have hOne : firstMissingPower D q = 1 := by simpa [Nat.Coprime] using hCop
  have hLower := firstMissingPower_ge D q hq
  have hTwo := hq.two_le
  omega

theorem firstMissingPowers_reciprocal_sum (D N : ℕ) :
    (reciprocalSum (firstMissingPowers D N) : ℝ) =
      ∑ p ∈ (N.primesLE).filter (fun p => firstMissingPower D p ≤ N),
        (1 : ℝ) / firstMissingPower D p := by
  classical
  rw [reciprocalSum_eq_baseline, Erdos319Formal.reciprocalSum_real, firstMissingPowers,
    Finset.sum_image]
  intro p hp q hq hEqual
  exact firstMissingPower_injective (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2 hEqual

theorem exists_firstMissingPower_of_not_dvd (D N n : ℕ) (hD : D ≠ 0)
    (hn : 0 < n) (hnN : n ≤ N) (hNot : ¬ n ∣ D) :
    ∃ q ∈ firstMissingPowers D N, q ∣ n := by
  have hExponent : ∃ p : ℕ, D.factorization p < n.factorization p := by
    by_contra hNone
    have hLe : n.factorization ≤ D.factorization := by
      intro p
      exact le_of_not_gt (fun h => hNone ⟨p, h⟩)
    exact hNot ((Nat.factorization_le_iff_dvd hn.ne' hD).mp hLe)
  obtain ⟨p, hExponent⟩ := hExponent
  have hp : p.Prime := by
    by_contra hNonprime
    rw [Nat.factorization_eq_zero_of_not_prime n hNonprime] at hExponent
    omega
  have hPower : firstMissingPower D p ∣ n := by
    apply (hp.pow_dvd_iff_le_factorization hn.ne').mpr
    omega
  have hPowerN : firstMissingPower D p ≤ N := (Nat.le_of_dvd hn hPower).trans hnN
  exact ⟨firstMissingPower D p, firstMissingPower_mem hp hPowerN, hPower⟩

theorem nondivisors_card_le_firstMissingMass (D N t : ℕ) (hD : D ≠ 0) (ht : t ≤ N) :
    (((Finset.Icc 1 t).filter (fun n => ¬ n ∣ D)).card : ℝ) ≤
      (t : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) := by
  classical
  let Q := firstMissingPowers D N
  let A := (Finset.Icc 1 t).filter (fun n => ¬ n ∣ D)
  have hCover : A ⊆ Q.biUnion (fun q => (Finset.Icc 1 t).filter (fun n => q ∣ n)) := by
    intro n hn
    obtain ⟨hnI, hNot⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnPos, hnt⟩ := Finset.mem_Icc.mp hnI
    obtain ⟨q, hq, hqn⟩ := exists_firstMissingPower_of_not_dvd D N n hD hnPos (hnt.trans ht) hNot
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨hnI, hqn⟩⟩
  have hCount : (A.card : ℝ) ≤ ∑ q ∈ Q, (((Finset.Icc 1 t).filter (fun n => q ∣ n)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hCover).trans Finset.card_biUnion_le
  change (A.card : ℝ) ≤ (t : ℝ) * (reciprocalSum Q : ℝ)
  calc
    (A.card : ℝ) ≤ ∑ q ∈ Q, (((Finset.Icc 1 t).filter (fun n => q ∣ n)).card : ℝ) := hCount
    _ ≤ ∑ q ∈ Q, (t : ℝ) / q := Finset.sum_le_sum (fun q hq =>
      prefix_multiples_card_le t q (firstMissingPowers_conditions hD q hq).1)
    _ = (t : ℝ) * (reciprocalSum Q : ℝ) := by
      rw [reciprocalSum_eq_baseline, Erdos319Formal.reciprocalSum_real, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

end Erdos319Sharp
