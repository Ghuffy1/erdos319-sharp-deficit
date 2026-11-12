import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem prime_cover_card_bound (N : ℕ) (A P : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hP : ∀ p ∈ P, p.Prime)
    (hCover : ∀ n ∈ A, ∃ p ∈ P, p ∣ n) :
    (A.card : ℝ) ≤ N * (∑ p ∈ P, (1 : ℝ) / p) := by
  classical
  have hUnion : A ⊆ P.biUnion (fun p => (Finset.Icc 1 N).filter (fun n => p ∣ n)) := by
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hCover n hn
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hA hn, hpn⟩⟩
  have hCard : A.card ≤ ∑ p ∈ P, ((Finset.Icc 1 N).filter (fun n => p ∣ n)).card :=
    (Finset.card_le_card hUnion).trans Finset.card_biUnion_le
  calc
    (A.card : ℝ) ≤ ∑ p ∈ P, (((Finset.Icc 1 N).filter (fun n => p ∣ n)).card : ℝ) := by
      exact_mod_cast hCard
    _ ≤ ∑ p ∈ P, (N : ℝ) / p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [card_divisible_interval N p (hP p hp).pos]
      exact Nat.cast_div_le
    _ = N * (∑ p ∈ P, (1 : ℝ) / p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- A positive-density set covered by large prime divisors has a large lcm. -/
theorem log_lcm_lower_bound_of_large_prime_cover (N : ℕ) (A : Finset ℕ) (L β : ℝ)
    (hN : 0 < N) (hA : A ⊆ Finset.Icc 1 N) (hL : 1 < L)
    (hCard : β * N ≤ (A.card : ℝ))
    (hLarge : ∀ n ∈ A, ∃ p : ℕ, p.Prime ∧ L ≤ (p : ℝ) ∧ p ∣ n) :
    β * L * Real.log L ≤ Real.log (A.lcm id : ℕ) := by
  classical
  let D := A.lcm id
  let P : Finset ℕ := D.primeFactors.filter (fun p : ℕ => L ≤ (p : ℝ))
  have hPos : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  have hD : 0 < D := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos n hn).ne'))
  have hP : ∀ (p : ℕ), p ∈ P → p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hPD : ∀ (p : ℕ), p ∈ P → p ∣ D := fun p hp =>
    Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hPL : ∀ (p : ℕ), p ∈ P → L ≤ (p : ℝ) := fun p hp => (Finset.mem_filter.mp hp).2
  have hCover : ∀ n ∈ A, ∃ p ∈ P, p ∣ n := by
    intro n hn
    obtain ⟨p, hp, hpL, hpn⟩ := hLarge n hn
    have hpD : p ∣ D := hpn.trans (Finset.dvd_lcm hn)
    exact ⟨p, Finset.mem_filter.mpr ⟨hp.mem_primeFactors hpD hD.ne', hpL⟩, hpn⟩
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMass : β ≤ ∑ p ∈ P, (1 : ℝ) / p := by
    have h := hCard.trans (prime_cover_card_bound N A P hA hP hCover)
    apply (mul_le_mul_iff_of_pos_left hNReal).mp
    simpa only [mul_comm] using h
  have hProdDiv : (∏ p ∈ P, p) ∣ D :=
    (sieve_prime_product_dvd_iff P hP D).mpr hPD
  have hProdPos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hLogBound : (∑ p ∈ P, Real.log (p : ℝ)) ≤ Real.log (D : ℝ) := by
    have hLe : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ D := by
      exact_mod_cast Nat.le_of_dvd hD hProdDiv
    have hLog := Real.log_le_log (by exact_mod_cast hProdPos) hLe
    have hIdentity : Real.log ((∏ p ∈ P, p : ℕ) : ℝ) = ∑ p ∈ P, Real.log (p : ℝ) := by
      rw [Nat.cast_prod]
      exact Real.log_prod (fun p hp => by exact_mod_cast (hP p hp).ne_zero)
    rwa [hIdentity] at hLog
  have hLPos : 0 < L := by linarith
  have hLogL : 0 ≤ Real.log L := (Real.log_pos hL).le
  have hWeighted : (L * Real.log L) * (∑ p ∈ P, (1 : ℝ) / p) ≤
      ∑ p ∈ P, Real.log (p : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hLogP : Real.log L ≤ Real.log (p : ℝ) := Real.log_le_log hLPos (hPL p hp)
    have hMul : L * Real.log L ≤ (p : ℝ) * Real.log (p : ℝ) :=
      mul_le_mul (hPL p hp) hLogP hLogL hpPos.le
    rw [mul_one_div]
    exact (div_le_iff₀ hpPos).mpr (by simpa only [mul_comm] using hMul)
  calc
    β * L * Real.log L = β * (L * Real.log L) := by ring
    _ ≤ (∑ p ∈ P, (1 : ℝ) / p) * (L * Real.log L) :=
      mul_le_mul_of_nonneg_right hMass (mul_nonneg hLPos.le hLogL)
    _ = (L * Real.log L) * (∑ p ∈ P, (1 : ℝ) / p) := by ring
    _ ≤ ∑ p ∈ P, Real.log (p : ℝ) := hWeighted
    _ ≤ Real.log (D : ℝ) := hLogBound

end Erdos319Sharp
