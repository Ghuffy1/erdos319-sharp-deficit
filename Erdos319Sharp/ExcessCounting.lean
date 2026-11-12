import Erdos319Sharp.CofactorDensity
import Erdos319Sharp.PrimeWeightCover
import Erdos319Sharp.WeightSupport

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem dvd_of_denominatorExcess_eq_one (D n : ℕ) (hOne : denominatorExcess D n = 1) :
    n ∣ D := by
  have hProduct : n.gcd D * denominatorExcess D n = n :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n D)
  rw [hOne, mul_one] at hProduct
  rw [← hProduct]
  exact Nat.gcd_dvd_right n D

theorem excessCofactors_mono (D b : ℕ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    excessCofactors D b A ⊆ excessCofactors D b B := by
  apply Finset.image_subset_image
  intro n hn
  obtain ⟨hnA, hnExcess⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hAB hnA, hnExcess⟩

theorem card_activeExcesses (D : ℕ) (A : Finset ℕ) :
    A.card = ∑ b ∈ activeExcesses D A, (excessGroup D b A).card := by
  classical
  apply Finset.card_eq_sum_card_fiberwise
  intro n hn
  exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

theorem active_excess_weights_nondivisor_bound (D N : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hA : A ⊆ Finset.Icc 1 N) (hNot : ∀ n ∈ A, ¬ n ∣ D) :
    (∑ b ∈ activeExcesses D A, excessWeight D b) ≤
      2 * (reciprocalSum (firstMissingPowers D N) : ℝ) *
        Real.exp (2 * (reciprocalSum (firstMissingPowers D N) : ℝ)) := by
  classical
  have hFactored := activeExcesses_factored D N A hD hA
  have hCover : ∀ b ∈ activeExcesses D A, ∃ p ∈ missingPrimeBases D N, p ∣ b := by
    intro b hb
    have hbOne : b ≠ 1 := by
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
      intro hOne
      exact hNot n hn (dvd_of_denominatorExcess_eq_one D n hOne)
    obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hbOne
    exact ⟨p, (Nat.mem_factoredNumbers'.mp (hFactored b hb)) p hp hpb, hpb⟩
  have hWeight := prime_cover_excess_sum_le D (activeExcesses D A)
    (missingPrimeBases D N) (missingPrimeBases D N) hD
    (fun p hp => missingPrimeBases_prime D N p hp) Finset.Subset.rfl hFactored hCover
  have hPrimeSum : (∑ p ∈ missingPrimeBases D N, primeExcessMass D p) ≤
      2 * (reciprocalSum (firstMissingPowers D N) : ℝ) := by
    calc
      _ ≤ ∑ p ∈ missingPrimeBases D N, 2 * (firstMissingPower D p : ℝ)⁻¹ :=
        Finset.sum_le_sum (fun p hp => primeExcessMass_le_two D p (missingPrimeBases_prime D N p hp))
      _ = _ := by rw [← Finset.mul_sum, ← missingPrimeBases_mass]
  rw [← missingPrimeBases_mass] at hWeight
  exact hWeight.trans (mul_le_mul_of_nonneg_right hPrimeSum (Real.exp_nonneg _))

theorem eventually_small_scale_nondivisor_count (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (D : ℕ) (A : Finset ℕ),
      D ≠ 0 → A ⊆ Finset.Icc 1 N → (∀ n ∈ A, ¬ n ∣ D) →
      (∀ b : ℕ, 0 < b → InverseZeroSumFree b (excessCofactors D b A)) →
      (∀ n ∈ A, (excessScale D (denominatorExcess D n) : ℝ) ≤ smoothCutoff 6 N) →
      (A.card : ℝ) ≤ 2 * ε * (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) *
        Real.exp (2 * (reciprocalSum (firstMissingPowers D N) : ℝ)) := by
  filter_upwards [eventually_small_scale_excess_group_card ε hε] with N hCount
  intro D A hD hA hNot hFree hScale
  have hEach : ∀ b ∈ activeExcesses D A, ((excessGroup D b A).card : ℝ) ≤
      (ε * N) * excessWeight D b := by
    intro b hb
    have hbBounds := Finset.mem_Icc.mp (activeExcesses_bounds D N A hA hb)
    have hScaleB : (excessScale D b : ℝ) ≤ smoothCutoff 6 N := by
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
      exact hScale n hn
    simpa only [div_eq_mul_inv, excessWeight] using
      hCount D b A hD hbBounds.1 hbBounds.2 hA (hFree b hbBounds.1) hScaleB
  have hSplit : (A.card : ℝ) = ∑ b ∈ activeExcesses D A, ((excessGroup D b A).card : ℝ) := by
    exact_mod_cast card_activeExcesses D A
  have hWeight := active_excess_weights_nondivisor_bound D N A hD hA hNot
  calc
    (A.card : ℝ) = ∑ b ∈ activeExcesses D A, ((excessGroup D b A).card : ℝ) := hSplit
    _ ≤ ∑ b ∈ activeExcesses D A, (ε * N) * excessWeight D b := Finset.sum_le_sum hEach
    _ = (ε * N) * ∑ b ∈ activeExcesses D A, excessWeight D b := (Finset.mul_sum _ _ _).symm
    _ ≤ (ε * N) * (2 * (reciprocalSum (firstMissingPowers D N) : ℝ) *
        Real.exp (2 * (reciprocalSum (firstMissingPowers D N) : ℝ))) :=
      mul_le_mul_of_nonneg_left hWeight (mul_nonneg hε.le (Nat.cast_nonneg N))
    _ = _ := by ring

end Erdos319Sharp
