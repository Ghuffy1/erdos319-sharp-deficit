import Erdos319Sharp.ExcessGroups
import Erdos319Sharp.ExcessWeights
import Mathlib.NumberTheory.SmoothNumbers

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def activeExcesses (D : ℕ) (A : Finset ℕ) : Finset ℕ := A.image (denominatorExcess D)

def missingPrimeBases (D N : ℕ) : Finset ℕ :=
  N.primesLE.filter (fun p => firstMissingPower D p ≤ N)

theorem missingPrimeBases_prime (D N p : ℕ) (hp : p ∈ missingPrimeBases D N) : p.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2

theorem missingPrimeBases_mass (D N : ℕ) :
    (reciprocalSum (firstMissingPowers D N) : ℝ) =
      ∑ p ∈ missingPrimeBases D N, (firstMissingPower D p : ℝ)⁻¹ := by
  simpa only [missingPrimeBases, one_div] using firstMissingPowers_reciprocal_sum D N

theorem activeExcesses_bounds (D N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    activeExcesses D A ⊆ Finset.Icc 1 N := by
  intro b hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hnPos, hnN⟩ := Finset.mem_Icc.mp (hA hn)
  exact Finset.mem_Icc.mpr ⟨denominatorExcess_pos D n hnPos,
    (Nat.div_le_self n (n.gcd D)).trans hnN⟩

theorem firstMissingPower_dvd_of_prime_dvd_excess (D n p : ℕ) (hD : D ≠ 0) (hn : 0 < n)
    (hp : p.Prime) (hDiv : p ∣ denominatorExcess D n) : firstMissingPower D p ∣ n := by
  have hbPos := denominatorExcess_pos D n hn
  have hExponent := factorization_eq_add_of_dvd_excess D n (denominatorExcess D n) p hD hn.ne' rfl hp hDiv
  have hPositive := hp.factorization_pos_of_dvd hbPos.ne' hDiv
  apply (hp.pow_dvd_iff_le_factorization hn.ne').mpr
  omega

theorem activeExcesses_factored (D N : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hA : A ⊆ Finset.Icc 1 N) : ∀ b ∈ activeExcesses D A, b ∈ Nat.factoredNumbers (missingPrimeBases D N) := by
  intro b hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hnPos, hnN⟩ := Finset.mem_Icc.mp (hA hn)
  apply Nat.mem_factoredNumbers_of_primeFactors_subset (denominatorExcess_pos D n hnPos).ne'
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpDiv := Nat.dvd_of_mem_primeFactors hp
  have hPower := firstMissingPower_dvd_of_prime_dvd_excess D n p hD hnPos hpPrime hpDiv
  have hPowerN : firstMissingPower D p ≤ N := (Nat.le_of_dvd hnPos hPower).trans hnN
  exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(firstMissingPower_ge D p hpPrime).trans hPowerN, hpPrime⟩, hPowerN⟩

theorem reciprocalSum_activeExcesses (D : ℕ) (A : Finset ℕ) :
    (∑ b ∈ activeExcesses D A, reciprocalSum (excessGroup D b A)) = reciprocalSum A := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro n hn
  exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

end Erdos319Sharp
