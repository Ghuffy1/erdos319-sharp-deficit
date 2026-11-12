import Erdos319Sharp.LocalResidue

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem integral_iff_local_inverse_sums (P A : Finset ℕ) (D : ℕ)
    (hPrime : ∀ p ∈ P, p.Prime) (hD : 0 < D) (hCoprime : D.Coprime (P.prod id))
    (hDiv : ∀ n ∈ A, n ∣ P.prod id * D) :
    DIntegral (P.prod id) (reciprocalSum A) ↔
      ∀ p ∈ P, (∑ n ∈ A.filter (fun n => p ∣ n), ((n / p : ℕ) : ZMod p)⁻¹) = 0 := by
  let G := P.prod id
  have hG : 0 < G := Finset.prod_pos (fun p hp => (hPrime p hp).pos)
  have hFactor : ∀ p ∈ P, G * D = p * ((G / p) * D) := by
    intro p hp
    have hpG : p ∣ G := Finset.dvd_prod_of_mem id hp
    rw [← mul_assoc, Nat.mul_div_cancel' hpG]
  have hLocal : ∀ p ∈ P, ((G / p) * D).Coprime p ∧
      ∀ n ∈ A, n ∣ p * ((G / p) * D) := by
    intro p hp
    have hpG : p ∣ G := Finset.dvd_prod_of_mem id hp
    have hRest : (G / p).Coprime p := (primeProduct_div_coprime P hPrime hp).symm
    have hDCop : D.Coprime p := Nat.Coprime.of_dvd_right hpG hCoprime
    refine ⟨hRest.mul_left hDCop, ?_⟩
    intro n hn
    rw [← hFactor p hp]
    exact hDiv n hn
  constructor
  · intro hIntegral p hp
    exact local_inverse_sum_zero_of_integral A G p ((G / p) * D) (hPrime p hp)
      (Finset.dvd_prod_of_mem id hp) (hLocal p hp).1 (hLocal p hp).2 hIntegral
  · intro hZero
    have hTotal : G ∣ ∑ n ∈ A, (G * D) / n := by
      apply primeProduct_dvd_of_all P _ hPrime
      intro p hp
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      have hSum := cofactor_sum_eq_local_inverse_sum A p ((G / p) * D) (hPrime p hp)
        (hLocal p hp).1 (hLocal p hp).2
      rw [hZero p hp, mul_zero, ← hFactor p hp] at hSum
      exact hSum
    exact integral_of_cofactor_divisibility A G D hG hD hCoprime hDiv hTotal

end Erdos319Sharp
