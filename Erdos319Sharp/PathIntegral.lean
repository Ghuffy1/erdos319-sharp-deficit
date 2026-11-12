import Erdos319Sharp.PathSupport
import Erdos319Sharp.PrimeProductResidue

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem path_integral_iff (k D : ℕ) (p u : ℕ → ℕ) (C : Finset ℕ) (hD : 0 < D)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬ p i ∣ D)
    (hUPositive : ∀ i < k - 1, 0 < u i)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬ p j ∣ u i)
    (hC : C ⊆ pathSupport k D p u) :
    DIntegral ((Finset.range k).prod p) (reciprocalSum C) ↔
      ∀ i < k, (∑ n ∈ C.filter (fun n => p i ∣ n), ((n / p i : ℕ) : ZMod (p i))⁻¹) = 0 := by
  classical
  let P := (Finset.range k).image p
  let G := P.prod id
  let U := D * (Finset.range (k - 1)).prod u
  have hMarks : G = (Finset.range k).prod p := by
    dsimp [G, P]
    rw [Finset.prod_image (fun i hi j hj hEqual =>
      hInjective i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hEqual)]
    rfl
  have hPPrime : ∀ s ∈ P, s.Prime := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    exact hPrime i (Finset.mem_range.mp hi)
  have hU : 0 < U := Nat.mul_pos hD (Finset.prod_pos (fun i hi => hUPositive i (Finset.mem_range.mp hi)))
  have hUCoprime : U.Coprime G := by
    apply Nat.coprime_prod_right_iff.mpr
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hjRange := Finset.mem_range.mp hj
    have hDCop : D.Coprime (p j) := ((hPrime j hjRange).coprime_iff_not_dvd.mpr (hAvoidD j hjRange)).symm
    have hProdCop : ((Finset.range (k - 1)).prod u).Coprime (p j) := by
      apply Nat.coprime_prod_left_iff.mpr
      intro i hi
      exact ((hPrime j hjRange).coprime_iff_not_dvd.mpr
        (hAvoidU i (Finset.mem_range.mp hi) j hjRange)).symm
    exact hDCop.mul_left hProdCop
  have hMarkDiv : ∀ i < k, p i ∣ G := by
    intro i hi
    exact Finset.dvd_prod_of_mem id (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
  have hSupportDiv : ∀ n ∈ pathSupport k D p u, n ∣ G * U := by
    intro n hn
    rcases Finset.mem_union.mp hn with hBlock | hEdge
    · obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hBlock
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hni
      have hbU : b ∣ U := (Nat.dvd_of_mem_divisors hb).trans (dvd_mul_right D _)
      exact Nat.mul_dvd_mul (hMarkDiv i (Finset.mem_range.mp hi)) hbU
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hEdge
      have hiRange := Finset.mem_range.mp hi
      have hiVertex : i < k := by omega
      have hiNext : i + 1 < k := by omega
      have hDistinct : p i ≠ p (i + 1) := by
        intro hEqual
        have h := hInjective i hiVertex (i + 1) hiNext hEqual
        omega
      have hPair : p i * p (i + 1) ∣ G :=
        ((Nat.coprime_primes (hPrime i hiVertex) (hPrime (i + 1) hiNext)).mpr hDistinct).mul_dvd_of_dvd_of_dvd
          (hMarkDiv i hiVertex) (hMarkDiv (i + 1) hiNext)
      have huU : u i ∣ U := (Finset.dvd_prod_of_mem u hi).trans (dvd_mul_left _ D)
      exact Nat.mul_dvd_mul hPair huU
  rw [← hMarks, integral_iff_local_inverse_sums P C U hPPrime hU hUCoprime
    (fun n hn => hSupportDiv n (hC hn))]
  constructor
  · intro h i hi
    exact h (p i) (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
  · intro h s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    exact h i (Finset.mem_range.mp hi)

end Erdos319Sharp
