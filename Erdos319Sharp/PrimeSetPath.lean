import Erdos319Sharp.BoundedPath
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem exists_prime_set_path_core (P : Finset ℕ) (D L M : ℕ)
    (hCard : 2 ≤ P.card) (hD : 0 < D) (hL : 0 < L)
    (hPrime : ∀ p ∈ P, p.Prime) (hAvoidD : ∀ p ∈ P, ¬p ∣ D)
    (hBound : ∀ p ∈ P, (∑ n ∈ D.divisors, D / n) + 1 < p)
    (hLower : ∀ p ∈ P, L ≤ p) (hUpper : ∀ p ∈ P, p ≤ M)
    (hMass : (∑ p ∈ P, (1 : ℝ) / p) ≤ 1 / 2) :
    ∃ E : Finset ℕ, MinimalCore (P.prod id) E ∧
      E ⊆ Finset.Icc 1 (max (M * D) (4 * P.card * M ^ 4)) ∧
      reciprocalSum D.divisors * reciprocalSum P ≤ reciprocalSum E ∧
      reciprocalSum E ≤ reciprocalSum D.divisors * reciprocalSum P + reciprocalSum P / L := by
  classical
  let k := P.card
  let e : Fin k ↪o ℕ := P.orderEmbOfFin rfl
  let p : ℕ → ℕ := fun i => if hi : i < k then e ⟨i, hi⟩ else 1
  have hMem : ∀ i < k, p i ∈ P := by
    intro i hi
    simp only [p, dif_pos hi]
    exact Finset.orderEmbOfFin_mem P rfl ⟨i, hi⟩
  have hInj : ∀ i < k, ∀ j < k, p i = p j → i = j := by
    intro i hi j hj hEqual
    have hFin : (⟨i, hi⟩ : Fin k) = ⟨j, hj⟩ := e.injective (by
      simpa only [p, dif_pos hi, dif_pos hj] using hEqual)
    exact congrArg Fin.val hFin
  have hImage : (Finset.range k).image p = P := by
    apply Finset.Subset.antisymm
    · intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      exact hMem i (Finset.mem_range.mp hi)
    · intro n hn
      have hEnum : n ∈ (Finset.univ : Finset (Fin k)).image e := by
        simpa only [e, Finset.image_orderEmbOfFin_univ] using hn
      obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp hEnum
      refine Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
      simpa only [p, dif_pos i.isLt, Fin.eta] using hEq
  have hInjective : Set.InjOn p (Finset.range k) := fun i hi j hj hEqual =>
    hInj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hEqual
  have hProduct : (Finset.range k).prod p = P.prod id := by
    calc
      _ = ((Finset.range k).image p).prod id := by
        simpa only [id_eq] using (Finset.prod_image (f := id) hInjective).symm
      _ = _ := congrArg (fun S : Finset ℕ => S.prod id) hImage
  have hReciprocal : (∑ i ∈ Finset.range k, (p i : ℚ)⁻¹) = reciprocalSum P := by
    calc
      _ = ∑ n ∈ (Finset.range k).image p, (n : ℚ)⁻¹ := (Finset.sum_image hInjective).symm
      _ = _ := by rw [hImage]; rfl
  have hRealSum : (∑ i ∈ Finset.range k, (1 : ℝ) / p i) = ∑ n ∈ P, (1 : ℝ) / n := by
    calc
      _ = ∑ n ∈ (Finset.range k).image p, (1 : ℝ) / n := (Finset.sum_image hInjective).symm
      _ = _ := congrArg (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℝ) / n) hImage
  obtain ⟨E, hCore, hE, hMassLower, hMassUpper⟩ := exists_bounded_path_core k D L M p hCard hD hL
    (fun i hi => hPrime (p i) (hMem i hi)) hInj
    (fun i hi => hAvoidD (p i) (hMem i hi))
    (fun i hi => hBound (p i) (hMem i hi))
    (fun i hi => hLower (p i) (hMem i hi))
    (fun i hi => hUpper (p i) (hMem i hi)) (by rw [hRealSum]; exact hMass)
  refine ⟨E, ?_, hE, ?_, ?_⟩
  · simpa only [hProduct] using hCore
  · simpa only [hReciprocal] using hMassLower
  · simpa only [hReciprocal] using hMassUpper

end Erdos319Sharp
