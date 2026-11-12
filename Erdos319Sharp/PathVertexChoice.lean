import Erdos319Sharp.DivisorBlockResidue

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem exists_path_vertex_choices (k D : ℕ) (p : ℕ → ℕ) (hk : 2 ≤ k) (hD : 0 < D)
    (hPrime : ∀ i < k, (p i).Prime) (hCoprime : ∀ i < k, D.Coprime (p i))
    (hBound : ∀ i < k, (∑ n ∈ D.divisors, D / n) + 1 < p i) :
    ∃ a b : (i : ℕ) → (ZMod (p i))ˣ,
      (∀ i < k, i = 0 → (b i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹)) ∧
      (∀ i < k, i + 1 = k → (a i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹)) ∧
      ∀ i, 0 < i → i + 1 < k →
        (b i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹) - (a i : ZMod (p i)) ∧
        ∀ B ⊆ D.divisors, ∀ incoming outgoing : Bool,
          (∑ n ∈ B, (n : ZMod (p i))⁻¹) + (if incoming then (a i : ZMod (p i)) else 0) +
            (if outgoing then (b i : ZMod (p i)) else 0) = 0 →
          incoming = outgoing ∧ B = if incoming then D.divisors else ∅ := by
  classical
  have hChoices : ∀ i : ℕ, ∃ a b : (ZMod (p i))ˣ,
      (i < k → i = 0 → (b : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹)) ∧
      (i < k → i + 1 = k → (a : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹)) ∧
      (0 < i → i + 1 < k →
        (b : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹) - (a : ZMod (p i)) ∧
        ∀ B ⊆ D.divisors, ∀ incoming outgoing : Bool,
          (∑ n ∈ B, (n : ZMod (p i))⁻¹) + (if incoming then (a : ZMod (p i)) else 0) +
            (if outgoing then (b : ZMod (p i)) else 0) = 0 →
          incoming = outgoing ∧ B = if incoming then D.divisors else ∅) := by
    intro i
    by_cases hi : i < k
    · letI : Fact (p i).Prime := ⟨hPrime i hi⟩
      have hSmall : (∑ n ∈ D.divisors, D / n) < p i := by have := hBound i hi; omega
      have hNonzero := divisor_inverse_sum_ne_zero (p i) D (hPrime i hi).pos hD (hCoprime i hi) hSmall
      by_cases hFirst : i = 0
      · refine ⟨1, Units.mk0 (-(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹)) (neg_ne_zero.mpr hNonzero), ?_, ?_, ?_⟩
        · intro _ _
          rfl
        · intro _ hLast
          omega
        · intro hPositive _
          omega
      · by_cases hLast : i + 1 = k
        · refine ⟨Units.mk0 (-(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹)) (neg_ne_zero.mpr hNonzero), 1, ?_, ?_, ?_⟩
          · intro _ hZero
            exact (hFirst hZero).elim
          · intro _ _
            rfl
          · intro _ hInterior
            omega
        · obtain ⟨a, b, hb, hLocal⟩ := exists_divisor_block_path_residues (p i) D (hPrime i hi) hD
            (hCoprime i hi) (hBound i hi)
          refine ⟨a, b, ?_, ?_, ?_⟩
          · intro _ hZero
            exact (hFirst hZero).elim
          · intro _ hEndpoint
            exact (hLast hEndpoint).elim
          · intro _ _
            exact ⟨hb, hLocal⟩
    · refine ⟨1, 1, ?_, ?_, ?_⟩
      · intro hValid _
        exact (hi hValid).elim
      · intro hValid _
        exact (hi hValid).elim
      · intro _ hInterior
        omega
  choose a b hChoices using hChoices
  exact ⟨a, b, fun i hi hFirst => (hChoices i).1 hi hFirst,
    fun i hi hLast => (hChoices i).2.1 hi hLast,
    fun i hPositive hInterior => (hChoices i).2.2 hPositive hInterior⟩

end Erdos319Sharp
