import Erdos319Sharp.PathDichotomy
import Erdos319Sharp.PathBounds

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem pathBlockSelection_support (k D : ℕ) (p u : ℕ → ℕ) {i : ℕ} (hi : i < k) :
    pathBlockSelection D p i (pathSupport k D p u) = D.divisors := by
  classical
  apply Finset.filter_eq_self.mpr
  intro b hb
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
    Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩)

theorem pathEdge_mem_support (k D : ℕ) (p u : ℕ → ℕ) {i : ℕ} (hi : i < k - 1) :
    pathEdge p u i ∈ pathSupport k D p u :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)

theorem pathSupport_integral (k D : ℕ) (p u : ℕ → ℕ)
    (a b : (i : ℕ) → (ZMod (p i))ˣ) (hk : 2 ≤ k) (hD : 0 < D)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬p i ∣ D)
    (hUPositive : ∀ i < k - 1, 0 < u i)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬p j ∣ u i)
    (hFirst : (b 0 : ZMod (p 0)) = -(∑ n ∈ D.divisors, (n : ZMod (p 0))⁻¹))
    (hLast : ∀ i < k, i + 1 = k → (a i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹))
    (hBalance : ∀ i, 0 < i → i + 1 < k →
      (b i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹) - (a i : ZMod (p i)))
    (hOutgoing : ∀ i < k - 1, (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) = (b i : ZMod (p i)))
    (hIncoming : ∀ i < k - 1, (((p i * u i : ℕ) : ZMod (p (i + 1)))⁻¹) = (a (i + 1) : ZMod (p (i + 1)))) :
    DIntegral ((Finset.range k).prod p) (reciprocalSum (pathSupport k D p u)) := by
  apply (path_integral_iff k D p u (pathSupport k D p u) hD hPrime hInjective hAvoidD hUPositive hAvoidU Finset.Subset.rfl).mpr
  intro i hi
  rw [pathSubset_local_sum k D p u (pathSupport k D p u) hPrime hInjective hAvoidD hAvoidU Finset.Subset.rfl hi,
    pathBlockSelection_support k D p u hi]
  by_cases hZero : i = 0
  · subst i
    have hEdge : pathEdge p u 0 ∈ pathSupport k D p u := pathEdge_mem_support k D p u (by omega)
    have hOne : 0 + 1 < k := by omega
    have hNotPositive : ¬(0 : ℕ) < 0 := by omega
    simp only [hNotPositive, false_and, ite_false, add_zero, hOne, hEdge, true_and,
      ite_true, hOutgoing 0 (by omega), hFirst, add_neg_cancel]
  · have hPositive : 0 < i := by omega
    have hPrev : i - 1 < k - 1 := by omega
    have hInEdge : pathEdge p u (i - 1) ∈ pathSupport k D p u := pathEdge_mem_support k D p u hPrev
    have hIn : (((p (i - 1) * u (i - 1) : ℕ) : ZMod (p i))⁻¹) = (a i : ZMod (p i)) := by
      exact pathIncoming_at_vertex k p u a hIncoming hPositive hi
    by_cases hEnd : i + 1 = k
    · have hNoOut : ¬i + 1 < k := by omega
      simp only [hPositive, hNoOut, hInEdge, true_and, false_and, ite_true, ite_false,
        add_zero, hIn, hLast i hi hEnd, add_neg_cancel]
    · have hInterior : i + 1 < k := by omega
      have hOutEdge : pathEdge p u i ∈ pathSupport k D p u := pathEdge_mem_support k D p u (by omega)
      rw [if_pos ⟨hPositive, hInEdge⟩, if_pos ⟨hInterior, hOutEdge⟩, hIn,
        hOutgoing i (by omega), hBalance i hPositive hInterior]
      ring

theorem pathSupport_minimalCore (k D : ℕ) (p u : ℕ → ℕ)
    (a b : (i : ℕ) → (ZMod (p i))ˣ) (hk : 2 ≤ k) (hD : 0 < D)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬p i ∣ D)
    (hUPositive : ∀ i < k - 1, 0 < u i)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬p j ∣ u i)
    (hBound : ∀ i < k, (∑ n ∈ D.divisors, D / n) + 1 < p i)
    (hFirst : (b 0 : ZMod (p 0)) = -(∑ n ∈ D.divisors, (n : ZMod (p 0))⁻¹))
    (hLast : ∀ i < k, i + 1 = k → (a i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹))
    (hBalance : ∀ i, 0 < i → i + 1 < k →
      (b i : ZMod (p i)) = -(∑ n ∈ D.divisors, (n : ZMod (p i))⁻¹) - (a i : ZMod (p i)))
    (hRules : ∀ i, 0 < i → i + 1 < k → ∀ B ⊆ D.divisors, ∀ incoming outgoing : Bool,
      (∑ n ∈ B, (n : ZMod (p i))⁻¹) + (if incoming then (a i : ZMod (p i)) else 0) +
        (if outgoing then (b i : ZMod (p i)) else 0) = 0 →
      incoming = outgoing ∧ B = if incoming then D.divisors else ∅)
    (hOutgoing : ∀ i < k - 1, (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) = (b i : ZMod (p i)))
    (hIncoming : ∀ i < k - 1, (((p i * u i : ℕ) : ZMod (p (i + 1)))⁻¹) = (a (i + 1) : ZMod (p (i + 1)))) :
    MinimalCore ((Finset.range k).prod p) (pathSupport k D p u) := by
  refine ⟨pathSupport_positive_and_not_coprime k D p u hPrime hUPositive,
    pathSupport_integral k D p u a b hk hD hPrime hInjective hAvoidD hUPositive hAvoidU hFirst hLast hBalance hOutgoing hIncoming, ?_⟩
  intro C hC hIntegral
  exact path_integral_subset_dichotomy k D p u a b hk hD hPrime hInjective hAvoidD hUPositive hAvoidU
    hBound hFirst hLast hRules hOutgoing hIncoming C hC hIntegral

end Erdos319Sharp
