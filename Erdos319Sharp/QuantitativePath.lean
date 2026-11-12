import Erdos319Sharp.PathCore
import Erdos319Sharp.PathVertexChoice
import Erdos319Sharp.PrimeSetConnector
import Erdos319Sharp.PathMass

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem exists_quantitative_path_core (k D : ℕ) (p : ℕ → ℕ) (hk : 2 ≤ k) (hD : 0 < D)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬p i ∣ D)
    (hBound : ∀ i < k, (∑ n ∈ D.divisors, D / n) + 1 < p i)
    (hMass : (∑ i ∈ Finset.range k, (1 : ℝ) / p i) ≤ 1 / 2) :
    ∃ u : ℕ → ℕ,
      (∀ i < k - 1, 0 < u i ∧ u i < 4 * k * p i * p (i + 1) ∧
        ∀ j < k, ¬p j ∣ u i) ∧
      MinimalCore ((Finset.range k).prod p) (pathSupport k D p u) := by
  classical
  let P := (Finset.range k).image p
  have hPPrime : ∀ s ∈ P, s.Prime := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    exact hPrime i (Finset.mem_range.mp hi)
  have hPCard : P.card ≤ k := by
    simpa only [Finset.card_range] using (Finset.card_image_le : P.card ≤ (Finset.range k).card)
  have hPMass : (∑ s ∈ P, (1 : ℝ) / s) ≤ 1 / 2 := by
    dsimp [P]
    rw [Finset.sum_image (fun i hi j hj hEqual =>
      hInjective i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hEqual)]
    exact hMass
  have hDCoprime : ∀ i < k, D.Coprime (p i) := fun i hi =>
    ((hPrime i hi).coprime_iff_not_dvd.mpr (hAvoidD i hi)).symm
  obtain ⟨a, b, hFirst, hLast, hVertices⟩ :=
    exists_path_vertex_choices k D p hk hD hPrime hDCoprime hBound
  have hEdges : ∀ i : ℕ, ∃ v : ℕ, i < k - 1 →
      0 < v ∧ v < 4 * k * p i * p (i + 1) ∧ (∀ j < k, ¬p j ∣ v) ∧
      (((p (i + 1) * v : ℕ) : ZMod (p i))⁻¹) = (b i : ZMod (p i)) ∧
      (((p i * v : ℕ) : ZMod (p (i + 1)))⁻¹) = (a (i + 1) : ZMod (p (i + 1))) := by
    intro i
    by_cases hi : i < k - 1
    · have hiVertex : i < k := by omega
      have hiNext : i + 1 < k := by omega
      have hpP : p i ∈ P := Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hiVertex, rfl⟩
      have hqP : p (i + 1) ∈ P := Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr hiNext, rfl⟩
      have hDistinct : p i ≠ p (i + 1) := by
        intro hEqual
        have h := hInjective i hiVertex (i + 1) hiNext hEqual
        omega
      obtain ⟨v, hvPos, hvBound, hvAvoid, hvOut, hvIn⟩ :=
        exists_prime_set_connector P (p i) (p (i + 1)) hPPrime hpP hqP hDistinct (b i) (a (i + 1)) hPMass
      refine ⟨v, fun _ => ⟨hvPos, hvBound.trans_le ?_, ?_, hvOut, hvIn⟩⟩
      · have h := Nat.mul_le_mul_right (p i * p (i + 1)) (Nat.mul_le_mul_left 4 hPCard)
        simpa only [mul_assoc] using h
      · intro j hj
        exact hvAvoid (p j) (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)
    · exact ⟨1, fun hValid => (hi hValid).elim⟩
  choose u hu using hEdges
  have hUPositive : ∀ i < k - 1, 0 < u i := fun i hi => (hu i hi).1
  have hAvoidU : ∀ i < k - 1, ∀ j < k, ¬p j ∣ u i := fun i hi => (hu i hi).2.2.1
  have hOutgoing : ∀ i < k - 1,
      (((p (i + 1) * u i : ℕ) : ZMod (p i))⁻¹) = (b i : ZMod (p i)) :=
    fun i hi => (hu i hi).2.2.2.1
  have hIncoming : ∀ i < k - 1,
      (((p i * u i : ℕ) : ZMod (p (i + 1)))⁻¹) = (a (i + 1) : ZMod (p (i + 1))) :=
    fun i hi => (hu i hi).2.2.2.2
  refine ⟨u, ?_, ?_⟩
  · intro i hi
    exact ⟨(hu i hi).1, (hu i hi).2.1, (hu i hi).2.2.1⟩
  · exact pathSupport_minimalCore k D p u a b hk hD hPrime hInjective hAvoidD hUPositive hAvoidU
      hBound (hFirst 0 (by omega) rfl) hLast
      (fun i hPos hInterior => (hVertices i hPos hInterior).1)
      (fun i hPos hInterior => (hVertices i hPos hInterior).2) hOutgoing hIncoming

end Erdos319Sharp
