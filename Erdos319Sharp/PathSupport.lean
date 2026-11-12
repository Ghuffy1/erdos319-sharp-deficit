import Erdos319Sharp.PairConnector
import Mathlib.NumberTheory.Divisors

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def pathBlock (D : ℕ) (p : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  D.divisors.image (fun b => p i * b)

def pathEdge (p u : ℕ → ℕ) (i : ℕ) : ℕ := p i * p (i + 1) * u i

def pathBlocks (k D : ℕ) (p : ℕ → ℕ) : Finset ℕ :=
  (Finset.range k).biUnion (pathBlock D p)

def pathEdges (k : ℕ) (p u : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (k - 1)).image (pathEdge p u)

def pathSupport (k D : ℕ) (p u : ℕ → ℕ) : Finset ℕ :=
  pathBlocks k D p ∪ pathEdges k p u

theorem marked_prime_dvd_block (k D : ℕ) (p : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ i < k, ¬ p i ∣ D)
    {i j b : ℕ} (hi : i < k) (hj : j < k) (hb : b ∈ D.divisors) :
    p j ∣ p i * b ↔ j = i := by
  constructor
  · intro hDiv
    rcases (hPrime j hj).dvd_mul.mp hDiv with hFirst | hSecond
    · exact hInjective j hj i hi ((Nat.prime_dvd_prime_iff_eq (hPrime j hj) (hPrime i hi)).mp hFirst)
    · exact (hAvoid j hj (hSecond.trans (Nat.dvd_of_mem_divisors hb))).elim
  · rintro rfl
    exact dvd_mul_right _ _

theorem marked_prime_dvd_edge (k : ℕ) (p u : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ i < k - 1, ∀ j < k, ¬ p j ∣ u i)
    {i j : ℕ} (hi : i < k - 1) (hj : j < k) :
    p j ∣ pathEdge p u i ↔ j = i ∨ j = i + 1 := by
  have hiVertex : i < k := by omega
  have hiNext : i + 1 < k := by omega
  constructor
  · intro hDiv
    rcases (hPrime j hj).dvd_mul.mp hDiv with hPair | hLast
    · rcases (hPrime j hj).dvd_mul.mp hPair with hLeft | hRight
      · exact Or.inl (hInjective j hj i hiVertex
          ((Nat.prime_dvd_prime_iff_eq (hPrime j hj) (hPrime i hiVertex)).mp hLeft))
      · exact Or.inr (hInjective j hj (i + 1) hiNext
          ((Nat.prime_dvd_prime_iff_eq (hPrime j hj) (hPrime (i + 1) hiNext)).mp hRight))
    · exact (hAvoid i hi j hj hLast).elim
  · intro hIndex
    rcases hIndex with hIndex | hIndex
    · subst j
      exact (dvd_mul_right (p i) (p (i + 1))).trans (dvd_mul_right (p i * p (i + 1)) (u i))
    · rw [hIndex]
      exact (dvd_mul_left (p (i + 1)) (p i)).trans (dvd_mul_right (p i * p (i + 1)) (u i))

theorem pathEdge_injective (k : ℕ) (p u : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ i < k - 1, ∀ j < k, ¬ p j ∣ u i) :
    Set.InjOn (pathEdge p u) (Finset.range (k - 1)) := by
  intro i hi j hj hEqual
  have hiEdge := Finset.mem_range.mp hi
  have hjEdge := Finset.mem_range.mp hj
  have hiVertex : i < k := by omega
  have hiNext : i + 1 < k := by omega
  have hLeft : p i ∣ pathEdge p u j := by
    rw [← hEqual]
    exact (marked_prime_dvd_edge k p u hPrime hInjective hAvoid hiEdge hiVertex).mpr (Or.inl rfl)
  have hRight : p (i + 1) ∣ pathEdge p u j := by
    rw [← hEqual]
    exact (marked_prime_dvd_edge k p u hPrime hInjective hAvoid hiEdge hiNext).mpr (Or.inr rfl)
  have hFirst := (marked_prime_dvd_edge k p u hPrime hInjective hAvoid hjEdge hiVertex).mp hLeft
  have hSecond := (marked_prime_dvd_edge k p u hPrime hInjective hAvoid hjEdge hiNext).mp hRight
  omega

theorem pathBlocks_pairwise_disjoint (k D : ℕ) (p : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoid : ∀ i < k, ¬ p i ∣ D) :
    Set.Pairwise (Finset.range k) (fun i j => Disjoint (pathBlock D p i) (pathBlock D p j)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hni
  obtain ⟨c, hc, hEqual⟩ := Finset.mem_image.mp hnj
  have hDiv : p i ∣ p j * c := by rw [hEqual]; exact dvd_mul_right _ _
  have hEq := (marked_prime_dvd_block k D p hPrime hInjective hAvoid
    (Finset.mem_range.mp hj) (Finset.mem_range.mp hi) hc).mp hDiv
  exact hij hEq

theorem pathBlocks_disjoint_pathEdges (k D : ℕ) (p u : ℕ → ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬ p i ∣ D)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬ p j ∣ u i) :
    Disjoint (pathBlocks k D p) (pathEdges k p u) := by
  apply Finset.disjoint_left.mpr
  intro n hnBlock hnEdge
  obtain ⟨i, hi, hBlock⟩ := Finset.mem_biUnion.mp hnBlock
  obtain ⟨b, hb, hBlockEq⟩ := Finset.mem_image.mp hBlock
  obtain ⟨j, hj, hEdgeEq⟩ := Finset.mem_image.mp hnEdge
  have hiVertex := Finset.mem_range.mp hi
  have hjEdge := Finset.mem_range.mp hj
  have hjVertex : j < k := by omega
  have hjNext : j + 1 < k := by omega
  have hLeft : p j ∣ p i * b := by
    rw [hBlockEq, ← hEdgeEq]
    exact (marked_prime_dvd_edge k p u hPrime hInjective hAvoidU hjEdge hjVertex).mpr (Or.inl rfl)
  have hRight : p (j + 1) ∣ p i * b := by
    rw [hBlockEq, ← hEdgeEq]
    exact (marked_prime_dvd_edge k p u hPrime hInjective hAvoidU hjEdge hjNext).mpr (Or.inr rfl)
  have hFirst := (marked_prime_dvd_block k D p hPrime hInjective hAvoidD hiVertex hjVertex hb).mp hLeft
  have hSecond := (marked_prime_dvd_block k D p hPrime hInjective hAvoidD hiVertex hjNext hb).mp hRight
  omega

end Erdos319Sharp
