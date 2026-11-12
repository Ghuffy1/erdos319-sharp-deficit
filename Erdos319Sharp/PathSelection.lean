import Erdos319Sharp.PathSupport

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def pathBlockSelection (D : ℕ) (p : ℕ → ℕ) (i : ℕ) (C : Finset ℕ) : Finset ℕ :=
  D.divisors.filter (fun b => p i * b ∈ C)

def pathEdgeSelection (k : ℕ) (p u : ℕ → ℕ) (C : Finset ℕ) : Finset ℕ :=
  (Finset.range (k - 1)).filter (fun i => pathEdge p u i ∈ C)

theorem pathBlockSelection_image (D : ℕ) (p : ℕ → ℕ) (i : ℕ) (C : Finset ℕ) :
    (pathBlockSelection D p i C).image (fun b => p i * b) = pathBlock D p i ∩ C := by
  classical
  simpa only [pathBlockSelection, pathBlock, Finset.filter_mem_eq_inter] using
    (Finset.filter_image (s := D.divisors) (f := fun b : ℕ => p i * b)
      (p := fun n : ℕ => n ∈ C)).symm

theorem pathEdgeSelection_image (k : ℕ) (p u : ℕ → ℕ) (C : Finset ℕ) :
    (pathEdgeSelection k p u C).image (pathEdge p u) = pathEdges k p u ∩ C := by
  classical
  simpa only [pathEdgeSelection, pathEdges, Finset.filter_mem_eq_inter] using
    (Finset.filter_image (s := Finset.range (k - 1)) (f := pathEdge p u)
      (p := fun n : ℕ => n ∈ C)).symm

theorem path_subset_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (k D : ℕ) (p u : ℕ → ℕ) (C : Finset ℕ)
    (hPrime : ∀ i < k, (p i).Prime)
    (hInjective : ∀ i < k, ∀ j < k, p i = p j → i = j)
    (hAvoidD : ∀ i < k, ¬ p i ∣ D)
    (hAvoidU : ∀ i < k - 1, ∀ j < k, ¬ p j ∣ u i)
    (hC : C ⊆ pathSupport k D p u) :
    (∑ n ∈ C, f n) =
      (∑ i ∈ Finset.range k, ∑ b ∈ pathBlockSelection D p i C, f (p i * b)) +
        ∑ i ∈ pathEdgeSelection k p u C, f (pathEdge p u i) := by
  classical
  have hDisjoint : Disjoint (pathBlocks k D p ∩ C) (pathEdges k p u ∩ C) :=
    (pathBlocks_disjoint_pathEdges k D p u hPrime hInjective hAvoidD hAvoidU).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hCover : (pathBlocks k D p ∩ C) ∪ (pathEdges k p u ∩ C) = C := by
    rw [← Finset.union_inter_distrib_right]
    exact Finset.inter_eq_right.mpr hC
  have hBlocks : (∑ n ∈ pathBlocks k D p ∩ C, f n) =
      ∑ i ∈ Finset.range k, ∑ b ∈ pathBlockSelection D p i C, f (p i * b) := by
    have hPair : Set.Pairwise (Finset.range k)
        (fun i j => Disjoint (pathBlock D p i ∩ C) (pathBlock D p j ∩ C)) := by
      intro i hi j hj hij
      exact (pathBlocks_pairwise_disjoint k D p hPrime hInjective hAvoidD hi hj hij).mono
        Finset.inter_subset_left Finset.inter_subset_left
    rw [pathBlocks, Finset.biUnion_inter, Finset.sum_biUnion hPair]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← pathBlockSelection_image D p i C]
    exact Finset.sum_image (fun b _ c _ hEqual =>
      Nat.eq_of_mul_eq_mul_left (hPrime i (Finset.mem_range.mp hi)).pos hEqual)
  have hEdges : (∑ n ∈ pathEdges k p u ∩ C, f n) =
      ∑ i ∈ pathEdgeSelection k p u C, f (pathEdge p u i) := by
    rw [← pathEdgeSelection_image k p u C]
    apply Finset.sum_image
    intro i hi j hj hEqual
    exact pathEdge_injective k p u hPrime hInjective hAvoidU
      (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hEqual
  calc
    (∑ n ∈ C, f n) = (∑ n ∈ pathBlocks k D p ∩ C, f n) +
        ∑ n ∈ pathEdges k p u ∩ C, f n := by rw [← Finset.sum_union hDisjoint, hCover]
    _ = _ := by rw [hBlocks, hEdges]

end Erdos319Sharp
