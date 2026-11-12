import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed-sign primitive reciprocal relations

The extremum ranges over all subsets of the integer interval. The same
signing is used for the total and every proper-subset test.
-/

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def reciprocalSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (n : ℚ)⁻¹

def signedSum (A : Finset ℕ) (δ : ℕ → ℤˣ) : ℚ :=
  ∑ n ∈ A, (δ n : ℚ) / n

def IsPrimitiveSigning (A : Finset ℕ) (δ : ℕ → ℤˣ) : Prop :=
  signedSum A δ = 0 ∧
    ∀ T ⊆ A, signedSum T δ = 0 → T = ∅ ∨ T = A

def Primitive (A : Finset ℕ) : Prop :=
  ∃ δ : ℕ → ℤˣ, IsPrimitiveSigning A δ

def maxSize (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter Primitive).sup Finset.card

def AgreeOn (A : Finset ℕ) (δ ε : ℕ → ℤˣ) : Prop :=
  ∀ n ∈ A, δ n = ε n

def reverseSigning (δ : ℕ → ℤˣ) : ℕ → ℤˣ :=
  fun n => -δ n

def switchSigning (T : Finset ℕ) (δ : ℕ → ℤˣ) : ℕ → ℤˣ :=
  fun n => if n ∈ T then -δ n else δ n

def differenceSet (A : Finset ℕ) (δ ε : ℕ → ℤˣ) : Finset ℕ :=
  A.filter (fun n => δ n ≠ ε n)

def positivePart (A : Finset ℕ) (δ : ℕ → ℤˣ) : Finset ℕ :=
  A.filter (fun n => δ n = 1)

def negativePart (A : Finset ℕ) (δ : ℕ → ℤˣ) : Finset ℕ :=
  A.filter (fun n => δ n = -1)

theorem unit_eq_or_eq_neg (x y : ℤˣ) : x = y ∨ x = -y := by
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    rcases Int.units_eq_one_or y with rfl | rfl <;> simp

theorem unit_ne_neg_self (x : ℤˣ) : x ≠ -x := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> decide

theorem signedSum_congr {A : Finset ℕ} {δ ε : ℕ → ℤˣ}
    (h : AgreeOn A δ ε) : signedSum A δ = signedSum A ε := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n hn]

theorem signedSum_reverse (A : Finset ℕ) (δ : ℕ → ℤˣ) :
    signedSum A (reverseSigning δ) = -signedSum A δ := by
  simp [signedSum, reverseSigning, neg_div]

theorem reversal_distinct_on_nonempty {A : Finset ℕ} (hA : A.Nonempty)
    (δ : ℕ → ℤˣ) : ¬AgreeOn A δ (reverseSigning δ) := by
  intro heq
  obtain ⟨n, hn⟩ := hA
  exact unit_ne_neg_self (δ n) (heq n hn)

theorem signedSum_partition (A : Finset ℕ) (δ : ℕ → ℤˣ) :
    signedSum A δ = reciprocalSum (positivePart A δ) -
      reciprocalSum (negativePart A δ) := by
  unfold reciprocalSum positivePart negativePart
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hunit : (1 : ℤˣ) ≠ -1 := unit_ne_neg_self 1
  rcases Int.units_eq_one_or (δ n) with h | h <;>
    simp [h, div_eq_mul_inv, hunit, Ne.symm hunit]

theorem positivePart_union_negativePart (A : Finset ℕ) (δ : ℕ → ℤˣ) :
    positivePart A δ ∪ negativePart A δ = A := by
  ext n
  simp only [positivePart, negativePart, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  · intro hn
    rcases Int.units_eq_one_or (δ n) with h | h
    · exact Or.inl ⟨hn, h⟩
    · exact Or.inr ⟨hn, h⟩

theorem balanced_parts_equal {A : Finset ℕ} {δ : ℕ → ℤˣ}
    (h : signedSum A δ = 0) :
    reciprocalSum (positivePart A δ) = reciprocalSum (negativePart A δ) := by
  exact sub_eq_zero.mp ((signedSum_partition A δ).symm.trans h)

theorem isPrimitiveSigning_reverse {A : Finset ℕ} {δ : ℕ → ℤˣ}
    (h : IsPrimitiveSigning A δ) : IsPrimitiveSigning A (reverseSigning δ) := by
  constructor
  · rw [signedSum_reverse, h.1, neg_zero]
  · intro T hTA hzero
    apply h.2 T hTA
    simpa only [signedSum_reverse, neg_eq_zero] using hzero

theorem signedSum_switch {A T : Finset ℕ} (hT : T ⊆ A) (δ : ℕ → ℤˣ) :
    signedSum A (switchSigning T δ) = signedSum A δ - 2 * signedSum T δ := by
  have hfilter : A.filter (fun n => n ∈ T) = T := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hn => ⟨hT hn, hn⟩⟩
  calc
    signedSum A (switchSigning T δ) =
        ∑ n ∈ A, ((δ n : ℚ) / n - 2 * (if n ∈ T then (δ n : ℚ) / n else 0)) := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n ∈ T
      · simp [switchSigning, hn, neg_div]
        ring
      · simp [switchSigning, hn]
    _ = signedSum A δ - 2 * signedSum T δ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter, hfilter]
      rfl

theorem switch_difference_agrees (A : Finset ℕ) (δ ε : ℕ → ℤˣ) :
    AgreeOn A (switchSigning (differenceSet A δ ε) δ) ε := by
  intro n hn
  by_cases hne : δ n ≠ ε n
  · have hm : n ∈ differenceSet A δ ε := Finset.mem_filter.mpr ⟨hn, hne⟩
    rcases unit_eq_or_eq_neg (ε n) (δ n) with heq | heq
    · exact (hne heq.symm).elim
    · simpa [switchSigning, hm] using heq.symm
  · have hm : n ∉ differenceSet A δ ε := by simp [differenceSet, hne]
    simpa [switchSigning, hm] using not_ne_iff.mp hne

/-- A primitive signing has exactly its reversal pair on the fixed support. -/
theorem primitive_iff_unique_reversal_pair (A : Finset ℕ) :
    Primitive A ↔ ∃ δ : ℕ → ℤˣ, signedSum A δ = 0 ∧
      ∀ ε : ℕ → ℤˣ, signedSum A ε = 0 →
        AgreeOn A ε δ ∨ AgreeOn A ε (reverseSigning δ) := by
  constructor
  · rintro ⟨δ, hzero, hprimitive⟩
    refine ⟨δ, hzero, ?_⟩
    intro ε hε
    let T := differenceSet A δ ε
    have hTA : T ⊆ A := Finset.filter_subset _ _
    have hagree := switch_difference_agrees A δ ε
    have hswitch := signedSum_switch hTA δ
    have hsame : signedSum A (switchSigning T δ) = 0 :=
      (signedSum_congr hagree).trans hε
    have hTzero : signedSum T δ = 0 := by linarith
    rcases hprimitive T hTA hTzero with hEmpty | hFull
    · left
      intro n hn
      have hnot : n ∉ T := by rw [hEmpty]; simp
      have heq : δ n = ε n := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
      exact heq.symm
    · right
      intro n hn
      have hm : n ∈ T := by rw [hFull]; exact hn
      change n ∈ differenceSet A δ ε at hm
      have heq := hagree n hn
      simpa [switchSigning, hm, reverseSigning] using heq.symm
  · rintro ⟨δ, hzero, hpair⟩
    refine ⟨δ, hzero, ?_⟩
    intro T hTA hTzero
    have hswitch : signedSum A (switchSigning T δ) = 0 := by
      rw [signedSum_switch hTA δ, hzero, hTzero]
      ring
    rcases hpair (switchSigning T δ) hswitch with hagree | hagree
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have heq := hagree n (hTA hn)
      have hneg : -δ n = δ n := by simpa [switchSigning, hn] using heq
      exact unit_ne_neg_self (δ n) hneg.symm
    · right
      apply Finset.Subset.antisymm hTA
      intro n hn
      by_contra hnot
      have heq := hagree n hn
      have hneg : δ n = -δ n := by
        simpa [switchSigning, hnot, reverseSigning] using heq
      exact unit_ne_neg_self (δ n) hneg

theorem primitive_empty : Primitive ∅ := by
  refine ⟨fun _ => 1, ?_⟩
  constructor
  · simp [signedSum]
  · intro T hT _
    exact Or.inl (Finset.subset_empty.mp hT)

theorem card_le_maxSize {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hP : Primitive A) : A.card ≤ maxSize N := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hP⟩)

theorem maxSize_le (N : ℕ) : maxSize N ≤ N := by
  classical
  apply Finset.sup_le
  intro A hA
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  simpa using Finset.card_le_card hsub

theorem maxSize_attained (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Primitive A ∧ A.card = maxSize N := by
  classical
  have hne : ((Finset.Icc 1 N).powerset.filter Primitive).Nonempty := by
    exact ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      primitive_empty⟩⟩
  obtain ⟨A, hA, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨A, Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1,
    (Finset.mem_filter.mp hA).2, hcard.symm⟩

theorem maxSize_mono : Monotone maxSize := by
  intro M N hMN
  obtain ⟨A, hA, hP, hcard⟩ := maxSize_attained M
  rw [← hcard]
  apply card_le_maxSize _ hP
  intro n hn
  rcases Finset.mem_Icc.mp (hA hn) with ⟨hlo, hhi⟩
  exact Finset.mem_Icc.mpr ⟨hlo, hhi.trans hMN⟩

end Erdos319Sharp
