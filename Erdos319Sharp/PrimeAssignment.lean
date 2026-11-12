import Erdos319Sharp.MinorityAlgebra
import Erdos319Sharp.PrimeAvoidance

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

def primeExceptions (A P : Finset ℕ) : Finset ℕ :=
  P.biUnion (fun p => A.filter (fun n => p ∣ n))

def primeAssignmentError (P Q : Finset ℕ) (b : ℝ) : ℝ :=
  ((P.card + Q.card : ℕ) : ℝ) * b + 3 * ((P ∪ Q).prod id : ℕ)

theorem mem_primeExceptions {A P : Finset ℕ} {n : ℕ} :
    n ∈ primeExceptions A P ↔ n ∈ A ∧ ∃ p ∈ P, p ∣ n := by
  constructor
  · intro h
    obtain ⟨p, hp, hn⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hnA, hpn⟩ := Finset.mem_filter.mp hn
    exact ⟨hnA, p, hp, hpn⟩
  · rintro ⟨hnA, p, hp, hpn⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hnA, hpn⟩⟩

theorem primeExceptions_card_bound (A P : Finset ℕ) (b : ℝ)
    (hRare : ∀ p ∈ P, ((A.filter (fun n => p ∣ n)).card : ℝ) ≤ b) :
    ((primeExceptions A P).card : ℝ) ≤ (P.card : ℝ) * b := by
  have hNat : (primeExceptions A P).card ≤ ∑ p ∈ P, (A.filter (fun n => p ∣ n)).card :=
    Finset.card_biUnion_le
  calc
    ((primeExceptions A P).card : ℝ) ≤ ∑ p ∈ P, ((A.filter (fun n => p ∣ n)).card : ℝ) := by
      exact_mod_cast hNat
    _ ≤ ∑ _p ∈ P, b := Finset.sum_le_sum hRare
    _ = (P.card : ℝ) * b := by simp

theorem card_le_primeAvoiders_add_exceptions (A P : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    (A.card : ℝ) ≤ (primeAvoiders P N).card + (primeExceptions A P).card := by
  classical
  have hSub : A ⊆ primeAvoiders P N ∪ primeExceptions A P := by
    intro n hn
    by_cases h : ∀ p ∈ P, ¬ p ∣ n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hA hn, h⟩)
    · push_neg at h
      exact Finset.mem_union_right _ (mem_primeExceptions.mpr ⟨hn, h⟩)
  exact_mod_cast (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)

theorem primeHitBoth_card_le_omissions (X Y P Q : Finset ℕ) (N : ℕ) :
    ((primeHitBoth P Q N).card : ℝ) ≤
      (Finset.Icc 1 N \ (X ∪ Y)).card + (primeExceptions X Q).card + (primeExceptions Y P).card := by
  classical
  have hSub : primeHitBoth P Q N ⊆
      (Finset.Icc 1 N \ (X ∪ Y)) ∪ (primeExceptions X Q ∪ primeExceptions Y P) := by
    intro n hn
    obtain ⟨hnI, hp, hq⟩ := mem_primeHitBoth.mp hn
    by_cases hnX : n ∈ X
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (mem_primeExceptions.mpr ⟨hnX, hq⟩))
    by_cases hnY : n ∈ Y
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (mem_primeExceptions.mpr ⟨hnY, hp⟩))
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨hnI, fun h => (Finset.mem_union.mp h).elim hnX hnY⟩)
  have hCount : (primeHitBoth P Q N).card ≤
      (Finset.Icc 1 N \ (X ∪ Y)).card + (primeExceptions X Q).card + (primeExceptions Y P).card := by
    have hOne := Finset.card_union_le (Finset.Icc 1 N \ (X ∪ Y))
      (primeExceptions X Q ∪ primeExceptions Y P)
    have hTwo := Finset.card_union_le (primeExceptions X Q) (primeExceptions Y P)
    have hCover := Finset.card_le_card hSub
    omega
  exact_mod_cast hCount

theorem minority_bound_of_prime_assignment (X Y P Q : Finset ℕ) (N : ℕ) (b : ℝ)
    (hX : X ⊆ Finset.Icc 1 N) (hY : Y ⊆ Finset.Icc 1 N)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint P Q)
    (hb : 0 ≤ b) (hR : primeAvoidanceDensity (P ∪ Q) < 1)
    (hRareP : ∀ p ∈ P, ((Y.filter (fun n => p ∣ n)).card : ℝ) ≤ b)
    (hRareQ : ∀ p ∈ Q, ((X.filter (fun n => p ∣ n)).card : ℝ) ≤ b) :
    min (X.card : ℝ) (Y.card : ℝ) ≤ (N : ℝ) * primeAvoidanceDensity (P ∪ Q) +
      (Real.sqrt (primeAvoidanceDensity (P ∪ Q)) / (1 - Real.sqrt (primeAvoidanceDensity (P ∪ Q)))) *
        ((Finset.Icc 1 N \ (X ∪ Y)).card + primeAssignmentError P Q b) + primeAssignmentError P Q b := by
  let E : ℝ := ((P.card + Q.card : ℕ) : ℝ) * b
  let D : ℝ := ((P ∪ Q).prod id : ℕ)
  have hExX := primeExceptions_card_bound X Q b hRareQ
  have hExY := primeExceptions_card_bound Y P b hRareP
  have hExTotal : ((primeExceptions X Q).card : ℝ) + (primeExceptions Y P).card ≤ E := by
    dsimp [E]
    push_cast
    nlinarith only [hExX, hExY]
  have hExX0 : (0 : ℝ) ≤ (primeExceptions X Q).card := Nat.cast_nonneg _
  have hExY0 : (0 : ℝ) ≤ (primeExceptions Y P).card := Nat.cast_nonneg _
  have hE : 0 ≤ E := mul_nonneg (Nat.cast_nonneg _) hb
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hProdP : 0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hProdQ : 0 < Q.prod id := Finset.prod_pos (fun p hp => (hQ p hp).pos)
  have hPeriod : (P ∪ Q).prod id = P.prod id * Q.prod id := Finset.prod_union hPQ
  have hDP : ((P.prod id : ℕ) : ℝ) ≤ D := by
    dsimp [D]
    exact_mod_cast (show P.prod id ≤ (P ∪ Q).prod id by
      rw [hPeriod]
      exact Nat.le_mul_of_pos_right _ hProdQ)
  have hDQ : ((Q.prod id : ℕ) : ℝ) ≤ D := by
    dsimp [D]
    exact_mod_cast (show Q.prod id ≤ (P ∪ Q).prod id by
      rw [hPeriod, Nat.mul_comm]
      exact Nat.le_mul_of_pos_right _ hProdP)
  have hXCard : (X.card : ℝ) ≤ (N : ℝ) * primeAvoidanceDensity Q + (E + 3 * D) := by
    have h := card_le_primeAvoiders_add_exceptions X Q N hX
    have hAvoid := (abs_le.mp (primeAvoiders_card_error Q N hQ)).2
    nlinarith only [h, hAvoid, hDQ, hExTotal, hExY0, hD]
  have hYCard : (Y.card : ℝ) ≤ (N : ℝ) * primeAvoidanceDensity P + (E + 3 * D) := by
    have h := card_le_primeAvoiders_add_exceptions Y P N hY
    have hAvoid := (abs_le.mp (primeAvoiders_card_error P N hP)).2
    nlinarith only [h, hAvoid, hDP, hExTotal, hExX0, hD]
  have hMixed : (N : ℝ) * (1 - primeAvoidanceDensity P) * (1 - primeAvoidanceDensity Q) ≤
      (Finset.Icc 1 N \ (X ∪ Y)).card + (E + 3 * D) := by
    have hLower := primeHitBoth_card_lower P Q N hP hQ hPQ
    have hUpper := primeHitBoth_card_le_omissions X Y P Q N
    change (N : ℝ) * (1 - primeAvoidanceDensity P) * (1 - primeAvoidanceDensity Q) ≤
      (primeHitBoth P Q N).card + 3 * D at hLower
    nlinarith only [hLower, hUpper, hExTotal]
  have hR' : primeAvoidanceDensity P * primeAvoidanceDensity Q < 1 := by
    rwa [primeAvoidanceDensity_union P Q hPQ] at hR
  have h := minority_minimum_bound N (primeAvoidanceDensity P) (primeAvoidanceDensity Q)
    ((Finset.Icc 1 N \ (X ∪ Y)).card) (E + 3 * D) X.card Y.card
    (primeAvoidanceDensity_pos_le_one P hP).1.le (primeAvoidanceDensity_pos_le_one Q hQ).1.le hR'
    (by positivity) hXCard hYCard hMixed
  simpa only [primeAvoidanceDensity_union P Q hPQ, primeAssignmentError, E, D] using h

end Erdos319Sharp
