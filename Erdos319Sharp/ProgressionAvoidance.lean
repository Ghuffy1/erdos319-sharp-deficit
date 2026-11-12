import Erdos319Sharp.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

open Finset

namespace Erdos319Sharp

theorem progression_divisibility_count (p q r T : ℕ) (hp : 0 < p) (hCop : p.Coprime q) :
    ((Finset.range T).filter (fun j => p ∣ r + q * j)).card ≤ T / p + 1 := by
  classical
  let A := (Finset.range T).filter (fun j => p ∣ r + q * j)
  have hBound : A.card ≤ (Finset.range (T / p + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun j => j / p)
    · intro j hj
      have hjT := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      apply Finset.mem_range.mpr
      change j / p < T / p + 1
      have := Nat.div_le_div_right (c := p) hjT.le
      omega
    · intro i hi j hj hQuotient
      have hiDiv := (Finset.mem_filter.mp hi).2
      have hjDiv := (Finset.mem_filter.mp hj).2
      change i / p = j / p at hQuotient
      have hiMod : r + q * i ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hiDiv
      have hjMod : r + q * j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hjDiv
      have hRemainder : i % p = j % p :=
        Nat.ModEq.cancel_left_of_coprime hCop
          (Nat.ModEq.add_left_cancel' r (hiMod.trans hjMod.symm))
      calc
        i = i % p + p * (i / p) := (Nat.mod_add_div i p).symm
        _ = j % p + p * (j / p) := by rw [hRemainder, hQuotient]
        _ = j := Nat.mod_add_div j p
  simpa only [Finset.card_range] using hBound

theorem exists_avoiding_progression_index_of_mass (P : Finset ℕ) (q r T : ℕ)
    (hPositive : ∀ p ∈ P, 0 < p) (hCoprime : ∀ p ∈ P, p.Coprime q)
    (hMass : (T : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + P.card < T) :
    ∃ j : ℕ, j < T ∧ ∀ p ∈ P, ¬ p ∣ r + q * j := by
  classical
  let B := P.biUnion (fun p => (Finset.range T).filter (fun j => p ∣ r + q * j))
  have hCount : B.card ≤ ∑ p ∈ P, (T / p + 1) := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun p hp => progression_divisibility_count p q r T
      (hPositive p hp) (hCoprime p hp))
  have hCast : (B.card : ℝ) ≤ ((∑ p ∈ P, (T / p + 1) : ℕ) : ℝ) := by
    exact_mod_cast hCount
  push_cast at hCast
  have hCountReal : (B.card : ℝ) ≤ (T : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + P.card := by
    calc
      (B.card : ℝ) ≤ ∑ p ∈ P, (((T / p : ℕ) : ℝ) + 1) := hCast
      _ ≤ ∑ p ∈ P, ((T : ℝ) / p + 1) := Finset.sum_le_sum (fun p hp => by
        have hDiv : ((T / p : ℕ) : ℝ) ≤ (T : ℝ) / p := Nat.cast_div_le
        linarith)
      _ = _ := by simp [Finset.mul_sum, Finset.sum_add_distrib, div_eq_mul_inv]
  have hStrict : B.card < (Finset.range T).card := by
    rw [Finset.card_range]
    exact_mod_cast hCountReal.trans_lt hMass
  obtain ⟨j, hjRange, hjB⟩ := Finset.exists_mem_notMem_of_card_lt_card hStrict
  refine ⟨j, Finset.mem_range.mp hjRange, ?_⟩
  intro p hp hDiv
  exact hjB (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hjRange, hDiv⟩⟩)

theorem exists_avoiding_progression_index (P : Finset ℕ) (q r : ℕ)
    (hPositive : ∀ p ∈ P, 0 < p) (hCoprime : ∀ p ∈ P, p.Coprime q)
    (hMass : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1 / 2) :
    ∃ j : ℕ, j < 4 * (P.card + 1) ∧ ∀ p ∈ P, ¬ p ∣ r + q * j := by
  apply exists_avoiding_progression_index_of_mass P q r (4 * (P.card + 1)) hPositive hCoprime
  push_cast
  have hCard : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  nlinarith

end Erdos319Sharp
