import Erdos319Sharp.ProgressionAvoidance

set_option autoImplicit false

open Finset

namespace Erdos319Sharp

theorem bounded_crt_avoiding_set (p q a b : ℕ) (P : Finset ℕ)
    (hp : 2 ≤ p) (hq : 0 < q) (hpq : p.Coprime q)
    (ha : a.Coprime p) (hb : b.Coprime q)
    (hPositive : ∀ s ∈ P, 0 < s) (hCoprime : ∀ s ∈ P, s.Coprime (p * q))
    (hMass : (∑ s ∈ P, 1 / (s : ℝ)) ≤ 1 / 2) :
    ∃ u : ℕ, 0 < u ∧ u < 4 * (P.card + 1) * (p * q) ∧
      u ≡ a [MOD p] ∧ u ≡ b [MOD q] ∧ u.Coprime (p * q) ∧
      ∀ s ∈ P, ¬ s ∣ u := by
  let base := Nat.chineseRemainder hpq a b
  have hpPos : 0 < p := by omega
  have hBaseBound : (base : ℕ) < p * q :=
    Nat.chineseRemainder_lt_mul hpq a b hpPos.ne' hq.ne'
  have hBaseCop : (base : ℕ).Coprime p := base.property.1.gcd_eq.trans ha
  have hBasePos : 0 < (base : ℕ) := by
    by_contra hNonpos
    have hZero : (base : ℕ) = 0 := by omega
    have hpOne : p = 1 := by simpa only [hZero, Nat.coprime_zero_left] using hBaseCop
    omega
  obtain ⟨j, hj, hAvoid⟩ := exists_avoiding_progression_index P (p * q) base
    hPositive hCoprime hMass
  let u := (base : ℕ) + (p * q) * j
  have huPos : 0 < u := by dsimp [u]; omega
  have huBound : u < 4 * (P.card + 1) * (p * q) := by
    calc
      u < p * q + (p * q) * j := Nat.add_lt_add_right hBaseBound _
      _ = (p * q) * (j + 1) := by ring
      _ ≤ (p * q) * (4 * (P.card + 1)) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hj)
      _ = _ := by ring
  have hShiftP : (p * q) * j ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr ⟨q * j, by ring⟩
  have hShiftQ : (p * q) * j ≡ 0 [MOD q] :=
    Nat.modEq_zero_iff_dvd.mpr ⟨p * j, by ring⟩
  have huModP : u ≡ a [MOD p] := by
    simpa only [u, Nat.add_zero] using base.property.1.add hShiftP
  have huModQ : u ≡ b [MOD q] := by
    simpa only [u, Nat.add_zero] using base.property.2.add hShiftQ
  have huCopP : u.Coprime p := huModP.gcd_eq.trans ha
  have huCopQ : u.Coprime q := huModQ.gcd_eq.trans hb
  exact ⟨u, huPos, huBound, huModP, huModQ, huCopP.mul_right huCopQ, hAvoid⟩

end Erdos319Sharp
