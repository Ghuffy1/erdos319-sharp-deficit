import Erdos319Sharp.DyadicMass
import Erdos319Sharp.RankinTail

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem card_le_of_dyadic_density (δ : ℝ) (hδ : 0 ≤ δ) (N : ℕ)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hDensity : ∀ (M : ℕ) (B : Finset ℕ), B ⊆ A → B ⊆ Finset.Ioc (M / 2) M →
      (B.card : ℝ) ≤ δ * M) :
    (A.card : ℝ) ≤ 2 * δ * N := by
  classical
  induction N using Nat.strong_induction_on generalizing A with
  | h N ih =>
    by_cases hN : N = 0
    · subst N
      have hEmpty : A = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro n hn
        have := Finset.mem_Icc.mp (hA hn)
        omega)
      simp [hEmpty]
    · let B := A.filter (fun n => n ≤ N / 2)
      let C := A.filter (fun n => ¬ n ≤ N / 2)
      have hBA : B ⊆ A := Finset.filter_subset _ _
      have hCA : C ⊆ A := Finset.filter_subset _ _
      have hBPrefix : B ⊆ Finset.Icc 1 (N / 2) := by
        intro n hn
        obtain ⟨hnA, hnB⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hA hnA)).1, hnB⟩
      have hCTail : C ⊆ Finset.Ioc (N / 2) N := by
        intro n hn
        obtain ⟨hnA, hnC⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnC, (Finset.mem_Icc.mp (hA hnA)).2⟩
      have hHalf : N / 2 < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN) (by norm_num)
      have hBCard := ih (N / 2) hHalf B hBPrefix
        (fun M T hTB hT => hDensity M T (hTB.trans hBA) hT)
      have hCCard := hDensity N C hCA hCTail
      have hSplit : (B.card : ℝ) + C.card = A.card := by
        exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (fun n => n ≤ N / 2)
      have hFloor : (2 : ℝ) * (N / 2 : ℕ) ≤ N := by
        exact_mod_cast (show 2 * (N / 2) ≤ N by omega)
      have hHalfBound := mul_le_mul_of_nonneg_left hFloor hδ
      nlinarith only [hBCard, hCCard, hSplit, hHalfBound]

theorem exists_smooth_prefix_density_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y t : ℕ) (A : Finset ℕ),
      4 ≤ Real.log Y → A ⊆ Finset.Icc 1 t →
      (∀ n ∈ A, n.maxPrimeFac ≤ Y) →
      (Y : ℝ) ^ (2 * Real.log Y) ≤ t →
      (A.card : ℝ) ≤ ((1 : ℝ) / Y + C * Real.log Y / Y) * t := by
  classical
  obtain ⟨C, hC, hRankin⟩ := exists_rankin_smooth_tail_bound
  refine ⟨C, hC, ?_⟩
  intro Y t A hLog hA hSmooth hScale
  have hLogPos : 0 < Real.log Y := by linarith
  have hYOne : 1 < (Y : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg Y)).mp hLogPos
  have hYPos : 0 < (Y : ℝ) := zero_lt_one.trans hYOne
  let X : ℝ := (Y : ℝ) ^ Real.log Y
  let Small : Finset ℕ := A.filter (fun n : ℕ => (n : ℝ) ≤ X)
  let Large : Finset ℕ := A.filter (fun n : ℕ => ¬ (n : ℝ) ≤ X)
  have hSmallSub : Small ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro n hn
    obtain ⟨hnA, hnX⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hA hnA)).1, Nat.le_floor hnX⟩
  have hSmallCard : (Small.card : ℝ) ≤ X := by
    have hNat : Small.card ≤ ⌊X⌋₊ := by simpa using Finset.card_le_card hSmallSub
    exact (by exact_mod_cast hNat : (Small.card : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg Y) _))
  have hXBound : X ≤ (t : ℝ) / Y := by
    apply (le_div_iff₀ hYPos).mpr
    calc
      X * Y = (Y : ℝ) ^ (Real.log Y + 1) := by
        rw [Real.rpow_add hYPos, Real.rpow_one]
      _ ≤ (Y : ℝ) ^ (2 * Real.log Y) :=
        Real.rpow_le_rpow_of_exponent_le hYOne.le (by linarith)
      _ ≤ t := hScale
  have hLargeSub : Large ⊆ Finset.Icc 1 t := (Finset.filter_subset _ _).trans hA
  have hLargeMass := hRankin Y (Real.log Y) Large hLog
    (fun n hn => ⟨(Finset.mem_Icc.mp (hLargeSub hn)).1,
      hSmooth n (Finset.mem_filter.mp hn).1⟩)
    (fun n hn => (lt_of_not_ge (Finset.mem_filter.mp hn).2).le)
  rw [Real.exp_neg, Real.exp_log hYPos] at hLargeMass
  have hLargeCard := card_le_N_mul_reciprocalSum hLargeSub
  rw [← reciprocalSum_eq_baseline] at hLargeCard
  have hLargeBound : (Large.card : ℝ) ≤ (t : ℝ) * (C * (Y : ℝ)⁻¹ * Real.log Y) :=
    hLargeCard.trans (mul_le_mul_of_nonneg_left hLargeMass (Nat.cast_nonneg t))
  have hSplit : (Small.card : ℝ) + Large.card = A.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (fun n => (n : ℝ) ≤ X)
  calc
    (A.card : ℝ) = Small.card + Large.card := hSplit.symm
    _ ≤ (t : ℝ) / Y + (t : ℝ) * (C * (Y : ℝ)⁻¹ * Real.log Y) :=
      add_le_add (hSmallCard.trans hXBound) hLargeBound
    _ = ((1 : ℝ) / Y + C * Real.log Y / Y) * t := by ring

end Erdos319Sharp
