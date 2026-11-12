import Erdos319Sharp.DenseRepresentation
import Erdos319Sharp.ResidueCorrection

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem exists_unit_sum_above (L : ℕ) :
    ∃ A : Finset ℕ, (∀ n ∈ A, L < n) ∧ reciprocalSum A = 1 := by
  let a : ℝ := Real.exp (-4)
  have ha : 0 < a := Real.exp_pos _
  have hMass : Real.log (1 / a) = 4 := by
    dsimp [a]
    rw [one_div, Real.log_inv, Real.log_exp]
    norm_num
  have hCore := eventually_dense_tail_core a ha (by rw [hMass]; norm_num)
  have hLog := tendsto_log_coe_at_top.eventually (eventually_ge_atTop (5 : ℝ))
  have hLarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_gt_atTop ((L : ℝ) / a))
  obtain ⟨N, hCoreN, hLogN, hLargeN⟩ := (hCore.and (hLog.and hLarge)).exists
  have hMissing : ((Finset.Icc 1 N \ Finset.Icc 1 N).card : ℝ) ≤ (a / 8) * N := by
    simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨F, hF, _, _, _, _, hTargets⟩ := hCoreN (Finset.Icc 1 N) Finset.Subset.rfl hMissing
  have hLower : (Real.log (1 / a) + 1) / Real.log N ≤ (1 : ℝ) := by
    rw [hMass]
    apply (div_le_one (by linarith)).mpr
    linarith only [hLogN]
  obtain ⟨A, hAF, hSum⟩ := hTargets 1 (by simp)
    (by simpa only [Rat.cast_one] using hLower) (by norm_num)
  refine ⟨A, ?_, hSum⟩
  intro n hn
  have hTail := (Finset.mem_inter.mp (hF (hAF hn))).2
  have hAbove := ((mem_tailInterval a ha.le N n).mp hTail).2.2
  have hL : (L : ℝ) < a * N := by
    have h := (div_lt_iff₀ ha).mp hLargeN
    nlinarith only [h]
  exact_mod_cast hL.trans hAbove

theorem exists_integer_sum_above (m L : ℕ) :
    ∃ A : Finset ℕ, (∀ n ∈ A, L < n) ∧ reciprocalSum A = m := by
  classical
  induction m with
  | zero => exact ⟨∅, by simp, by simp [reciprocalSum]⟩
  | succ m ih =>
      obtain ⟨A, hAbove, hSum⟩ := ih
      obtain ⟨B, hBAbove, hBSum⟩ := exists_unit_sum_above (max L (A.sup id))
      have hDisjoint : Disjoint A B := Finset.disjoint_left.mpr (by
        intro n hnA hnB
        have hHigh := hBAbove n hnB
        have hLow : n ≤ max L (A.sup id) := (Finset.le_sup (f := id) hnA).trans (le_max_right _ _)
        omega)
      have hUnion : reciprocalSum (A ∪ B) = reciprocalSum A + reciprocalSum B :=
        Finset.sum_union hDisjoint
      refine ⟨A ∪ B, ?_, ?_⟩
      · intro n hn
        rcases Finset.mem_union.mp hn with hnA | hnB
        · exact hAbove n hnA
        · exact (le_max_left L (A.sup id)).trans_lt (hBAbove n hnB)
      · rw [hUnion, hSum, hBSum]
        simp only [Nat.cast_add, Nat.cast_one]

theorem exists_fraction_sum_above_multiple (D c m L : ℕ) (hD : 0 < D) (hc : 0 < c) :
    ∃ A : Finset ℕ, (∀ n ∈ A, L < n ∧ c ∣ n ∧ D ∣ n) ∧
      reciprocalSum A = (m : ℚ) / D := by
  classical
  obtain ⟨B, hB, hSum⟩ := exists_integer_sum_above (c * m) L
  let A := B.image (fun n => (c * D) * n)
  have hScale : 0 < c * D := Nat.mul_pos hc hD
  refine ⟨A, ?_, ?_⟩
  · intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have hAtLeast : b ≤ (c * D) * b := by nlinarith only [hScale]
    exact ⟨(hB b hb).trans_le hAtLeast, (dvd_mul_right c D).trans (dvd_mul_right (c * D) b),
      (dvd_mul_left D c).trans (dvd_mul_right (c * D) b)⟩
  · rw [reciprocalSum_mul_image B (c * D) hScale, hSum, Nat.cast_mul, Nat.cast_mul]
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp

theorem exists_bounded_fraction_reservoir (D c k L : ℕ) (hD : 0 < D) (hc : 0 < c) :
    ∃ R : Finset ℕ, (∀ n ∈ R, L < n ∧ c ∣ n ∧ D ∣ n) ∧
      ∀ m : ℕ, m ≤ k → ∃ A ⊆ R, reciprocalSum A = (m : ℚ) / D := by
  classical
  have hEach : ∀ m : ℕ, ∃ A : Finset ℕ, (∀ n ∈ A, L < n ∧ c ∣ n ∧ D ∣ n) ∧
      reciprocalSum A = (m : ℚ) / D := fun m => exists_fraction_sum_above_multiple D c m L hD hc
  choose A hAbove hSum using hEach
  let R := (Finset.range (k + 1)).biUnion A
  refine ⟨R, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, _, hm⟩ := Finset.mem_biUnion.mp hn
    exact hAbove m n hm
  · intro m hm
    refine ⟨A m, ?_, hSum m⟩
    intro n hn
    exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by omega), hn⟩

end Erdos319Sharp
