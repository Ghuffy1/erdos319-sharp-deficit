import Erdos319Sharp.DenseTail

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem prefix_multiples_card (N q : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card = N / q := by
  have hInterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hInterval]
  exact Nat.Ioc_filter_dvd_card_eq_div N q

theorem prefix_multiples_card_le (N q : ℕ) (hq : 0 < q) :
    (((Finset.Icc 1 N).filter (fun n => q ∣ n)).card : ℝ) ≤ (N : ℝ) / q := by
  rw [prefix_multiples_card]
  apply (le_div_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
  exact_mod_cast Nat.div_mul_le_self N q

theorem tail_multiples_card_lower (a : ℝ) (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4)
    (N q : ℕ) (hq : 0 < q) (hqN : q ≤ N) :
    (N : ℝ) / (4 * q) ≤ ((tailInterval a N).filter (fun n => q ∣ n)).card := by
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hAN : a * N ≤ (N : ℝ) / 4 := by
    have h := mul_le_mul_of_nonneg_right haQuarter (Nat.cast_nonneg N)
    nlinarith only [h]
  by_cases hSmall : 4 * (q : ℝ) ≤ N
  · have hCount := coprimeWindow_divisor_card_lower 1 q (by norm_num) hq (by simp) a ha N
    simp only [Nat.cast_one, mul_one] at hCount
    change (1 - a) / (q : ℝ) * N - 2 ≤
      ((tailInterval a N).filter (fun n => q ∣ n)).card at hCount
    have hMul := mul_le_mul_of_nonneg_left hCount hqReal.le
    have hCancel : (q : ℝ) * ((1 - a) / q * N - 2) = (1 - a) * N - 2 * q := by
      field_simp [hqReal.ne']
      <;> ring
    rw [hCancel] at hMul
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hqReal)).mpr
    nlinarith only [hMul, hSmall, hAN]
  · have hLarge : (N : ℝ) < 4 * q := lt_of_not_ge hSmall
    have hMember : q ∈ (tailInterval a N).filter (fun n => q ∣ n) := by
      refine Finset.mem_filter.mpr ⟨(mem_tailInterval a ha N q).mpr ⟨hq, hqN, ?_⟩, dvd_refl q⟩
      nlinarith only [hAN, hLarge]
    have hCard : (1 : ℝ) ≤ ((tailInterval a N).filter (fun n => q ∣ n)).card := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨q, hMember⟩)
    have hOne : (N : ℝ) / (4 * q) < 1 := by
      apply (div_lt_one (mul_pos (by norm_num : (0 : ℝ) < 4) hqReal)).mpr
      exact hLarge
    exact hOne.le.trans hCard

theorem missing_tail_multiples_le (a : ℝ) (N q : ℕ) (F : Finset ℕ)
    (hMissing : ∀ n ∈ F, ¬ q ∣ n) :
    (((tailInterval a N).filter (fun n => q ∣ n)).card : ℝ) ≤ (tailInterval a N \ F).card := by
  have hSub : (tailInterval a N).filter (fun n => q ∣ n) ⊆ tailInterval a N \ F := by
    intro n hn
    obtain ⟨hnT, hqn⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_sdiff.mpr ⟨hnT, fun hnF => hMissing n hnF hqn⟩
  exact_mod_cast Finset.card_le_card hSub

theorem tail_divisibility_first_moment_lower (a : ℝ) (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4)
    (N : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 0 < q ∧ q ≤ N) :
    (N : ℝ) / 4 * (∑ q ∈ Q, (1 : ℝ) / q) ≤
      ∑ q ∈ Q, (((tailInterval a N).filter (fun n => q ∣ n)).card : ℝ) := by
  calc
    (N : ℝ) / 4 * (∑ q ∈ Q, (1 : ℝ) / q) = ∑ q ∈ Q, (N : ℝ) / (4 * q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ ∑ q ∈ Q, (((tailInterval a N).filter (fun n => q ∣ n)).card : ℝ) :=
      Finset.sum_le_sum (fun q hq => tail_multiples_card_lower a ha haQuarter N q (hQ q hq).1 (hQ q hq).2)

end Erdos319Sharp
