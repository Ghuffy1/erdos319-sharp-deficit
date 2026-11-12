import Erdos319Sharp.Harmonic
import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

def integerTail (b N : ℕ) : Finset ℕ := Icc (b + 1) N

theorem integerTail_eq_sdiff (b N : ℕ) :
    integerTail b N = Icc 1 N \ Icc 1 b := by
  ext n
  simp only [integerTail, Finset.mem_sdiff, Finset.mem_Icc]
  omega

theorem reciprocalSum_integerTail (b N : ℕ) (hbN : b ≤ N) :
    reciprocalSum (integerTail b N) = harmonic N - harmonic b := by
  have hSub : Icc 1 b ⊆ Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hbN⟩
  have hSplit : reciprocalSum (Icc 1 N \ Icc 1 b) + reciprocalSum (Icc 1 b) =
      reciprocalSum (Icc 1 N) := Finset.sum_sdiff hSub
  rw [← integerTail_eq_sdiff, reciprocalSum_Icc, reciprocalSum_Icc] at hSplit
  exact eq_sub_iff_add_eq.mpr hSplit

theorem divisiblePrefix_eq_image (N q : ℕ) (hq : 0 < q) :
    (Icc 1 N).filter (fun n => q ∣ n) = (Icc 1 (N / q)).image (fun n => n * q) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hDiv⟩ := Finset.mem_filter.mp hn
    obtain ⟨m, rfl⟩ := hDiv
    obtain ⟨hLower, hUpper⟩ := Finset.mem_Icc.mp hnI
    refine Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, by ring⟩
    · exact Nat.succ_le_of_lt (Nat.pos_of_mul_pos_left hLower)
    · exact (Nat.le_div_iff_mul_le hq).mpr (by simpa only [mul_comm] using hUpper)
  · intro hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hLower, hUpper⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨one_le_mul hLower hq, (Nat.le_div_iff_mul_le hq).mp hUpper⟩, dvd_mul_left _ _⟩

theorem reciprocalSum_divisiblePrefix (N q : ℕ) (hq : 0 < q) :
    reciprocalSum ((Icc 1 N).filter (fun n => q ∣ n)) = harmonic (N / q) / q := by
  rw [divisiblePrefix_eq_image N q hq]
  have hInjective : Set.InjOn (fun n : ℕ => n * q) (Icc 1 (N / q)) := by
    intro n hn m hm hEq
    exact Nat.eq_of_mul_eq_mul_right hq (by simpa only [mul_comm] using hEq)
  change (∑ n ∈ (Icc 1 (N / q)).image (fun n => n * q), (n : ℚ)⁻¹) = _
  rw [Finset.sum_image hInjective]
  calc
    (∑ n ∈ Icc 1 (N / q), ((n * q : ℕ) : ℚ)⁻¹) =
        ∑ n ∈ Icc 1 (N / q), (n : ℚ)⁻¹ / q := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Nat.cast_mul, mul_inv_rev, div_eq_mul_inv, mul_comm]
    _ = (∑ n ∈ Icc 1 (N / q), (n : ℚ)⁻¹) / q := (Finset.sum_div _ _ _).symm
    _ = harmonic (N / q) / q := by rw [← reciprocalSum_Icc]; rfl

theorem reciprocalSum_divisibleTail (b N q : ℕ) (hbN : b ≤ N) (hq : 0 < q) :
    reciprocalSum ((integerTail b N).filter (fun n => q ∣ n)) =
      (harmonic (N / q) - harmonic (b / q)) / q := by
  have hSub : (Icc 1 b).filter (fun n => q ∣ n) ⊆ (Icc 1 N).filter (fun n => q ∣ n) := by
    intro n hn
    obtain ⟨hnI, hDiv⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hnI).1, (Finset.mem_Icc.mp hnI).2.trans hbN⟩, hDiv⟩
  have hSet : (integerTail b N).filter (fun n => q ∣ n) =
      (Icc 1 N).filter (fun n => q ∣ n) \ (Icc 1 b).filter (fun n => q ∣ n) := by
    ext n
    simp only [integerTail, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    omega
  have hSplit : reciprocalSum ((integerTail b N).filter (fun n => q ∣ n)) +
      reciprocalSum ((Icc 1 b).filter (fun n => q ∣ n)) =
      reciprocalSum ((Icc 1 N).filter (fun n => q ∣ n)) := by
    rw [hSet]
    exact Finset.sum_sdiff hSub
  rw [reciprocalSum_divisiblePrefix b q hq, reciprocalSum_divisiblePrefix N q hq] at hSplit
  have hEq := eq_sub_iff_add_eq.mpr hSplit
  calc
    _ = harmonic (N / q) / q - harmonic (b / q) / q := hEq
    _ = _ := by ring

theorem harmonic_gap_upper (b N : ℕ) (hb : 0 < b) (hbN : b ≤ N) :
    (harmonic N : ℝ) - (harmonic b : ℝ) ≤ 1 + Real.log ((N : ℝ) / b) := by
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hb.trans_le hbN
  have hbPos : (0 : ℝ) < b := by exact_mod_cast hb
  have hUpper := harmonic_le_one_add_log N
  have hLower : Real.log (b : ℝ) ≤ (harmonic b : ℝ) := by
    simpa only [Nat.floor_natCast] using log_le_harmonic_floor (b : ℝ) (Nat.cast_nonneg b)
  rw [Real.log_div hNPos.ne' hbPos.ne']
  linarith

theorem reciprocalSum_divisibleTail_upper (b N q : ℕ) (hq : 0 < q)
    (hqb : q ≤ b) (hbN : b ≤ N) :
    (reciprocalSum ((integerTail b N).filter (fun n => q ∣ n)) : ℝ) ≤
      (1 + Real.log (2 * (N : ℝ) / b)) / q := by
  have hm : 1 ≤ b / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa using hqb)
  have hQuotient : b / q ≤ N / q := Nat.div_le_div_right hbN
  have hB : b ≤ 2 * (b / q) * q := by
    have hRemainder := (Nat.mod_lt b hq).le
    have hQLe : q ≤ q * (b / q) := by
      simpa only [mul_one] using Nat.mul_le_mul_left q hm
    calc
      b = b % q + q * (b / q) := (Nat.mod_add_div b q).symm
      _ ≤ q + q * (b / q) := Nat.add_le_add_right hRemainder _
      _ ≤ q * (b / q) + q * (b / q) := Nat.add_le_add_right hQLe _
      _ = _ := by ring
  have hNQ : (N / q) * q ≤ N := Nat.div_mul_le_self N q
  have hmPos : (0 : ℝ) < (b / q : ℕ) := by exact_mod_cast (by omega : 0 < b / q)
  have hbPos : (0 : ℝ) < b := by exact_mod_cast hq.trans_le hqb
  have hMPos : (0 : ℝ) < (N / q : ℕ) := by exact_mod_cast (by omega : 0 < N / q)
  have hBReal : (b : ℝ) ≤ 2 * (b / q : ℕ) * (q : ℝ) := by exact_mod_cast hB
  have hNQReal : (N / q : ℕ) * (q : ℝ) ≤ N := by exact_mod_cast hNQ
  have hRatio : (N / q : ℕ) / (b / q : ℕ) ≤ 2 * (N : ℝ) / b := by
    apply (div_le_div_iff₀ hmPos hbPos).mpr
    calc
      ((N / q : ℕ) : ℝ) * b ≤ (N / q : ℕ) * (2 * (b / q : ℕ) * (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hBReal hMPos.le
      _ = (2 * (b / q : ℕ)) * ((N / q : ℕ) * (q : ℝ)) := by ring
      _ ≤ (2 * (b / q : ℕ)) * (N : ℝ) := mul_le_mul_of_nonneg_left hNQReal (by positivity)
      _ = (2 * (N : ℝ)) * (b / q : ℕ) := by ring
  have hLog := Real.log_le_log (div_pos hMPos hmPos) hRatio
  have hHarmonic := harmonic_gap_upper (b / q) (N / q) (by omega) hQuotient
  have hBound : (harmonic (N / q) : ℝ) - (harmonic (b / q) : ℝ) ≤
      1 + Real.log (2 * (N : ℝ) / b) := by linarith
  rw [reciprocalSum_divisibleTail b N q hbN hq]
  push_cast
  exact div_le_div_of_nonneg_right hBound (Nat.cast_nonneg q)

end Erdos319Sharp
