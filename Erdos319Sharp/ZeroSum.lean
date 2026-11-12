import Erdos319Sharp.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

open Finset

namespace Erdos319Sharp

def ZeroSumFree {G : Type*} [AddCommMonoid G] (A : Finset ℕ) (f : ℕ → G) : Prop :=
  ∀ T ⊆ A, T.Nonempty → (∑ n ∈ T, f n) ≠ 0

theorem ZeroSumFree.mono {G : Type*} [AddCommMonoid G]
    {A B : Finset ℕ} {f : ℕ → G} (h : ZeroSumFree A f) (hBA : B ⊆ A) :
    ZeroSumFree B f := by
  intro T hTB hT
  exact h T (hTB.trans hBA) hT

theorem prefix_sums_ne {G : Type*} [AddCommGroup G]
    {A : Finset ℕ} {f : ℕ → G} (h : ZeroSumFree A f)
    {x y : ℕ} (hxy : x < y) (hy : y ∈ A) :
    (∑ n ∈ A.filter (fun n => n ≤ x), f n) ≠
      ∑ n ∈ A.filter (fun n => n ≤ y), f n := by
  let X := A.filter (fun n => n ≤ x)
  let Y := A.filter (fun n => n ≤ y)
  have hXY : X ⊆ Y := by
    intro n hn
    obtain ⟨hnA, hnx⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnA, hnx.trans hxy.le⟩
  have hsub : Y \ X ⊆ A := by
    intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).1
  have hne : (Y \ X).Nonempty := by
    refine ⟨y, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hy, le_rfl⟩
    · intro hmem
      exact (not_le_of_gt hxy) (Finset.mem_filter.mp hmem).2
  intro heq
  have hs := Finset.sum_sdiff hXY (f := f)
  change (∑ n ∈ Y \ X, f n) + (∑ n ∈ X, f n) = ∑ n ∈ Y, f n at hs
  have hz : (∑ n ∈ Y \ X, f n) = 0 := by
    apply add_right_cancel (b := ∑ n ∈ X, f n)
    calc
      (∑ n ∈ Y \ X, f n) + (∑ n ∈ X, f n) = ∑ n ∈ Y, f n := hs
      _ = ∑ n ∈ X, f n := heq.symm
      _ = 0 + ∑ n ∈ X, f n := (zero_add _).symm
  exact h (Y \ X) hsub hne hz

/-- Distinct prefix sums give the cyclic-group length bound for every modulus. -/
theorem ZeroSumFree.card_lt_modulus {q : ℕ} (hq : 0 < q)
    {A : Finset ℕ} {f : ℕ → ZMod q}
    (hpos : ∀ n ∈ A, 0 < n) (h : ZeroSumFree A f) : A.card < q := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let F := fun a : ℕ => ∑ n ∈ A.filter (fun n => n ≤ a), f n
  have h0 : 0 ∉ A := by
    intro hm
    exact (Nat.lt_irrefl 0) (hpos 0 hm)
  have hinj : Set.InjOn F (insert 0 A : Finset ℕ) := by
    intro x hx y hy heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · have hyA : y ∈ A := by
        rcases Finset.mem_insert.mp hy with hy0 | hyA
        · exact False.elim ((Nat.not_lt_zero x) (hy0 ▸ hxy))
        · exact hyA
      exact prefix_sums_ne h hxy hyA heq
    · have hxA : x ∈ A := by
        rcases Finset.mem_insert.mp hx with hx0 | hxA
        · exact False.elim ((Nat.not_lt_zero y) (hx0 ▸ hyx))
        · exact hxA
      exact prefix_sums_ne h hyx hxA heq.symm
  have hcard : (insert 0 A).card ≤ (Finset.univ : Finset (ZMod q)).card :=
    Finset.card_le_card_of_injOn F (fun _ _ => Finset.mem_univ _) hinj
  have hbound : A.card + 1 ≤ q := by
    simpa only [Finset.card_insert_of_notMem h0, Finset.card_univ, ZMod.card] using hcard
  exact Nat.lt_of_succ_le hbound

def InverseZeroSumFree (q : ℕ) (A : Finset ℕ) : Prop :=
  ZeroSumFree A (fun n => (n : ZMod q)⁻¹)

theorem InverseZeroSumFree.card_lt {q : ℕ} (hq : 0 < q) {A : Finset ℕ}
    (hpos : ∀ n ∈ A, 0 < n) (h : InverseZeroSumFree q A) : A.card < q :=
  ZeroSumFree.card_lt_modulus hq hpos h

theorem InverseZeroSumFree.tail_mass_le_one {q : ℕ} (hq : 0 < q)
    {A : Finset ℕ} (hpos : ∀ n ∈ A, 0 < n) (h : InverseZeroSumFree q A) :
    reciprocalSum (A.filter (fun n => q < n)) ≤ 1 := by
  let T := A.filter (fun n => q < n)
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hcard : (T.card : ℚ) ≤ q := by
    exact_mod_cast ((Finset.card_le_card (Finset.filter_subset _ _)).trans
      (InverseZeroSumFree.card_lt hq hpos h).le)
  calc
    reciprocalSum T ≤ ∑ _n ∈ T, (q : ℚ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hqn : (q : ℚ) ≤ n := by
        exact_mod_cast (Finset.mem_filter.mp hn).2.le
      exact inv_anti₀ hqQ hqn
    _ = (T.card : ℚ) * (q : ℚ)⁻¹ := by simp
    _ ≤ (q : ℚ) * (q : ℚ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hqQ.le)
    _ = 1 := mul_inv_cancel₀ hqQ.ne'

end Erdos319Sharp
