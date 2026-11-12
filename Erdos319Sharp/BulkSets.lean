import Erdos319Sharp.PrimeTailCover
import Erdos319Sharp.ConstructionParameters
import Erdos319Sharp.SmoothTailRate

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

def smoothCoprimeTail (P : Finset ℕ) (b N : ℕ) (S : ℝ) : Finset ℕ := by
  classical
  exact ((integerTail b N).filter (fun n => n.Coprime (P.prod id))).filter
    (fun n => PrimePowerSmooth S n)

def constructionBulk (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  smoothCoprimeTail P (constructionBoundary N) N (smoothCutoff 6 N)

theorem mem_smoothCoprimeTail {P : Finset ℕ} {b N n : ℕ} {S : ℝ} :
    n ∈ smoothCoprimeTail P b N S ↔
      n ∈ integerTail b N ∧ n.Coprime (P.prod id) ∧ PrimePowerSmooth S n := by
  classical
  simp only [smoothCoprimeTail, Finset.mem_filter, and_assoc]

theorem smoothCoprimeTail_subset (P : Finset ℕ) (b N : ℕ) (S : ℝ) :
    smoothCoprimeTail P b N S ⊆ integerTail b N :=
  fun _ hn => (mem_smoothCoprimeTail.mp hn).1

theorem integerTail_subset (b N : ℕ) : integerTail b N ⊆ Icc 1 N := by
  intro n hn
  obtain ⟨hLower, hUpper⟩ := Finset.mem_Icc.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega, hUpper⟩

theorem smoothCoprimeTail_omission_bound (P : Finset ℕ) (b N : ℕ) (S : ℝ)
    (hPrime : ∀ p ∈ P, p.Prime) :
    (N : ℝ) - (smoothCoprimeTail P b N S).card ≤
      b + (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) + (N : ℝ) * primePowerTail N S := by
  classical
  let F := smoothCoprimeTail P b N S
  let I := Icc 1 N
  let K := I.filter (fun n => ¬n.Coprime (P.prod id))
  let R := I.filter (fun n => ¬PrimePowerSmooth S n)
  let D := I \ F
  have hFInside : F ⊆ I := (smoothCoprimeTail_subset P b N S).trans (integerTail_subset b N)
  have hCover : D ⊆ (Icc 1 b ∪ K) ∪ R := by
    intro n hn
    obtain ⟨hnI, hnF⟩ := Finset.mem_sdiff.mp hn
    by_cases hnb : n ≤ b
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, hnb⟩))
    · by_cases hCop : n.Coprime (P.prod id)
      · have hRough : ¬PrimePowerSmooth S n := by
          intro hSmooth
          apply hnF
          exact mem_smoothCoprimeTail.mpr ⟨Finset.mem_Icc.mpr
            ⟨by omega, (Finset.mem_Icc.mp hnI).2⟩, hCop, hSmooth⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hRough⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hCop⟩))
  have hUnion : ((Icc 1 b ∪ K) ∪ R).card ≤ (Icc 1 b).card + K.card + R.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hCardNat : D.card ≤ b + K.card + R.card := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using (Finset.card_le_card hCover).trans hUnion
  have hCard : (D.card : ℝ) ≤ b + (K.card : ℝ) + R.card := by exact_mod_cast hCardNat
  have hK : (K.card : ℝ) ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) :=
    prime_cover_card_bound N K P (Finset.filter_subset _ _) hPrime (by
      intro n hn
      exact primeProduct_nonCoprime_cover P n hPrime (Finset.mem_filter.mp hn).2)
  have hR : (R.card : ℝ) ≤ (N : ℝ) * primePowerTail N S :=
    nonsmooth_card_bound I Finset.Subset.rfl S
  have hSplitNat : D.card + F.card = N := by
    simpa only [I, Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_sdiff_add_card_eq_card hFInside
  have hSplit : (D.card : ℝ) + F.card = N := by exact_mod_cast hSplitNat
  change (N : ℝ) - F.card ≤ _
  linarith

end Erdos319Sharp
