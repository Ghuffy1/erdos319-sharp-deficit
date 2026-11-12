import Erdos319Sharp.SmallMissingPowers

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_core_omission_count (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (a : ℝ) (A : Finset ℕ) (τ : ℕ → ℤˣ) (F P : Finset ℕ),
      0 ≤ a → a ≤ 1 / 4 → A ⊆ Finset.Icc 1 N →
      F ⊆ negativePart A τ ∩ tailInterval a N → F.lcm id ≠ 0 →
      (∀ b : ℕ, 0 < b →
        InverseZeroSumFree b (excessCofactors (F.lcm id) b (positivePart A τ \ P))) →
      (1 - 2 * a) * (N : ℝ) * (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) -
        (N : ℝ) * (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) ^ 2 -
          4 * smoothCutoff 6 N - 2 * (N : ℝ) * primePowerTail N (smoothCutoff 6 N) ≤
        ((N - A.card : ℕ) : ℝ) + (((negativePart A τ ∩ tailInterval a N) \ F).card : ℝ) +
          P.card + 2 * ε * (N : ℝ) * (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) *
            Real.exp (2 * (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ)) := by
  classical
  filter_upwards [eventually_small_scale_nondivisor_count ε hε, eventually_gt_atTop (0 : ℕ)]
    with N hSparse hN
  intro a A τ F P ha haQuarter hA hF hD hFree
  let D := F.lcm id
  let S := smoothCutoff 6 N
  let Q := smallMissingPowers D N S
  let T : Finset ℕ := (singleDivisorSet a N Q).filter (fun n => PrimePowerSmooth S n)
  let O : Finset ℕ := Finset.Icc 1 N \ A
  let R : Finset ℕ := (negativePart A τ ∩ tailInterval a N) \ F
  let E : Finset ℕ := T ∩ (positivePart A τ \ P)
  have hProperty : ∀ n ∈ T, ¬ n ∣ D ∧ (excessScale D (denominatorExcess D n) : ℝ) ≤ S := by
    intro n hn
    exact single_small_missing_smooth_scale D N n a S ha hD
      (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  have hTTail : T ⊆ tailInterval a N := by
    intro n hn
    exact ((mem_singleDivisorSet a N n Q).mp (Finset.mem_filter.mp hn).1).1
  have hTPrefix : T ⊆ Finset.Icc 1 N := hTTail.trans (tailInterval_subset a N)
  have hCover : T ⊆ O ∪ (R ∪ (P ∪ E)) := by
    intro n hn
    by_cases hnA : n ∈ A
    · have hParts : n ∈ positivePart A τ ∪ negativePart A τ := by
        rw [positivePart_union_negativePart]
        exact hnA
      rcases Finset.mem_union.mp hParts with hnPos | hnNeg
      · by_cases hnP : n ∈ P
        · exact Finset.mem_union_right O (Finset.mem_union_right R (Finset.mem_union_left E hnP))
        · exact Finset.mem_union_right O (Finset.mem_union_right R (Finset.mem_union_right P
            (Finset.mem_inter.mpr ⟨hn, Finset.mem_sdiff.mpr ⟨hnPos, hnP⟩⟩)))
      · have hnR : n ∈ R := Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hnNeg, hTTail hn⟩, by
            intro hnF
            exact (hProperty n hn).1 (Finset.dvd_lcm hnF)⟩
        exact Finset.mem_union_right O (Finset.mem_union_left (P ∪ E) hnR)
    · exact Finset.mem_union_left (R ∪ (P ∪ E)) (Finset.mem_sdiff.mpr ⟨hTPrefix hn, hnA⟩)
  have hCardCover : T.card ≤ O.card + R.card + P.card + E.card := by
    have hFirst := (Finset.card_le_card hCover).trans (Finset.card_union_le O (R ∪ (P ∪ E)))
    have hSecond := Finset.card_union_le R (P ∪ E)
    have hThird := Finset.card_union_le P E
    omega
  have hEPrefix : E ⊆ Finset.Icc 1 N := Finset.inter_subset_left.trans hTPrefix
  have hEFree : ∀ b : ℕ, 0 < b → InverseZeroSumFree b (excessCofactors D b E) := by
    intro b hb
    exact ZeroSumFree.mono (hFree b hb) (excessCofactors_mono D b Finset.inter_subset_right)
  have hECard := hSparse D E hD hEPrefix
    (fun n hn => (hProperty n (Finset.mem_inter.mp hn).1).1) hEFree
    (fun n hn => (hProperty n (Finset.mem_inter.mp hn).1).2)
  have hOCard : O.card = N - A.card := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset hA]
    simp
  have hCoverReal : (T.card : ℝ) ≤ ((N - A.card : ℕ) : ℝ) + R.card + P.card + E.card := by
    exact_mod_cast (hOCard ▸ hCardCover)
  have hLower := smooth_single_missing_count_lower a S D N ha haQuarter
    (smoothCutoff_pos 6 hN).le hD
  change (1 - 2 * a) * (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) -
    (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) ^ 2 -
      4 * S - 2 * (N : ℝ) * primePowerTail N S ≤ (T.card : ℝ) at hLower
  change (1 - 2 * a) * (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) -
    (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) ^ 2 -
      4 * S - 2 * (N : ℝ) * primePowerTail N S ≤
        ((N - A.card : ℕ) : ℝ) + R.card + P.card +
          2 * ε * (N : ℝ) * (reciprocalSum (firstMissingPowers D N) : ℝ) *
            Real.exp (2 * (reciprocalSum (firstMissingPowers D N) : ℝ))
  linarith only [hLower, hCoverReal, hECard]

end Erdos319Sharp
