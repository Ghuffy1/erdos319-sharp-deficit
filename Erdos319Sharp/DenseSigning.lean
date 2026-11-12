import Erdos319Sharp.DenseRepresentation
import Erdos319Sharp.MinorityBound

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem sign_parts_card (A : Finset ℕ) (δ : ℕ → ℤˣ) :
    (positivePart A δ).card + (negativePart A δ).card = A.card := by
  have hDisjoint : Disjoint (positivePart A δ) (negativePart A δ) := by
    apply Finset.disjoint_left.mpr
    intro n hPos hNeg
    have hp := (Finset.mem_filter.mp hPos).2
    have hn := (Finset.mem_filter.mp hNeg).2
    exact unit_ne_neg_self 1 (hp.symm.trans hn)
  rw [← Finset.card_union_of_disjoint hDisjoint, positivePart_union_negativePart]

theorem exists_dense_sign_part (N : ℕ) (A : Finset ℕ) (δ : ℕ → ℤˣ) (M : ℝ)
    (hA : A ⊆ Finset.Icc 1 N)
    (hMin : min ((positivePart A δ).card : ℝ) ((negativePart A δ).card : ℝ) ≤ M) :
    ∃ B : Finset ℕ, (B = positivePart A δ ∨ B = negativePart A δ) ∧
      B ⊆ Finset.Icc 1 N ∧
      ((Finset.Icc 1 N \ B).card : ℝ) ≤ ((N - A.card : ℕ) : ℝ) + M := by
  have hPos : positivePart A δ ⊆ Finset.Icc 1 N := (Finset.filter_subset _ _).trans hA
  have hNeg : negativePart A δ ⊆ Finset.Icc 1 N := (Finset.filter_subset _ _).trans hA
  have hCard := sign_parts_card A δ
  have hAcard : A.card ≤ N := by simpa using Finset.card_le_card hA
  have hPosOmissions : (Finset.Icc 1 N \ positivePart A δ).card =
      (N - A.card) + (negativePart A δ).card := by
    rw [Finset.card_sdiff_of_subset hPos]
    have hI : (Finset.Icc 1 N).card = N := by simp
    rw [hI]
    omega
  have hNegOmissions : (Finset.Icc 1 N \ negativePart A δ).card =
      (N - A.card) + (positivePart A δ).card := by
    rw [Finset.card_sdiff_of_subset hNeg]
    have hI : (Finset.Icc 1 N).card = N := by simp
    rw [hI]
    omega
  by_cases hOrder : ((positivePart A δ).card : ℝ) ≤ (negativePart A δ).card
  · refine ⟨negativePart A δ, Or.inr rfl, hNeg, ?_⟩
    rw [min_eq_left hOrder] at hMin
    rw [hNegOmissions, Nat.cast_add]
    linarith only [hMin]
  · refine ⟨positivePart A δ, Or.inl rfl, hPos, ?_⟩
    rw [min_eq_right (le_of_not_ge hOrder)] at hMin
    rw [hPosOmissions, Nat.cast_add]
    linarith only [hMin]

theorem eventually_dense_sign_core (a K : ℝ) (ha : 0 < a)
    (hMass : 3 ≤ Real.log (1 / a)) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ →
      ((N - A.card : ℕ) : ℝ) ≤ K * ((N : ℝ) * minorityScale N) →
      ∃ B : Finset ℕ, (B = positivePart A δ ∨ B = negativePart A δ) ∧
        ∃ F ⊆ B ∩ tailInterval a N,
          (∀ n ∈ F, PrimePowerSmooth (smoothCutoff 6 N) n) ∧
          ((tailInterval a N \ F).card : ℝ) ≤ (N : ℝ) *
            ((201 + 2 * K) * minorityScale N + (Real.log N) ^ (-(1 / 40 : ℝ))) ∧
          (N : ℝ) / 2 ≤ F.card ∧
          |(reciprocalSum F : ℝ) - Real.log (1 / a)| ≤ 1 / 2 ∧
          ∀ r : ℚ, r.den ∣ F.lcm id →
            (Real.log (1 / a) + 1) / Real.log N ≤ (r : ℝ) → (r : ℝ) ≤ 2 →
            ∃ U ⊆ F, reciprocalSum U = r := by
  have hLimit : Tendsto (fun N : ℕ => (201 + 2 * K) * minorityScale N) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_minorityScale_zero.const_mul (201 + 2 * K)
  have hSmall := hLimit.eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < a / 8))
  filter_upwards [eventually_minority_bound 1 (by norm_num), eventually_dense_tail_core a ha hMass,
    hSmall] with N hMinority hCore hSmallN
  intro A δ hA hPrimitive hDeficit
  have hMin : min ((positivePart A δ).card : ℝ) ((negativePart A δ).card : ℝ) ≤
      (201 + K) * ((N : ℝ) * minorityScale N) := by
    have h := hMinority A δ hA hPrimitive
    norm_num only [one_mul] at h
    nlinarith only [h, hDeficit]
  obtain ⟨B, hChoice, hB, hMissing⟩ :=
    exists_dense_sign_part N A δ ((201 + K) * ((N : ℝ) * minorityScale N)) hA hMin
  have hBbound : ((Finset.Icc 1 N \ B).card : ℝ) ≤
      (201 + 2 * K) * ((N : ℝ) * minorityScale N) := by
    nlinarith only [hMissing, hDeficit]
  have hBsmall : ((Finset.Icc 1 N \ B).card : ℝ) ≤ (a / 8) * N := by
    have h := mul_le_mul_of_nonneg_left hSmallN.le (Nat.cast_nonneg N)
    nlinarith only [hBbound, h]
  obtain ⟨F, hF, hSmooth, hLoss, hCard, hApprox, hTargets⟩ := hCore B hB hBsmall
  refine ⟨B, hChoice, F, hF, hSmooth, ?_, hCard, hApprox, hTargets⟩
  nlinarith only [hLoss, hBbound]

end Erdos319Sharp
