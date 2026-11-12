import Erdos319Sharp.CommonPrimeTarget

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem IsPrimitiveSigning.no_equal_opposite_subsums {A U V : Finset ℕ} {δ : ℕ → ℤˣ}
    (hPrimitive : IsPrimitiveSigning A δ) (hU : U ⊆ positivePart A δ)
    (hV : V ⊆ negativePart A δ) (hUne : U.Nonempty) (hProper : U ≠ positivePart A δ)
    (hEqual : reciprocalSum U = reciprocalSum V) : False := by
  have hDisjoint : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro n hnU hnV
    have hPos := (Finset.mem_filter.mp (hU hnU)).2
    have hNeg := (Finset.mem_filter.mp (hV hnV)).2
    exact unit_ne_neg_self 1 (hPos.symm.trans hNeg)
  have hSub : U ∪ V ⊆ A := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact (Finset.mem_filter.mp (hU hn)).1
    · exact (Finset.mem_filter.mp (hV hn)).1
  have hUValue : signedSum U δ = reciprocalSum U := by
    unfold signedSum reciprocalSum
    apply Finset.sum_congr rfl
    intro n hn
    have hSign := (Finset.mem_filter.mp (hU hn)).2
    simp [hSign, one_div]
  have hVValue : signedSum V δ = -reciprocalSum V := by
    unfold signedSum reciprocalSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hSign := (Finset.mem_filter.mp (hV hn)).2
    simp [hSign, div_eq_mul_inv]
  have hZero : signedSum (U ∪ V) δ = 0 := by
    have hSum : signedSum (U ∪ V) δ = signedSum U δ + signedSum V δ :=
      Finset.sum_union hDisjoint
    rw [hSum, hUValue, hVValue, hEqual, add_neg_cancel]
  rcases hPrimitive.2 (U ∪ V) hSub hZero with hEmpty | hAll
  · obtain ⟨n, hn⟩ := hUne
    have h := Finset.mem_union_left V hn
    rw [hEmpty] at h
    exact Finset.notMem_empty n h
  · apply hProper
    apply Finset.Subset.antisymm hU
    intro n hn
    have hnA := (Finset.mem_filter.mp hn).1
    rw [← hAll] at hnA
    rcases Finset.mem_union.mp hnA with hnU | hnV
    · exact hnU
    · have hPos := (Finset.mem_filter.mp hn).2
      have hNeg := (Finset.mem_filter.mp (hV hnV)).2
      exact False.elim (unit_ne_neg_self 1 (hPos.symm.trans hNeg))

theorem eventually_opposite_prime_fiber_obstruction :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ) (p : ℕ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ → p.Prime →
      (Real.log (Real.log N)) ^ 2 ≤ (p : ℝ) → (p : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ) →
      4 * (N : ℝ) / (Real.log (Real.log N)) ^ 2 ≤ (positivePart A δ).card →
      4 * (N : ℝ) / (Real.log (Real.log N)) ^ 2 ≤ (negativePart A δ).card →
      (((positivePart A δ).filter (fun n => p ∣ n)).card : ℝ) <
          (N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)) ∨
        (((negativePart A δ).filter (fun n => p ∣ n)).card : ℝ) <
          (N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)) := by
  filter_upwards [eventually_common_prime_target] with N hTarget
  intro A δ p hA hPrimitive hp hpLow hpHigh hPos hNeg
  by_cases hPosSmall : (((positivePart A δ).filter (fun n => p ∣ n)).card : ℝ) <
      (N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ))
  · exact Or.inl hPosSmall
  right
  by_contra hNegSmall
  obtain ⟨U, hU, hUne, hUProper, hUSum⟩ := hTarget (positivePart A δ) p
    ((Finset.filter_subset _ _).trans hA) hp hpLow hpHigh hPos (le_of_not_gt hPosSmall)
  obtain ⟨V, hV, _, _, hVSum⟩ := hTarget (negativePart A δ) p
    ((Finset.filter_subset _ _).trans hA) hp hpLow hpHigh hNeg (le_of_not_gt hNegSmall)
  exact hPrimitive.no_equal_opposite_subsums hU hV hUne hUProper (hUSum.trans hVSum.symm)

end Erdos319Sharp
