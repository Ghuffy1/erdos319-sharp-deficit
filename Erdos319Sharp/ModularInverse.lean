import Erdos319Sharp.Imported.ErdosProblems.Erdos285.SubsetSum

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- The prime-pool specialization of Martin's inverse subset-sum theorem.
The modulus is an arbitrary sufficiently large positive integer. -/
theorem eventually_prime_inverse_subset_sum :
    ∀ᶠ n : ℕ in atTop, ∀ (D : ℕ) (B : ℝ) (M : Finset ℕ),
      M.card ≤ D → 0 < B →
      1 / Real.log (Real.log n) ^ (1 / 2 : ℝ) < B →
      200 * (B ^ (2 / 3 : ℝ) * Real.log n /
        Real.log (Real.log n) ^ (2 / 3 : ℝ)) < M.card →
      (∀ p ∈ M, (p : ℝ) < B ∧ p.Prime ∧ ¬ p ∣ n) →
      ∀ a : ZMod n, ∃ K : Finset ℕ, K ⊆ M ∧ K.card ≤ D ∧
        K.sum (fun p => ((p : ZMod n)⁻¹)) = a := by
  have hSource :=
    Erdos319Imported.Erdos285.SubsetSum.eventually_bounded_inverse_subset_sum_of_martin_hypotheses
      1 (by norm_num)
  filter_upwards [hSource] with n h
  intro D B M hCard hB hSmall hLarge hPrimes a
  refine h D B M hCard hB ?_ ?_ ?_ a
  · simpa using hSmall
  · simpa using hLarge
  · intro p hp
    obtain ⟨hpB, hpPrime, hpAway⟩ := hPrimes p hp
    refine ⟨hpB, {p}, by simp, ?_, by simp⟩
    intro q hq
    have hqp : q = p := by simpa using hq
    subst q
    exact ⟨hpPrime, hpAway⟩

end Erdos319Sharp
