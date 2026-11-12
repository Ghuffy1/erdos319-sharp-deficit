import Erdos319Sharp.OppositeSignTarget
import Erdos319Sharp.PrimeAssignment

set_option autoImplicit false

open Filter Finset
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem exists_prime_assignment (X Y R : Finset ℕ) (b : ℝ)
    (hRare : ∀ p ∈ R, ((X.filter (fun n => p ∣ n)).card : ℝ) < b ∨
      ((Y.filter (fun n => p ∣ n)).card : ℝ) < b) :
    ∃ P Q : Finset ℕ, P ∪ Q = R ∧ Disjoint P Q ∧
      (∀ p ∈ P, ((Y.filter (fun n => p ∣ n)).card : ℝ) ≤ b) ∧
      (∀ p ∈ Q, ((X.filter (fun n => p ∣ n)).card : ℝ) ≤ b) := by
  classical
  let P : Finset ℕ := R.filter (fun p => ((Y.filter (fun n => p ∣ n)).card : ℝ) ≤ b)
  let Q : Finset ℕ := R \ P
  have hPR : P ⊆ R := Finset.filter_subset _ _
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · ext p
    simp only [Q, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hp | ⟨hp, _⟩)
      · exact hPR hp
      · exact hp
    · intro hp
      by_cases h : p ∈ P
      · exact Or.inl h
      · exact Or.inr ⟨hp, h⟩
  · exact Finset.disjoint_left.mpr (fun p hp hq => (Finset.mem_sdiff.mp hq).2 hp)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    obtain ⟨hpR, hpP⟩ := Finset.mem_sdiff.mp hp
    rcases hRare p hpR with hX | hY
    · exact hX.le
    · exact False.elim (hpP (Finset.mem_filter.mpr ⟨hpR, hY.le⟩))

def minorityBandError (R : Finset ℕ) (N : ℕ) : ℝ :=
  (R.card : ℝ) * ((N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ))) +
    3 * (R.prod id : ℕ)

def minorityEstimate (N : ℕ) (A R : Finset ℕ) : ℝ :=
  (N : ℝ) * primeAvoidanceDensity R +
    (Real.sqrt (primeAvoidanceDensity R) / (1 - Real.sqrt (primeAvoidanceDensity R))) *
      ((N - A.card : ℕ) + minorityBandError R N) + minorityBandError R N

theorem eventually_minority_prime_band_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (δ : ℕ → ℤˣ) (R : Finset ℕ),
      A ⊆ Finset.Icc 1 N → IsPrimitiveSigning A δ → R.Nonempty →
      (∀ p ∈ R, p.Prime ∧ (Real.log (Real.log N)) ^ 2 ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (Real.log N) ^ (1 / 100 : ℝ)) →
      min ((positivePart A δ).card : ℝ) ((negativePart A δ).card : ℝ) ≤
        max (4 * (N : ℝ) / (Real.log (Real.log N)) ^ 2) (minorityEstimate N A R) := by
  filter_upwards [eventually_opposite_prime_fiber_obstruction, eventually_ge_atTop 1] with N hObstruction hN
  intro A δ R hA hPrimitive hRne hR
  by_cases hPos : 4 * (N : ℝ) / (Real.log (Real.log N)) ^ 2 ≤ (positivePart A δ).card
  · by_cases hNeg : 4 * (N : ℝ) / (Real.log (Real.log N)) ^ 2 ≤ (negativePart A δ).card
    · have hRare : ∀ p ∈ R,
          (((positivePart A δ).filter (fun n => p ∣ n)).card : ℝ) <
              (N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)) ∨
            (((negativePart A δ).filter (fun n => p ∣ n)).card : ℝ) <
              (N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)) := by
        intro p hp
        exact hObstruction A δ p hA hPrimitive (hR p hp).1 (hR p hp).2.1
          (hR p hp).2.2 hPos hNeg
      obtain ⟨P, Q, hUnion, hDisjoint, hRareP, hRareQ⟩ :=
        exists_prime_assignment (positivePart A δ) (negativePart A δ) R
          ((N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ))) hRare
      have hP : ∀ p ∈ P, p.Prime := by
        intro p hp
        exact (hR p (hUnion ▸ Finset.mem_union_left Q hp)).1
      have hQ : ∀ p ∈ Q, p.Prime := by
        intro p hp
        exact (hR p (hUnion ▸ Finset.mem_union_right P hp)).1
      have hRPrime : ∀ p ∈ R, p.Prime := fun p hp => (hR p hp).1
      have hDensity : primeAvoidanceDensity (P ∪ Q) < 1 := by
        rw [hUnion]
        exact primeAvoidanceDensity_lt_one R hRPrime hRne
      have hb : 0 ≤ (N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)) := by
        apply mul_nonneg (Nat.cast_nonneg _)
        exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _
      have hBound := minority_bound_of_prime_assignment
        (positivePart A δ) (negativePart A δ) P Q N
        ((N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ)))
        ((Finset.filter_subset _ _).trans hA) ((Finset.filter_subset _ _).trans hA)
        hP hQ hDisjoint hb hDensity hRareP hRareQ
      have hCards : P.card + Q.card = R.card := by
        rw [← Finset.card_union_of_disjoint hDisjoint, hUnion]
      have hError : primeAssignmentError P Q
          ((N : ℝ) * (Real.log N) ^ (-(1 / 50 : ℝ))) = minorityBandError R N := by
        simp only [primeAssignmentError, hUnion, hCards, minorityBandError]
      have hOmissions : (Finset.Icc 1 N \ (positivePart A δ ∪ negativePart A δ)).card = N - A.card := by
        rw [positivePart_union_negativePart, Finset.card_sdiff_of_subset hA]
        simp
      rw [hUnion, hError, hOmissions] at hBound
      exact hBound.trans (le_max_right _ _)
    · exact (min_le_right _ _).trans ((le_of_not_ge hNeg).trans (le_max_left _ _))
  · exact (min_le_left _ _).trans ((le_of_not_ge hPos).trans (le_max_left _ _))

end Erdos319Sharp
