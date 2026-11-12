import Erdos319Sharp.PrimaryProducts

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem primaryHeight_finset_lcm_le (A : Finset ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ n ∈ A, n ≠ 0 ∧ primaryHeight n ≤ M) : primaryHeight (A.lcm id) ≤ M := by
  classical
  revert hA
  induction A using Finset.induction_on with
  | empty => intro hA; simpa [primaryHeight] using hM
  | @insert n A hn ih =>
      intro hA
      have hnBound := hA n (Finset.mem_insert_self _ _)
      have hRest : ∀ m ∈ A, m ≠ 0 ∧ primaryHeight m ≤ M :=
        fun m hm => hA m (Finset.mem_insert_of_mem hm)
      have hLcm : A.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun m hm => (hRest m hm).1)
      rw [Finset.lcm_insert, id_eq, lcm_eq_nat_lcm,
        primaryHeight_lcm n (A.lcm id) hnBound.1 hLcm]
      exact max_le hnBound.2 (ih hRest)

theorem primaryHeight_reciprocalSum_le (A : Finset ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ n ∈ A, n ≠ 0 ∧ primaryHeight n ≤ M) :
    primaryHeight (reciprocalSum A).den ≤ M := by
  have hLcm : A.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun n hn => (hA n hn).1)
  letI : NeZero (A.lcm id) := ⟨hLcm⟩
  have hDen : (reciprocalSum A).den ∣ A.lcm id := by
    exact reciprocalSum_den_dvd_common A (fun n hn => Finset.dvd_lcm hn)
  exact (primaryHeight_mono_dvd _ _ (reciprocalSum A).den_ne_zero hLcm hDen).trans
    (primaryHeight_finset_lcm_le A M hM hA)

theorem primaryHeight_sub_le (r s : ℚ) (M : ℕ)
    (hr : primaryHeight r.den ≤ M) (hs : primaryHeight s.den ≤ M) :
    primaryHeight (r - s).den ≤ M := by
  have hLcm : r.den.lcm s.den ≠ 0 := Nat.lcm_ne_zero r.den_ne_zero s.den_ne_zero
  have hHeight : primaryHeight (r.den.lcm s.den) ≤ M := by
    rw [primaryHeight_lcm r.den s.den r.den_ne_zero s.den_ne_zero]
    exact max_le hr hs
  exact (primaryHeight_mono_dvd _ _ (r - s).den_ne_zero hLcm (Rat.sub_den_dvd_lcm r s)).trans hHeight

theorem primaryHeight_le_of_smooth (d : ℕ) (S : ℝ) (hS : 1 ≤ S)
    (hSmooth : PrimePowerSmooth S d) : (primaryHeight d : ℝ) ≤ S := by
  by_cases hSmall : primaryHeight d ≤ 1
  · exact (by exact_mod_cast hSmall : (primaryHeight d : ℝ) ≤ 1).trans hS
  · obtain ⟨p, hp, hExponent, hHeight⟩ := exists_prime_at_primaryHeight d (by omega)
    have hPower : IsPrimePow (p ^ d.factorization p) :=
      (isPrimePow_nat_iff _).mpr ⟨p, d.factorization p, hp, hExponent, rfl⟩
    rw [hHeight]
    exact hSmooth _ hPower (Nat.ordProj_dvd d p)

end Erdos319Sharp
