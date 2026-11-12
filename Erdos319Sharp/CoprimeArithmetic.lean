import Erdos319Sharp.RationalCompatibility

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

theorem reciprocalSum_den_coprime (A : Finset ℕ) (G : ℕ)
    (hCop : ∀ n ∈ A, n.Coprime G) : (reciprocalSum A).den.Coprime G := by
  classical
  revert hCop
  induction A using Finset.induction_on with
  | empty => intro hCop; simp [reciprocalSum]
  | @insert n A hn ih =>
      intro hCop
      have hRest := ih (fun m hm => hCop m (Finset.mem_insert_of_mem hm))
      have hnCop := hCop n (Finset.mem_insert_self _ _)
      have hOneDen : ((n : ℚ)⁻¹).den ∣ n := by
        simpa only [Int.cast_one, one_div] using int_quotient_den_dvd 1 n
      have hOneCop := Nat.Coprime.of_dvd_left hOneDen hnCop
      have hSum : reciprocalSum (insert n A) = (n : ℚ)⁻¹ + reciprocalSum A := by
        exact Finset.sum_insert hn
      rw [hSum]
      exact Nat.Coprime.of_dvd_left (Rat.add_den_dvd _ _) (hOneCop.mul_left hRest)

theorem sub_den_coprime (r s : ℚ) (G : ℕ)
    (hr : r.den.Coprime G) (hs : s.den.Coprime G) : (r - s).den.Coprime G :=
  Nat.Coprime.of_dvd_left (Rat.sub_den_dvd _ _) (hr.mul_left hs)

theorem small_prime_coprime (p G C : ℕ) (hp : p.Prime) (hpC : p ≤ C)
    (hLarge : ∀ q : ℕ, q.Prime → q ∣ G → C < q) : p.Coprime G := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hDiv
  exact (not_lt_of_ge hpC) (hLarge p hp hDiv)

end Erdos319Sharp
