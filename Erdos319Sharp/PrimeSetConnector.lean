import Erdos319Sharp.PairConnector

set_option autoImplicit false

open Finset

namespace Erdos319Sharp

theorem exists_prime_set_connector (P : Finset ℕ) (p q : ℕ)
    (hPrime : ∀ s ∈ P, s.Prime) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (rp : (ZMod p)ˣ) (rq : (ZMod q)ˣ)
    (hMass : (∑ s ∈ P, 1 / (s : ℝ)) ≤ 1 / 2) :
    ∃ u : ℕ, 0 < u ∧ u < 4 * P.card * (p * q) ∧
      (∀ s ∈ P, ¬ s ∣ u) ∧
      (((q * u : ℕ) : ZMod p)⁻¹ = (rp : ZMod p)) ∧
      (((p * u : ℕ) : ZMod q)⁻¹ = (rq : ZMod q)) := by
  classical
  let Q := (P.erase p).erase q
  have hSub : Q ⊆ P := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hPositive : ∀ s ∈ Q, 0 < s := fun s hs => (hPrime s (hSub hs)).pos
  have hCoprime : ∀ s ∈ Q, s.Coprime (p * q) := by
    intro s hs
    have hsNeq : s ≠ q := (Finset.mem_erase.mp hs).1
    have hsNep : s ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
    exact ((Nat.coprime_primes (hPrime s (hSub hs)) (hPrime p hp)).mpr hsNep).mul_right
      ((Nat.coprime_primes (hPrime s (hSub hs)) (hPrime q hq)).mpr hsNeq)
  have hSmall : (∑ s ∈ Q, 1 / (s : ℝ)) ≤ 1 / 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => by positivity)).trans hMass
  obtain ⟨u, huPos, huBound, huCop, huAvoid, huP, huQ⟩ :=
    exists_bounded_pair_connector p q Q (hPrime p hp).two_le (hPrime q hq).pos
      ((Nat.coprime_primes (hPrime p hp) (hPrime q hq)).mpr hpq) rp rq
      hPositive hCoprime hSmall
  have hCard : Q.card + 1 ≤ P.card := by
    have h := Finset.card_le_card (show Q ⊆ P.erase p from Finset.erase_subset _ _)
    have hErase := Finset.card_erase_add_one hp
    omega
  have hBound : 4 * (Q.card + 1) * (p * q) ≤ 4 * P.card * (p * q) := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hCard)
  refine ⟨u, huPos, huBound.trans_le hBound, ?_, huP, huQ⟩
  intro s hs
  by_cases hsp : s = p
  · subst s
    have hCop : u.Coprime p := Nat.Coprime.of_dvd_right (dvd_mul_right p q) huCop
    exact (hPrime p hp).coprime_iff_not_dvd.mp hCop.symm
  · by_cases hsq : s = q
    · subst s
      have hCop : u.Coprime q := Nat.Coprime.of_dvd_right (dvd_mul_left q p) huCop
      exact (hPrime q hq).coprime_iff_not_dvd.mp hCop.symm
    · exact huAvoid s (Finset.mem_erase.mpr ⟨hsq, Finset.mem_erase.mpr ⟨hsp, hs⟩⟩)

end Erdos319Sharp
