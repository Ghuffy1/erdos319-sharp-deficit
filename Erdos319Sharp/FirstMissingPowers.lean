import Erdos319Sharp.MissingDivisorMass

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def firstMissingPower (D p : ℕ) : ℕ := p ^ (D.factorization p + 1)

def firstMissingPowers (D N : ℕ) : Finset ℕ :=
  ((N.primesLE).filter (fun p => firstMissingPower D p ≤ N)).image (firstMissingPower D)

theorem mem_firstMissingPowers {D N q : ℕ} :
    q ∈ firstMissingPowers D N ↔ ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
      firstMissingPower D p ≤ N ∧ firstMissingPower D p = q := by
  simp only [firstMissingPowers, Finset.mem_image, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨p, ⟨⟨hpN, hp⟩, hPower⟩, hEq⟩
    exact ⟨p, hp, hpN, hPower, hEq⟩
  · rintro ⟨p, hp, hpN, hPower, hEq⟩
    exact ⟨p, ⟨⟨hpN, hp⟩, hPower⟩, hEq⟩

theorem firstMissingPower_ge (D p : ℕ) (hp : p.Prime) : p ≤ firstMissingPower D p := by
  have h := Nat.pow_le_pow_right hp.one_le (show 1 ≤ D.factorization p + 1 by omega)
  simpa only [pow_one, firstMissingPower] using h

theorem firstMissingPower_mem {D N p : ℕ} (hp : p.Prime)
    (hPower : firstMissingPower D p ≤ N) : firstMissingPower D p ∈ firstMissingPowers D N :=
  mem_firstMissingPowers.mpr ⟨p, hp, (firstMissingPower_ge D p hp).trans hPower, hPower, rfl⟩

theorem firstMissingPowers_conditions {D N : ℕ} (hD : D ≠ 0) :
    ∀ q ∈ firstMissingPowers D N, 0 < q ∧ q ≤ N ∧ ¬ q ∣ D := by
  intro q hq
  obtain ⟨p, hp, _, hPower, rfl⟩ := mem_firstMissingPowers.mp hq
  exact ⟨pow_pos hp.pos _, hPower, Nat.pow_succ_factorization_not_dvd hD hp⟩

theorem firstMissingPowers_pairwise_coprime (D N : ℕ) :
    ∀ q ∈ firstMissingPowers D N, ∀ r ∈ firstMissingPowers D N,
      q ≠ r → q.Coprime r := by
  intro q hq r hr hqr
  obtain ⟨p, hp, _, _, rfl⟩ := mem_firstMissingPowers.mp hq
  obtain ⟨s, hs, _, _, rfl⟩ := mem_firstMissingPowers.mp hr
  have hps : p ≠ s := by
    intro h
    subst s
    exact hqr rfl
  exact (((Nat.coprime_primes hp hs).mpr hps).pow_left _).pow_right _

theorem firstMissingPowers_avoid_lcm (F : Finset ℕ) (N : ℕ)
    (hPos : ∀ n ∈ F, 0 < n) :
    ∀ q ∈ firstMissingPowers (F.lcm id) N, ∀ n ∈ F, ¬ q ∣ n := by
  have hD : F.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos n hn).ne')
  intro q hq n hn hqn
  exact (firstMissingPowers_conditions hD q hq).2.2 (hqn.trans (Finset.dvd_lcm hn))

theorem firstMissingPowers_mass_bound (a δ : ℝ) (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4)
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 32) (N : ℕ) (hN : 0 < N) (F : Finset ℕ)
    (hF : F ⊆ Finset.Icc 1 N) (hLoss : ((tailInterval a N \ F).card : ℝ) ≤ δ * N) :
    (reciprocalSum (firstMissingPowers (F.lcm id) N) : ℝ) ≤ 32 * δ := by
  have hPos : ∀ n ∈ F, 0 < n := fun n hn => (Finset.mem_Icc.mp (hF hn)).1
  have hD : F.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos n hn).ne')
  apply missing_divisor_mass_small a δ ha haQuarter hδ hδSmall N hN
    (firstMissingPowers (F.lcm id) N) F
  · intro q hq
    exact ⟨(firstMissingPowers_conditions hD q hq).1, (firstMissingPowers_conditions hD q hq).2.1⟩
  · exact firstMissingPowers_pairwise_coprime _ _
  · exact firstMissingPowers_avoid_lcm F N hPos
  · exact hLoss

end Erdos319Sharp
