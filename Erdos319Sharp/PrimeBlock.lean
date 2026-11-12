import Erdos319Sharp.PrimeFiber
import Mathlib.Data.Nat.MaxPrimeFac

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def primeBlockProduct (X : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 (2 * X)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹

theorem maxPrimeFac_cofactor_mul (n : ℕ) :
    n / n.maxPrimeFac * n.maxPrimeFac = n :=
  Nat.div_mul_cancel Nat.maxPrimeFac_dvd

/-- A largest-prime block is bounded by inverse coverage on each cofactor
fiber and the full Euler product over the permitted cofactor primes. -/
theorem eventually_prime_block_mass_bound :
    ∀ᶠ q : ℕ in atTop, ∀ (A : Finset ℕ) (X : ℕ),
      2 ≤ X → (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, X ≤ n.maxPrimeFac ∧ n.maxPrimeFac < 2 * X) →
      (reciprocalSum A : ℝ) ≤
        (primeInverseThreshold q (2 * X) + 1) / X * primeBlockProduct X := by
  classical
  filter_upwards [eventually_cofactor_prime_card_bound,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with q hCardBound hLL hq
  intro A X hX hCop hFree hBlock
  let f := fun n : ℕ => n / n.maxPrimeFac
  let P : Finset ℕ := (Finset.Icc 1 (2 * X)).filter Nat.Prime
  have hXPos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hNgt : ∀ n ∈ A, 1 < n := by
    intro n hn
    exact Nat.one_lt_maxPrimeFac_iff.mp (lt_of_lt_of_le (by omega : 1 < X) (hBlock n hn).1)
  have hFPos : ∀ n ∈ A, 0 < f n := by
    intro n hn
    have hnPos : 0 < n := lt_trans Nat.zero_lt_one (hNgt n hn)
    exact Nat.div_pos (Nat.le_of_dvd hnPos Nat.maxPrimeFac_dvd)
      (Nat.prime_maxPrimeFac_of_one_lt (hNgt n hn)).pos
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hFactored : ∀ n ∈ A, f n ∈ Nat.factoredNumbers P := by
    intro n hn
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpf
    have hpn : p ∣ n := hpf.trans (Nat.div_dvd_of_dvd Nat.maxPrimeFac_dvd)
    have hpMax : p ≤ n.maxPrimeFac :=
      Nat.le_maxPrimeFac (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hNgt n hn))) hp hpn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hp.one_le, hpMax.trans (hBlock n hn).2.le⟩, hp⟩
  have hC : 0 < primeBlockProduct X := by
    apply Finset.prod_pos
    intro p hp
    exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀
      (by exact_mod_cast (hP p hp).one_lt)))
  have hThreshold : 0 ≤ primeInverseThreshold q (2 * X) := by
    have hLog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
    unfold primeInverseThreshold
    positivity
  have hFiber : ∀ d ∈ A.image f,
      (d : ℝ) * (∑ n ∈ A.filter (fun n => f n = d), (n : ℝ)⁻¹) ≤
        (primeInverseThreshold q (2 * X) + 1) / X := by
    intro d hd
    obtain ⟨a, ha, had⟩ := Finset.mem_image.mp hd
    have hdPos : 0 < d := had ▸ hFPos a ha
    have hdReal : (0 : ℝ) < d := by exact_mod_cast hdPos
    let T := A.filter (fun n => f n = d)
    let M := T.image Nat.maxPrimeFac
    have hM : ∀ p ∈ M, (p : ℝ) < (2 : ℝ) * X ∧ p.Prime ∧ d * p ∈ A := by
      intro p hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hnA, hnd⟩ := Finset.mem_filter.mp hn
      refine ⟨by exact_mod_cast (hBlock n hnA).2,
        Nat.prime_maxPrimeFac_of_one_lt (hNgt n hnA), ?_⟩
      have hIdentity : d * n.maxPrimeFac = n := by
        rw [← hnd]
        exact maxPrimeFac_cofactor_mul n
      simpa only [hIdentity] using hnA
    have hMCard := hCardBound A M d (2 * X) hdPos (by exact_mod_cast (show 2 ≤ 2 * X by omega))
      hCop hFree hM
    have hInjective : Set.InjOn Nat.maxPrimeFac T := by
      intro n hn m hm heq
      have hnd := (Finset.mem_filter.mp hn).2
      have hmd := (Finset.mem_filter.mp hm).2
      calc
        n = f n * n.maxPrimeFac := (maxPrimeFac_cofactor_mul n).symm
        _ = d * n.maxPrimeFac := by rw [hnd]
        _ = d * m.maxPrimeFac := by rw [heq]
        _ = f m * m.maxPrimeFac := by rw [hmd]
        _ = m := maxPrimeFac_cofactor_mul m
    have hTCard : (T.card : ℝ) ≤ primeInverseThreshold q (2 * X) + 1 := by
      simpa only [M, Finset.card_image_of_injOn hInjective] using hMCard
    have hMin : ∀ n ∈ T, (d : ℝ) * X ≤ (n : ℝ) := by
      intro n hn
      obtain ⟨hnA, hnd⟩ := Finset.mem_filter.mp hn
      have hNat : d * X ≤ n := by
        calc
          d * X ≤ d * n.maxPrimeFac := Nat.mul_le_mul_left d (hBlock n hnA).1
          _ = n := by rw [← hnd]; exact maxPrimeFac_cofactor_mul n
      exact_mod_cast hNat
    have hMass := reciprocalSum_le_card_div_min T ((d : ℝ) * X) (mul_pos hdReal hXPos) hMin
    rw [reciprocalSum_real] at hMass
    simp only [one_div] at hMass
    calc
      (d : ℝ) * (∑ n ∈ T, (n : ℝ)⁻¹) ≤ (d : ℝ) * (T.card / ((d : ℝ) * X)) :=
        mul_le_mul_of_nonneg_left hMass hdReal.le
      _ = (T.card : ℝ) / X := by field_simp [hdReal.ne']
      _ ≤ (primeInverseThreshold q (2 * X) + 1) / X :=
        div_le_div_of_nonneg_right hTCard hXPos.le
  rw [reciprocalSum_eq_baseline, reciprocalSum_real]
  simp only [one_div]
  by_contra hMassBound
  have hLarge : (primeInverseThreshold q (2 * X) + 1) / X * primeBlockProduct X <
      ∑ n ∈ A, (n : ℝ)⁻¹ := lt_of_not_ge hMassBound
  have hTotal : 0 < ∑ n ∈ A, (n : ℝ)⁻¹ :=
    lt_trans (mul_pos (div_pos (by linarith) hXPos) hC) hLarge
  obtain ⟨d, hd, hBig⟩ := exists_factored_fiber_mass A P f (fun n => (n : ℝ)⁻¹)
    (∑ n ∈ A, (n : ℝ)⁻¹) hTotal hP hFactored
    (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)) le_rfl
  have hSmall := hBig.trans (hFiber d hd)
  have hFinal : (∑ n ∈ A, (n : ℝ)⁻¹) ≤
      (primeInverseThreshold q (2 * X) + 1) / X * primeBlockProduct X :=
    (div_le_iff₀ hC).mp hSmall
  exact (not_lt_of_ge hFinal) hLarge

end Erdos319Sharp
