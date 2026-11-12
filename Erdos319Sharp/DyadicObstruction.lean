import Erdos319Sharp.Regularization
import Erdos319Sharp.LcmLowerBound
import Erdos319Sharp.ModularTarget

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem dyadic_subset_prefix {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Ioc (N / 2) N) : A ⊆ Finset.Icc 1 N := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (hA hn)
  exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩

theorem dyadic_minimum {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Ioc (N / 2) N) : ∀ n ∈ A, (1 / 2 : ℝ) * N ≤ n := by
  intro n hn
  have h := (Finset.mem_Ioc.mp (hA hn)).1
  have hNat : N ≤ 2 * n := by omega
  have hReal : (N : ℝ) ≤ 2 * n := by exact_mod_cast hNat
  linarith

theorem dyadic_reciprocal_mass_le_one {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Ioc (N / 2) N) : (reciprocalSum A : ℝ) ≤ 1 := by
  have hM : (0 : ℝ) < (N / 2 + 1 : ℕ) := by positivity
  have hMin : ∀ n ∈ A, ((N / 2 + 1 : ℕ) : ℝ) ≤ n := by
    intro n hn
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_Ioc.mp (hA hn)).1
  have hCard : A.card ≤ N / 2 + 1 := by
    have h := (Finset.card_le_card hA).trans_eq (Nat.card_Ioc (N / 2) N)
    omega
  rw [reciprocalSum_eq_baseline]
  exact (reciprocalSum_le_card_div_min A _ hM hMin).trans
    ((div_le_one hM).mpr (by exact_mod_cast hCard))

/-- Regular positive-density dyadic sets with fine modular mesh contain a zero. -/
theorem eventually_regular_dyadic_modular_obstruction (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (q : ℕ),
      A ⊆ Finset.Ioc (N / 2) N → RegularSet N A →
      (β / 2) * N ≤ (A.card : ℝ) → 0 < q →
      (∀ n ∈ A, n.Coprime q) →
      (q : ℝ) / (A.lcm id : ℕ) ≤ β / 8 → ¬ InverseZeroSumFree q A := by
  filter_upwards [eventually_uniform_dyadic_target (1 / 2) β (by norm_num)
    (by norm_num) hβ, eventually_gt_atTop (0 : ℕ)] with N hExact hN
  intro A q hA hRegular hCard hq hCop hMesh hFree
  have hD : 0 < A.lcm id := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun n hn =>
      (show 0 < n from (Finset.mem_Icc.mp (hRegular.1 hn)).1).ne'))
  obtain ⟨x, hx, hqx, hrLo, hrHi⟩ :=
    exists_positive_modular_target q (A.lcm id) β hq hD hβ hMesh
  have hMass : β / 2 ≤ (reciprocalSum A : ℝ) := by
    have hBound := card_le_N_mul_reciprocalSum hRegular.1
    rw [← reciprocalSum_eq_baseline] at hBound
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    apply (mul_le_mul_iff_of_pos_right hNR).mp
    simpa only [mul_comm] using hCard.trans hBound
  obtain ⟨B, hBA, hBsum⟩ := hExact A hRegular.1 (dyadic_minimum hA)
    hRegular.2.1 hRegular.2.2.1 hRegular.2.2.2 hCard hMass
    (dyadic_reciprocal_mass_le_one hA) ((x : ℚ) / (A.lcm id)) hrLo hrHi
    (nat_quotient_den_dvd x (A.lcm id))
  have hBne : B.Nonempty := by
    by_contra hEmpty
    have hB : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hPos : (0 : ℚ) < (x : ℚ) / (A.lcm id) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hD)
    simp [hB, reciprocalSum] at hBsum
    linarith
  exact hFree.no_rational_target hBA hBne hD (lcm_coprime_of_members A q hCop)
    (fun n hn => Finset.dvd_lcm (hBA hn)) hBsum hqx

/-- Large-prime elements of an inverse-zero-free set have vanishing dyadic density,
uniformly over every integer dyadic scale above the logarithm of the modulus. -/
theorem eventually_sparse_large_prime_dyadic (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ q : ℕ in atTop, ∀ (N : ℕ) (A : Finset ℕ),
      Real.log q ≤ (N : ℝ) → A ⊆ Finset.Ioc (N / 2) N →
      (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ n ∈ A, ∃ p : ℕ, p.Prime ∧ Real.log q ≤ (p : ℝ) ∧ p ∣ n) →
      (A.card : ℝ) < β * N := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    ((eventually_dense_regular_subset (1 / 2) β (by norm_num) hβ).and
      (eventually_regular_dyadic_modular_obstruction β hβ))
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (max (K : ℝ) 2)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (4 / β)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (8 / β)),
    eventually_gt_atTop (1 : ℕ)] with q hLog hLogLog hqLarge hq
  intro N A hScale hA hCop hFree hLarge
  by_contra hSmall
  have hCard : β * N ≤ (A.card : ℝ) := le_of_not_gt hSmall
  have hNK : K ≤ N := by
    have h : (K : ℝ) ≤ N := (le_max_left _ _).trans (hLog.trans hScale)
    exact_mod_cast h
  have hN : 0 < N := by
    have h : (2 : ℝ) ≤ N := (le_max_right _ _).trans (hLog.trans hScale)
    have hNat : 2 ≤ N := by exact_mod_cast h
    omega
  obtain ⟨F, hFA, hRegular, hFCard⟩ := (hK N hNK).1 A
    (dyadic_subset_prefix hA) (dyadic_minimum hA) hCard
  have hF : F ⊆ Finset.Ioc (N / 2) N := hFA.trans hA
  have hD : 0 < F.lcm id := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun n hn =>
      (show 0 < n from (Finset.mem_Icc.mp (hRegular.1 hn)).1).ne'))
  have hL : 1 < Real.log q := by
    have h := (le_max_right (K : ℝ) 2).trans hLog
    linarith
  have hLower := log_lcm_lower_bound_of_large_prime_cover N F (Real.log q) (β / 2)
    hN hRegular.1 hL hFCard (fun n hn => hLarge n (hFA hn))
  have hCoefficient : 2 ≤ (β / 2) * Real.log (Real.log q) := by
    have h := (div_le_iff₀ hβ).mp hLogLog
    nlinarith
  have hLogD : 2 * Real.log q ≤ Real.log (F.lcm id : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hCoefficient (by linarith : 0 ≤ Real.log q)
    nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hDR : (0 : ℝ) < (F.lcm id : ℕ) := by exact_mod_cast hD
  have hSquare : (q : ℝ) ^ 2 ≤ (F.lcm id : ℕ) := by
    apply (Real.log_le_log_iff (sq_pos_of_pos hqR) hDR).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hLogD
  have hMesh : (q : ℝ) / (F.lcm id : ℕ) ≤ β / 8 := by
    have hFirst : (q : ℝ) / (F.lcm id : ℕ) ≤ (q : ℝ) / (q : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hqR.le (sq_pos_of_pos hqR) hSquare
    have hSecond : (1 : ℝ) / q ≤ β / 8 := by
      have h := (div_le_iff₀ hβ).mp hqLarge
      apply (div_le_iff₀ hqR).mpr
      nlinarith
    have hCancel : (q : ℝ) / (q : ℝ) ^ 2 = 1 / q := by field_simp
    calc
      (q : ℝ) / (F.lcm id : ℕ) ≤ (q : ℝ) / (q : ℝ) ^ 2 := hFirst
      _ = 1 / q := hCancel
      _ ≤ β / 8 := hSecond
  exact (hK N hNK).2 F q hF hRegular hFCard (by omega)
    (fun n hn => hCop n (hFA hn)) hMesh (ZeroSumFree.mono hFree hFA)

end Erdos319Sharp
