import Erdos319Sharp.ModularInverse
import Erdos319Sharp.ReciprocalResidues

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def primeInverseThreshold (q : ℕ) (B : ℝ) : ℝ :=
  200 * (B ^ (2 / 3 : ℝ) * Real.log q /
    Real.log (Real.log q) ^ (2 / 3 : ℝ))

theorem inverse_nat_mul_of_coprime (g p q : ℕ)
    (hg : g.Coprime q) (hp : p.Coprime q) :
    ((g * p : ℕ) : ZMod q)⁻¹ = (g : ZMod q)⁻¹ * (p : ZMod q)⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  rw [Nat.cast_mul]
  calc
    (g : ZMod q) * p * ((g : ZMod q)⁻¹ * (p : ZMod q)⁻¹) =
        ((g : ZMod q) * (g : ZMod q)⁻¹) * ((p : ZMod q) * (p : ZMod q)⁻¹) := by ring
    _ = 1 := by rw [ZMod.coe_mul_inv_eq_one g hg, ZMod.coe_mul_inv_eq_one p hp, one_mul]

theorem InverseZeroSumFree.of_mul_image {q g : ℕ} {A M : Finset ℕ}
    (hFree : InverseZeroSumFree q A) (hg : 0 < g) (hgCop : g.Coprime q)
    (hPCop : ∀ p ∈ M, p.Coprime q) (hImage : ∀ p ∈ M, g * p ∈ A) :
    InverseZeroSumFree q M := by
  classical
  intro T hTM hTne hZero
  let U := T.image (fun p => g * p)
  have hUA : U ⊆ A := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact hImage p (hTM hp)
  have hUne : U.Nonempty := hTne.image _
  have hSum : (∑ n ∈ U, (n : ZMod q)⁻¹) =
      (g : ZMod q)⁻¹ * ∑ p ∈ T, (p : ZMod q)⁻¹ := by
    rw [Finset.mul_sum]
    dsimp [U]
    rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hg hab)]
    exact Finset.sum_congr rfl (fun p hp => inverse_nat_mul_of_coprime g p q hgCop (hPCop p (hTM hp)))
  exact hFree U hUA hUne (by rw [hSum, hZero, mul_zero])

/-- Delete a pivot before applying inverse coverage so that the resulting zero
subsum is nonempty. -/
theorem eventually_prime_zero_free_card_bound :
    ∀ᶠ q : ℕ in atTop, ∀ (B : ℝ) (M : Finset ℕ),
      2 ≤ B → (∀ p ∈ M, (p : ℝ) < B ∧ p.Prime ∧ ¬ p ∣ q) →
      InverseZeroSumFree q M → (M.card : ℝ) ≤ primeInverseThreshold q B + 1 := by
  filter_upwards [eventually_prime_inverse_subset_sum,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with q hCover hLL hq
  intro B M hB hPrimes hFree
  have hLog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
  have hThreshold : 0 ≤ primeInverseThreshold q B := by
    unfold primeInverseThreshold
    positivity
  have hRoot : 1 ≤ Real.log (Real.log q) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hLL (by norm_num)
  have hSmall : 1 / Real.log (Real.log q) ^ (1 / 2 : ℝ) < B := by
    have hRootPos : 0 < Real.log (Real.log q) ^ (1 / 2 : ℝ) := by linarith
    have hInv : 1 / Real.log (Real.log q) ^ (1 / 2 : ℝ) ≤ 1 :=
      (div_le_one hRootPos).mpr hRoot
    linarith
  by_contra hBound
  have hLarge : primeInverseThreshold q B + 1 < (M.card : ℝ) := lt_of_not_ge hBound
  have hMne : M.Nonempty := Finset.card_pos.mp (by
    have h : (0 : ℝ) < M.card := by linarith
    exact_mod_cast h)
  obtain ⟨p, hp⟩ := hMne
  have hCard : ((M.erase p).card : ℝ) + 1 = M.card := by
    exact_mod_cast Finset.card_erase_add_one hp
  have hEraseLarge : primeInverseThreshold q B < ((M.erase p).card : ℝ) := by linarith
  obtain ⟨K, hKM, _, hKSum⟩ := hCover (M.erase p).card B (M.erase p) le_rfl
    (by linarith) hSmall hEraseLarge (fun r hr => hPrimes r (Finset.mem_of_mem_erase hr))
    (-(p : ZMod q)⁻¹)
  have hpK : p ∉ K := fun h => Finset.notMem_erase p M (hKM h)
  have hInsert : insert p K ⊆ M := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hp
    · exact Finset.mem_of_mem_erase (hKM hr)
  apply hFree (insert p K) hInsert (Finset.insert_nonempty _ _)
  rw [Finset.sum_insert hpK, hKSum, add_neg_cancel]

theorem eventually_cofactor_prime_card_bound :
    ∀ᶠ q : ℕ in atTop, ∀ (A M : Finset ℕ) (g : ℕ) (B : ℝ),
      0 < g → 2 ≤ B → (∀ n ∈ A, n.Coprime q) → InverseZeroSumFree q A →
      (∀ p ∈ M, (p : ℝ) < B ∧ p.Prime ∧ g * p ∈ A) →
      (M.card : ℝ) ≤ primeInverseThreshold q B + 1 := by
  filter_upwards [eventually_prime_zero_free_card_bound,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with q hBound hLL hq
  intro A M g B hg hB hCop hFree hM
  by_cases hMne : M.Nonempty
  · obtain ⟨p, hp⟩ := hMne
    have hgCop : g.Coprime q :=
      Nat.Coprime.of_dvd_left (dvd_mul_right g p) (hCop (g * p) (hM p hp).2.2)
    have hPCop : ∀ p ∈ M, p.Coprime q := fun p hp =>
      Nat.Coprime.of_dvd_left (dvd_mul_left p g) (hCop (g * p) (hM p hp).2.2)
    apply hBound B M hB
    · intro p hp
      exact ⟨(hM p hp).1, (hM p hp).2.1,
        ((hM p hp).2.1.coprime_iff_not_dvd).mp (hPCop p hp)⟩
    · exact hFree.of_mul_image hg hgCop hPCop (fun p hp => (hM p hp).2.2)
  · have hEmpty : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hMne
    have hLog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
    have hThreshold : 0 ≤ primeInverseThreshold q B := by
      unfold primeInverseThreshold
      positivity
    simp only [hEmpty, Finset.card_empty, Nat.cast_zero]
    linarith

end Erdos319Sharp
