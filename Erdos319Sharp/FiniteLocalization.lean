import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

/-- A finite localization criterion with a variable fiber mass. The two
prime bands and all their numerical sieve estimates are explicit inputs. -/
theorem divisor_localization_of_sieve_bounds
    (A D P Q : Finset ℕ) (N Y H W Z s t u : ℕ) (c η K δ : ℝ) (h : ℤ)
    (hN : 0 < N) (hc : 0 < c) (hη : 0 < η) (hK : 0 < K)
    (hY : 1 ≤ Y) (hYN : Y ≤ N) (hH : 1 ≤ H) (hW : 1 ≤ W) (hZ : 1 ≤ Z)
    (hδ : 0 < δ)
    (hDensity : δ ≤ c * (η / (4 * (partial_euler_product N / partial_euler_product Y))))
    (hA : A ⊆ Finset.Icc 1 N) (hMin : ∀ n ∈ A, c * N ≤ (n : ℝ))
    (hMult : ∀ n ∈ A, primePowerMultiplicity N n ≤ t)
    (hP : ∀ p ∈ P, p.Prime ∧ H ≤ p ∧ p ≤ Y)
    (hQ : ∀ p ∈ Q, p.Prime ∧ Z ≤ p ∧ p ≤ W)
    (hWidth : K * (Y : ℝ) ^ t ≤ c * N)
    (hClose : K ≤ (Z ^ Z : ℕ))
    (hTail : Real.exp (2 * ∑ p ∈ Q, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * u) ≤ δ / 4)
    (hCount : (W : ℝ) ^ (2 * u) ≤ δ * H / 4)
    (hPrimeMass : 1 ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) - 2 * Real.log (2 / δ))
    (hD : ∀ q ∈ D, 0 < q ∧
      η ≤ (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ) ∧
      (q : ℝ) * (((A.filter (fun n => q ∣ n)).filter
        (fun n => K / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ) / (c * N) ≤ η / 2)
    (hBudget : ∀ q ∈ D,
      (N : ℝ) / (c * N) * (Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
        Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * s)) +
        (q : ℝ) / (c * N) * (Y : ℝ) ^ (2 * s) ≤ η / 4) :
    ∃ x : ℤ, |(x : ℝ) - h| < K / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ x := by
  apply common_nearby_multiple_of_dense_packets D Q H W u Z δ K h hH hW hZ
    hδ hK hClose hQ hTail hCount hPrimeMass
  intro q hq
  obtain ⟨hqPos, hMass, hBad⟩ := hD q hq
  let Aq := A.filter (fun n => q ∣ n)
  let G := Aq.filter (fun n => |((h : ZMod n).valMinAbs : ℝ)| < K / 2)
  have hGsub : G ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hM : 0 < c * (N : ℝ) := mul_pos hc (by exact_mod_cast hN)
  have hGoodMass := good_residue_mass Aq q h (c * N) K η hM
    (fun n hn => hMin n (Finset.mem_filter.mp hn).1) hMass hBad
  have hGoodDiv : ∀ n ∈ G, q ∣ n := by
    intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hBudget' : (N : ℝ) / (c * N) * (Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
      Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * s)) +
      (q : ℝ) / (c * N) * (Y : ℝ) ^ (2 * s) ≤ (η / 2) / 2 := by
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hBudget q hq
  obtain ⟨J, T, x, hHJ, hT, hDense, hx, hqx, hTx⟩ :=
    extract_nearby_dense_cofactor_packet G P N Y H q s t c (η / 2) K h
      hN hqPos hc (half_pos hη) hY hYN (hGsub.trans hA)
      (fun n hn => hMin n (hGsub hn)) hGoodDiv
      (fun n hn => hMult n (hGsub hn)) hP hGoodMass
      (fun n hn => (Finset.mem_filter.mp hn).2) hWidth hBudget'
  refine ⟨J, T, x, hHJ, hT, ?_, hx, hqx, hTx⟩
  apply le_trans _ hDense
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg J)
  convert hDensity using 1 <;> ring

end Erdos319Sharp
