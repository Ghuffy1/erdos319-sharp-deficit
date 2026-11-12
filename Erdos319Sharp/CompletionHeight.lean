import Erdos319Sharp.CompletionParameters
import Erdos319Sharp.PrimarySums

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem primaryHeight_reciprocalSum_le_real (A : Finset ℕ) (S : ℝ) (hS : 1 ≤ S)
    (hA : ∀ n ∈ A, n ≠ 0 ∧ (primaryHeight n : ℝ) ≤ S) :
    (primaryHeight (reciprocalSum A).den : ℝ) ≤ S := by
  have hNonneg : 0 ≤ S := le_trans (by norm_num) hS
  have hFloor : 1 ≤ ⌊S⌋₊ := (Nat.le_floor_iff hNonneg).mpr (by simpa using hS)
  have hBound := primaryHeight_reciprocalSum_le A ⌊S⌋₊ hFloor (by
    intro n hn
    exact ⟨(hA n hn).1, (Nat.le_floor_iff hNonneg).mpr (hA n hn).2⟩)
  exact (show (primaryHeight (reciprocalSum A).den : ℝ) ≤ (⌊S⌋₊ : ℕ) by
    exact_mod_cast hBound).trans (Nat.floor_le hNonneg)

theorem primaryHeight_sub_le_real (r s : ℚ) (S : ℝ) (hS : 1 ≤ S)
    (hr : (primaryHeight r.den : ℝ) ≤ S) (hs : (primaryHeight s.den : ℝ) ≤ S) :
    (primaryHeight (r - s).den : ℝ) ≤ S := by
  have hNonneg : 0 ≤ S := le_trans (by norm_num) hS
  have hBound := primaryHeight_sub_le r s ⌊S⌋₊
    ((Nat.le_floor_iff hNonneg).mpr hr) ((Nat.le_floor_iff hNonneg).mpr hs)
  exact (show (primaryHeight (r - s).den : ℝ) ≤ (⌊S⌋₊ : ℕ) by
    exact_mod_cast hBound).trans (Nat.floor_le hNonneg)

theorem eventually_construction_residual_height :
    ∀ᶠ N : ℕ in atTop, ∀ E F : Finset ℕ,
      (∀ n ∈ E, 0 < n ∧ (n : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ)) →
      (∀ n ∈ F, 0 < n ∧ PrimePowerSmooth (smoothCutoff 6 N) n) →
      (primaryHeight (reciprocalSum E - reciprocalSum F).den : ℝ) ≤
        (constructionBoundary N : ℝ) / (Real.log (constructionBoundary N)) ^ 14 := by
  filter_upwards [eventually_smoothCutoff_le_boundary_div_log,
    eventually_smoothCutoff_ge_rpow 6 (1 / 4) (by norm_num),
    (tendsto_smoothCutoff 6).eventually (eventually_ge_atTop (1 : ℝ))]
    with N hThreshold hPower hS E F hE hF
  have hPower' : (N : ℝ) ^ (3 / 4 : ℝ) ≤ smoothCutoff 6 N := by norm_num at hPower ⊢; exact hPower
  have hEHeight : (primaryHeight (reciprocalSum E).den : ℝ) ≤ smoothCutoff 6 N :=
    primaryHeight_reciprocalSum_le_real E _ hS (by
      intro n hn
      have h := hE n hn
      refine ⟨h.1.ne', ?_⟩
      exact (show (primaryHeight n : ℝ) ≤ n by exact_mod_cast primaryHeight_le_self n h.1.ne').trans
        (h.2.trans hPower'))
  have hFHeight : (primaryHeight (reciprocalSum F).den : ℝ) ≤ smoothCutoff 6 N :=
    primaryHeight_reciprocalSum_le_real F _ hS (by
      intro n hn
      exact ⟨(hF n hn).1.ne', primaryHeight_le_of_smooth n _ hS (hF n hn).2⟩)
  exact (primaryHeight_sub_le_real _ _ _ hS hEHeight hFHeight).trans hThreshold

end Erdos319Sharp
