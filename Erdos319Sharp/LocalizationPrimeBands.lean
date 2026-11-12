import Erdos319Sharp.LocalizationScales

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem eventually_packet_prime_mass :
    ∀ᶠ N : ℕ in atTop,
      packetMediumBound N ≤ localizationRoughBound N ∧
        (1 / 10 : ℝ) * Real.log (Real.log N) ≤
          ∑ p ∈ primeBand (packetMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹ := by
  obtain ⟨B, hB, hError⟩ := exists_uniform_primeBand_error
  have hGap := (tendsto_loglog_linear_sub_log (1 / 10) 2 (Real.log 4 + 2)
    (by norm_num)).eventually (eventually_ge_atTop (0 : ℝ))
  filter_upwards [
    eventually_stretchedCutoff_loglog_bounds (4 / 5) 2 2 (by norm_num) (by norm_num),
    eventually_stretchedCutoff_loglog_bounds (3 / 5) 0 1 (by norm_num) (by norm_num),
    tendsto_packetMediumBound.eventually (eventually_ge_atTop B),
    tendsto_localizationRoughBound.eventually (eventually_ge_atTop 2),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ)), hGap]
    with N hYBounds hHBounds hHB hYTwo hLL hGapN
  have hYLower : (4 / 5 : ℝ) * Real.log (Real.log N) -
      2 * Real.log (Real.log (Real.log N)) - Real.log 4 ≤
        Real.log (Real.log (localizationRoughBound N)) := by
    simpa [stretchedCutoff, stretchedExponent, localizationRoughBound, localizationPower,
      show (2 : ℝ) * 2 = 4 by norm_num]
      using hYBounds.1
  have hHUpper : Real.log (Real.log (packetMediumBound N)) ≤
      (3 / 5 : ℝ) * Real.log (Real.log N) := by
    simpa [packetMediumBound] using hHBounds.2
  have hOrder : packetMediumBound N ≤ localizationRoughBound N :=
    nat_le_of_loglog_le (hB.trans hHB) hYTwo (by linarith)
  have hBandLower := (abs_le.mp (hError _ _ hHB hOrder)).1
  exact ⟨hOrder, by linarith⟩

theorem eventually_common_prime_mass :
    ∀ᶠ N : ℕ in atTop,
      localizationPrimeLower N ≤ packetCommonBound N ∧ packetCommonBound N ≤ N ∧
        (57 / 100 : ℝ) * Real.log (Real.log N) ≤
          ∑ p ∈ primeBand (localizationPrimeLower N) (packetCommonBound N), (p : ℝ)⁻¹ := by
  obtain ⟨B, hB, hError⟩ := exists_uniform_primeBand_error
  have hGap := (tendsto_loglog_linear_sub_log (3 / 100) 3
    (Real.log 32 + Real.log 2 + 2) (by norm_num)).eventually
      (eventually_ge_atTop (0 : ℝ))
  filter_upwards [
    eventually_stretchedCutoff_loglog_bounds (3 / 5) 2 16 (by norm_num) (by norm_num),
    tendsto_localizationPrimeLower.eventually (eventually_ge_atTop B),
    tendsto_packetCommonBound.eventually (eventually_ge_atTop 2),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ), hGap]
    with N hWBounds hZB hWTwo hL hLL hN hGapN
  have hWLower : (3 / 5 : ℝ) * Real.log (Real.log N) -
      2 * Real.log (Real.log (Real.log N)) - Real.log 32 ≤
        Real.log (Real.log (packetCommonBound N)) := by
    simpa [packetCommonBound, show (2 : ℝ) * 16 = 32 by norm_num] using hWBounds.1
  have hZUpper := (localizationPrimeLower_loglog_upper N hL hLL).2
  have hOrder : localizationPrimeLower N ≤ packetCommonBound N :=
    nat_le_of_loglog_le (hB.trans hZB) hWTwo (by linarith)
  have hAmbient : packetCommonBound N ≤ N := by
    exact stretchedCutoff_le_ambient (3 / 5) 2 16 N (by norm_num) (by norm_num) hN hL hLL
  have hBandLower := (abs_le.mp (hError _ _ hZB hOrder)).1
  exact ⟨hOrder, hAmbient, by linarith⟩

end Erdos319Sharp
