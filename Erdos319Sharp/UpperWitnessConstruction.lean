import Erdos319Sharp.BulkApproximation
import Erdos319Sharp.CompletionHeight
import Erdos319Sharp.UpperAssembly

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

def constructionOmissionBound (N : ℕ) : ℝ :=
  constructionBoundary N + (N : ℝ) * (constructionTarget 1 N + 1 / constructionPrimeBase N) +
    (N : ℝ) * (Real.log N) ^ (-(1 / 10 : ℝ))

theorem eventually_primitive_construction :
    ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ Primitive A ∧
      (N : ℝ) - A.card ≤ constructionOmissionBound N := by
  obtain ⟨C, hComplete⟩ := eventually_quantitative_rational_completion (1 / 2) (by norm_num)
  have hBulkSmall := (tendsto_constructionBulkError 1).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hErrorSmall := ((tendsto_constructionCoreError 1).add (tendsto_constructionBulkError 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1))
  filter_upwards [eventually_exists_constructionCore_window 1 (by norm_num),
    eventually_constructionBulk_mass_approximation 1 (by norm_num),
    eventually_constructionBulk_omissions, eventually_construction_residual_height,
    eventually_construction_completion_primes C, tendsto_constructionBoundary.eventually hComplete,
    hBulkSmall, hErrorSmall] with N hCoreN hBulkN hOmitN hHeightN hPrimesN hCompleteN hBulkSmallN hErrorSmallN
  obtain ⟨P, E, hP, hPCard, hPLower, hPUpper, hCore, hE, hESmall, hELower, hEUpper⟩ := hCoreN
  let F := constructionBulk P N
  have hFInfo : ∀ n ∈ F,
      n ∈ integerTail (constructionBoundary N) N ∧ n.Coprime (P.prod id) ∧
        PrimePowerSmooth (smoothCutoff 6 N) n := by
    intro n hn
    exact mem_smoothCoprimeTail.mp hn
  have hFPositive : ∀ n ∈ F, 0 < n := by
    intro n hn
    have h := (Finset.mem_Icc.mp (hFInfo n hn).1).1
    omega
  have hFCoprime : ∀ n ∈ F, n.Coprime (P.prod id) := fun n hn => (hFInfo n hn).2.1
  have hFMass := hBulkN P hP hPUpper.le
  change |(reciprocalSum F : ℝ) - Real.log (constructionMass N)| ≤ constructionBulkError 1 N at hFMass
  obtain ⟨hFLower, hFUpper⟩ := abs_le.mp hFMass
  let r : ℚ := reciprocalSum E - reciprocalSum F
  have hrLower : (1 / 2 : ℝ) ≤ r := by
    change (1 / 2 : ℝ) ≤ ((reciprocalSum E - reciprocalSum F : ℚ) : ℝ)
    push_cast
    linarith
  have hrUpper : (r : ℝ) ≤ 2 := by
    change ((reciprocalSum E - reciprocalSum F : ℚ) : ℝ) ≤ 2
    push_cast
    linarith
  have hEDen : (reciprocalSum E).den.Coprime (P.prod id) := hCore.2.1
  have hrCoprime : r.den.Coprime (P.prod id) :=
    sub_den_coprime _ _ _ hEDen (reciprocalSum_den_coprime F _ hFCoprime)
  have hrHeight : (primaryHeight r.den : ℝ) ≤
      (constructionBoundary N : ℝ) / (Real.log (constructionBoundary N)) ^ 14 :=
    hHeightN E F (fun n hn => ⟨(hCore.1 n hn).1, hESmall n hn⟩)
      (fun n hn => ⟨hFPositive n hn, (hFInfo n hn).2.2⟩)
  obtain ⟨B, hB, hBCoprime, hBSum⟩ := hCompleteN r (P.prod id) hrLower hrUpper hrCoprime hrHeight
    (hPrimesN P hP)
  obtain ⟨A, hA, hPrimitive, hFSub, hFCard⟩ := primitive_of_core_bulk_completion
    (constructionBoundary_le N) hCore hE (fun n hn => (hFInfo n hn).1) hB hFCoprime hBCoprime hBSum
  refine ⟨A, hA, hPrimitive, ?_⟩
  have hCard : (F.card : ℝ) ≤ A.card := by exact_mod_cast hFCard
  have hOmit := hOmitN P hP
  change (N : ℝ) - F.card ≤ _ at hOmit
  have hRho := mul_le_mul_of_nonneg_left hPUpper.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  unfold constructionOmissionBound
  linarith

end Erdos319Sharp
