import Erdos319Sharp.DenominatorExcess
import Erdos319Sharp.CompatiblePeeling

set_option autoImplicit false

open Finset

noncomputable section

namespace Erdos319Sharp

def excessGroup (D b : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun n => denominatorExcess D n = b)

def excessCofactors (D b : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (excessGroup D b A).image (fun n => n / excessScale D b)

theorem reciprocalSum_excessGroups (D N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    (∑ b ∈ Finset.Icc 1 N, reciprocalSum (excessGroup D b A)) = reciprocalSum A := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro n hn
  obtain ⟨hnPos, hnN⟩ := Finset.mem_Icc.mp (hA hn)
  exact Finset.mem_Icc.mpr ⟨denominatorExcess_pos D n hnPos,
    (Nat.div_le_self n (n.gcd D)).trans hnN⟩

theorem card_excessGroups (D N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    A.card = ∑ b ∈ Finset.Icc 1 N, (excessGroup D b A).card := by
  classical
  apply Finset.card_eq_sum_card_fiberwise
  intro n hn
  obtain ⟨hnPos, hnN⟩ := Finset.mem_Icc.mp (hA hn)
  exact Finset.mem_Icc.mpr ⟨denominatorExcess_pos D n hnPos,
    (Nat.div_le_self n (n.gcd D)).trans hnN⟩

theorem excessCofactors_divide_core (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hPos : ∀ n ∈ A, 0 < n) : ∀ m ∈ excessCofactors D b A, m ∣ coprimeCore D b := by
  intro m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hnA, hnExcess⟩ := Finset.mem_filter.mp hn
  exact excess_cofactor_dvd_core D n b hD (hPos n hnA).ne' hnExcess

theorem excessCofactors_positive (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hPos : ∀ n ∈ A, 0 < n) : ∀ m ∈ excessCofactors D b A, 0 < m := by
  intro m hm
  apply Nat.pos_of_ne_zero
  intro hmZero
  have hDiv := excessCofactors_divide_core D b A hD hPos m hm
  rw [hmZero, zero_dvd_iff] at hDiv
  exact coprimeCore_ne_zero D b hD hDiv

theorem excessCofactors_coprime (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hPos : ∀ n ∈ A, 0 < n) : ∀ m ∈ excessCofactors D b A, m.Coprime b := by
  intro m hm
  exact Nat.Coprime.of_dvd_left (excessCofactors_divide_core D b A hD hPos m hm)
    (coprimeCore_coprime D b hD)

theorem excessCofactors_card (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hPos : ∀ n ∈ A, 0 < n) : (excessCofactors D b A).card = (excessGroup D b A).card := by
  classical
  apply Finset.card_image_of_injOn
  intro n hn m hm hEqual
  obtain ⟨hnA, hnExcess⟩ := Finset.mem_filter.mp hn
  obtain ⟨hmA, hmExcess⟩ := Finset.mem_filter.mp hm
  have hnDiv := excessScale_dvd_of_excess D n b hD (hPos n hnA).ne' hnExcess
  have hmDiv := excessScale_dvd_of_excess D m b hD (hPos m hmA).ne' hmExcess
  calc
    n = excessScale D b * (n / excessScale D b) := (Nat.mul_div_cancel' hnDiv).symm
    _ = excessScale D b * (m / excessScale D b) := congrArg (fun k => excessScale D b * k) hEqual
    _ = m := Nat.mul_div_cancel' hmDiv

theorem excessCofactors_subset (D b N : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hA : A ⊆ Finset.Icc 1 N) :
    excessCofactors D b A ⊆ Finset.Icc 1 (N / excessScale D b) := by
  intro m hm
  have hmPos := excessCofactors_positive D b A hD (fun n hn => (Finset.mem_Icc.mp (hA hn)).1) m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hnN := (Finset.mem_Icc.mp (hA (Finset.mem_filter.mp hn).1)).2
  exact Finset.mem_Icc.mpr ⟨hmPos, Nat.div_le_div_right hnN⟩

theorem excessCofactors_image (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0)
    (hPos : ∀ n ∈ A, 0 < n) :
    (excessCofactors D b A).image (fun m => excessScale D b * m) = excessGroup D b A := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hkA, hkExcess⟩ := Finset.mem_filter.mp hk
    have hDiv := excessScale_dvd_of_excess D k b hD (hPos k hkA).ne' hkExcess
    rwa [Nat.mul_div_cancel' hDiv]
  · intro hn
    obtain ⟨hnA, hnExcess⟩ := Finset.mem_filter.mp hn
    have hDiv := excessScale_dvd_of_excess D n b hD (hPos n hnA).ne' hnExcess
    refine Finset.mem_image.mpr ⟨n / excessScale D b, ?_, Nat.mul_div_cancel' hDiv⟩
    exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨hnA, hnExcess⟩, rfl⟩

theorem excessGroup_reciprocalSum (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0) (hb : 0 < b)
    (hPos : ∀ n ∈ A, 0 < n) :
    reciprocalSum (excessGroup D b A) = reciprocalSum (excessCofactors D b A) / excessScale D b := by
  rw [← excessCofactors_image D b A hD hPos]
  exact reciprocalSum_mul_image _ _ (Nat.pos_of_ne_zero (excessScale_ne_zero D b hD hb.ne'))

theorem excessGroup_compatibility_iff (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0) (hb : 0 < b)
    (hPos : ∀ n ∈ A, 0 < n) :
    (reciprocalSum (excessGroup D b A)).den ∣ D ↔
      (∑ m ∈ excessCofactors D b A, (m : ZMod b)⁻¹) = 0 := by
  have hs : 0 < D / coprimeCore D b :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (coprimeCore_dvd D b))
      (Nat.pos_of_ne_zero (coprimeCore_ne_zero D b hD))
  have hBase : (D / coprimeCore D b) * coprimeCore D b = D :=
    Nat.div_mul_cancel (coprimeCore_dvd D b)
  have hImage : (excessCofactors D b A).image (fun m => (b * (D / coprimeCore D b)) * m) =
      excessGroup D b A := excessCofactors_image D b A hD hPos
  simpa only [hBase, hImage] using scaled_cofactor_compatibility_iff (excessCofactors D b A)
    (D / coprimeCore D b) (coprimeCore D b) b hs (coprimeCore_ne_zero D b hD) hb
    (coprimeCore_coprime D b hD) (excessCofactors_divide_core D b A hD hPos)

theorem excessCofactors_inverse_free (D b : ℕ) (A : Finset ℕ) (hD : D ≠ 0) (hb : 0 < b)
    (hPos : ∀ n ∈ A, 0 < n)
    (hObstruction : ∀ T ⊆ A, T.Nonempty → (reciprocalSum T).den ∣ D → 1 < reciprocalSum T) :
    InverseZeroSumFree b (excessCofactors D b A) := by
  classical
  by_contra hNotFree
  have hs : 0 < D / coprimeCore D b :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (coprimeCore_dvd D b))
      (Nat.pos_of_ne_zero (coprimeCore_ne_zero D b hD))
  obtain ⟨K, hKM, hKne, hKCard, hCompatible, hMass⟩ := small_inverse_zero_compatible_block
    (excessCofactors D b A) (D / coprimeCore D b) (coprimeCore D b) b
      hs (coprimeCore_ne_zero D b hD) hb (coprimeCore_coprime D b hD)
      (excessCofactors_divide_core D b A hD hPos) hNotFree
  let T := K.image (fun m => excessScale D b * m)
  have hTA : T ⊆ A := by
    intro n hn
    have hWhole : n ∈ (excessCofactors D b A).image (fun m => excessScale D b * m) :=
      Finset.image_subset_image hKM hn
    rw [excessCofactors_image D b A hD hPos] at hWhole
    exact (Finset.mem_filter.mp hWhole).1
  have hDen : (reciprocalSum T).den ∣ D := by
    simpa only [T, excessScale, Nat.div_mul_cancel (coprimeCore_dvd D b)] using hCompatible
  exact (not_lt_of_ge hMass) (hObstruction T hTA (hKne.image _) hDen)

end Erdos319Sharp
