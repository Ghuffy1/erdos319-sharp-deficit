import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finsupp.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section

namespace Erdos319Sharp

def denominatorExcess (D n : ℕ) : ℕ := n / n.gcd D

def coprimeCore (D b : ℕ) : ℕ :=
  (D.factorization.filter (fun p => ¬p ∣ b)).prod (fun p k => p ^ k)

def excessScale (D b : ℕ) : ℕ := b * (D / coprimeCore D b)

theorem denominatorExcess_pos (D n : ℕ) (hn : 0 < n) : 0 < denominatorExcess D n := by
  exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left n D)) (Nat.gcd_pos_of_pos_left D hn)

theorem denominatorExcess_factorization (D n : ℕ) (hD : D ≠ 0) (hn : n ≠ 0) :
    (denominatorExcess D n).factorization = n.factorization - D.factorization := by
  rw [denominatorExcess, Nat.factorization_div (Nat.gcd_dvd_left n D), Nat.factorization_gcd hn hD]
  ext p
  change n.factorization p - min (n.factorization p) (D.factorization p) =
    n.factorization p - D.factorization p
  omega

theorem coprimeCore_filter_le (D b : ℕ) :
    D.factorization.filter (fun p => ¬p ∣ b) ≤ D.factorization := by
  intro p
  rw [Finsupp.filter_apply]
  split_ifs <;> omega

theorem coprimeCore_dvd (D b : ℕ) : coprimeCore D b ∣ D :=
  Nat.prod_pow_dvd_of_le_factorization (coprimeCore_filter_le D b)

theorem coprimeCore_factorization (D b : ℕ) :
    (coprimeCore D b).factorization = D.factorization.filter (fun p => ¬p ∣ b) :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (coprimeCore_filter_le D b)

theorem coprimeCore_ne_zero (D b : ℕ) (hD : D ≠ 0) : coprimeCore D b ≠ 0 := by
  intro hZero
  have h := coprimeCore_dvd D b
  rw [hZero, zero_dvd_iff] at h
  exact hD h

theorem coprimeCore_coprime (D b : ℕ) (hD : D ≠ 0) : (coprimeCore D b).Coprime b := by
  apply Nat.coprime_of_dvd
  intro p hp hpCore hpb
  have hPositive := hp.factorization_pos_of_dvd (coprimeCore_ne_zero D b hD) hpCore
  rw [coprimeCore_factorization] at hPositive
  simpa [Finsupp.filter_apply, hpb] using hPositive

theorem excessScale_ne_zero (D b : ℕ) (hD : D ≠ 0) (hb : b ≠ 0) : excessScale D b ≠ 0 := by
  unfold excessScale
  apply Nat.mul_ne_zero hb
  exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (coprimeCore_dvd D b))
    (Nat.pos_of_ne_zero (coprimeCore_ne_zero D b hD))).ne'

theorem excessScale_factorization (D b p : ℕ) (hD : D ≠ 0) (hb : b ≠ 0) :
    (excessScale D b).factorization p =
      b.factorization p + if p ∣ b then D.factorization p else 0 := by
  have hQuotient : D / coprimeCore D b ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (coprimeCore_dvd D b))
      (Nat.pos_of_ne_zero (coprimeCore_ne_zero D b hD))).ne'
  rw [excessScale, Nat.factorization_mul hb hQuotient,
    Nat.factorization_div (coprimeCore_dvd D b), coprimeCore_factorization]
  change b.factorization p + (D.factorization p -
    (D.factorization.filter (fun q => ¬q ∣ b)) p) = _
  by_cases hpb : p ∣ b <;> simp [Finsupp.filter_apply, hpb]

theorem factorization_eq_add_of_dvd_excess (D n b p : ℕ) (hD : D ≠ 0) (hn : n ≠ 0)
    (hExcess : denominatorExcess D n = b) (hp : p.Prime) (hpb : p ∣ b) :
    n.factorization p = D.factorization p + b.factorization p := by
  have hb : b ≠ 0 := by rw [← hExcess]; exact (denominatorExcess_pos D n (Nat.pos_of_ne_zero hn)).ne'
  have hPositive := hp.factorization_pos_of_dvd hb hpb
  have hExponent := congrArg (fun f : ℕ →₀ ℕ => f p) (denominatorExcess_factorization D n hD hn)
  rw [hExcess] at hExponent
  change b.factorization p = n.factorization p - D.factorization p at hExponent
  omega

theorem excessScale_dvd_of_excess (D n b : ℕ) (hD : D ≠ 0) (hn : n ≠ 0)
    (hExcess : denominatorExcess D n = b) : excessScale D b ∣ n := by
  have hb : b ≠ 0 := by rw [← hExcess]; exact (denominatorExcess_pos D n (Nat.pos_of_ne_zero hn)).ne'
  apply (Nat.factorization_le_iff_dvd (excessScale_ne_zero D b hD hb) hn).mp
  intro p
  rw [excessScale_factorization D b p hD hb]
  by_cases hpb : p ∣ b
  · rw [if_pos hpb]
    by_cases hp : p.Prime
    · rw [factorization_eq_add_of_dvd_excess D n b p hD hn hExcess hp hpb]
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · simp [hpb, Nat.factorization_eq_zero_of_not_dvd hpb]

theorem excess_cofactor_dvd_core (D n b : ℕ) (hD : D ≠ 0) (hn : n ≠ 0)
    (hExcess : denominatorExcess D n = b) : n / excessScale D b ∣ coprimeCore D b := by
  have hb : b ≠ 0 := by rw [← hExcess]; exact (denominatorExcess_pos D n (Nat.pos_of_ne_zero hn)).ne'
  have hScale := excessScale_dvd_of_excess D n b hD hn hExcess
  have hScalePos := Nat.pos_of_ne_zero (excessScale_ne_zero D b hD hb)
  have hQuotient : n / excessScale D b ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hScale) hScalePos).ne'
  apply (Nat.factorization_le_iff_dvd hQuotient (coprimeCore_ne_zero D b hD)).mp
  intro p
  rw [Nat.factorization_div hScale, coprimeCore_factorization]
  change n.factorization p - (excessScale D b).factorization p ≤
    (D.factorization.filter (fun q => ¬q ∣ b)) p
  rw [excessScale_factorization D b p hD hb, Finsupp.filter_apply]
  by_cases hpb : p ∣ b
  · simp only [hpb, ite_true, not_true_eq_false, ite_false]
    by_cases hp : p.Prime
    · rw [factorization_eq_add_of_dvd_excess D n b p hD hn hExcess hp hpb]
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · have hExponent := congrArg (fun f : ℕ →₀ ℕ => f p) (denominatorExcess_factorization D n hD hn)
    rw [hExcess] at hExponent
    change b.factorization p = n.factorization p - D.factorization p at hExponent
    have hbZero := Nat.factorization_eq_zero_of_not_dvd hpb
    simp only [hpb, ite_false, not_false_eq_true, ite_true, hbZero, zero_add]
    omega

theorem denominatorExcess_decomposition (D n b : ℕ) (hD : D ≠ 0) (hn : 0 < n)
    (hExcess : denominatorExcess D n = b) :
    n = excessScale D b * (n / excessScale D b) ∧
      n / excessScale D b ∣ coprimeCore D b ∧ (n / excessScale D b).Coprime b := by
  have hDiv := excessScale_dvd_of_excess D n b hD hn.ne' hExcess
  have hCore := excess_cofactor_dvd_core D n b hD hn.ne' hExcess
  exact ⟨(Nat.mul_div_cancel' hDiv).symm, hCore,
    Nat.Coprime.of_dvd_left hCore (coprimeCore_coprime D b hD)⟩

end Erdos319Sharp
