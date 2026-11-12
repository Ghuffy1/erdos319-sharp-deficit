import Erdos319Sharp.BoundedCRT
import Erdos319Sharp.Residue

set_option autoImplicit false

open Finset

namespace Erdos319Sharp

theorem exists_bounded_pair_connector (p q : ℕ) (P : Finset ℕ)
    (hp : 2 ≤ p) (hq : 0 < q) (hpq : p.Coprime q)
    (rp : (ZMod p)ˣ) (rq : (ZMod q)ˣ)
    (hPositive : ∀ s ∈ P, 0 < s) (hCoprime : ∀ s ∈ P, s.Coprime (p * q))
    (hMass : (∑ s ∈ P, 1 / (s : ℝ)) ≤ 1 / 2) :
    ∃ u : ℕ, 0 < u ∧ u < 4 * (P.card + 1) * (p * q) ∧
      u.Coprime (p * q) ∧ (∀ s ∈ P, ¬ s ∣ u) ∧
      (((q * u : ℕ) : ZMod p)⁻¹ = (rp : ZMod p)) ∧
      (((p * u : ℕ) : ZMod q)⁻¹ = (rq : ZMod q)) := by
  have hpPos : 0 < p := by omega
  letI : NeZero p := ⟨hpPos.ne'⟩
  letI : NeZero q := ⟨hq.ne'⟩
  let cp : (ZMod p)ˣ := ZMod.unitOfCoprime q hpq.symm
  let cq : (ZMod q)ˣ := ZMod.unitOfCoprime p hpq
  let ap : (ZMod p)ˣ := cp⁻¹ * rp⁻¹
  let aq : (ZMod q)ˣ := cq⁻¹ * rq⁻¹
  obtain ⟨u, huPos, huBound, huModP, huModQ, huCop, huAvoid⟩ :=
    bounded_crt_avoiding_set p q (ap : ZMod p).val (aq : ZMod q).val P hp hq hpq
      (ZMod.val_coe_unit_coprime ap) (ZMod.val_coe_unit_coprime aq)
      hPositive hCoprime hMass
  have huP : (u : ZMod p) = (ap : ZMod p) :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).mpr huModP).trans (ZMod.natCast_zmod_val _)
  have huQ : (u : ZMod q) = (aq : ZMod q) :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).mpr huModQ).trans (ZMod.natCast_zmod_val _)
  have hProductP : ((q * u : ℕ) : ZMod p) = (rp⁻¹ : (ZMod p)ˣ) := by
    rw [Nat.cast_mul, huP]
    change (cp : ZMod p) * (ap : ZMod p) = (rp⁻¹ : (ZMod p)ˣ)
    rw [← Units.val_mul]
    congr 1
    simp only [ap, ← mul_assoc, mul_inv_cancel, one_mul]
  have hProductQ : ((p * u : ℕ) : ZMod q) = (rq⁻¹ : (ZMod q)ˣ) := by
    rw [Nat.cast_mul, huQ]
    change (cq : ZMod q) * (aq : ZMod q) = (rq⁻¹ : (ZMod q)ˣ)
    rw [← Units.val_mul]
    congr 1
    simp only [aq, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨u, huPos, huBound, huCop, huAvoid, ?_, ?_⟩
  · rw [hProductP, ZMod.inv_coe_unit, inv_inv]
  · rw [hProductQ, ZMod.inv_coe_unit, inv_inv]

end Erdos319Sharp
