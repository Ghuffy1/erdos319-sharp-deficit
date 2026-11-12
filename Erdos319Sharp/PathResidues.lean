import Erdos319Sharp.Residue
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

open Finset

namespace Erdos319Sharp

theorem exists_internal_path_residues (p : ℕ) (hp : p.Prime)
    (S : Finset (ZMod p)) (s : ZMod p) (hZero : 0 ∈ S) (hFull : s ∈ S)
    (hComplement : ∀ x ∈ S, s - x ∈ S) (hCard : S.card < p) :
    ∃ a b : (ZMod p)ˣ, (b : ZMod p) = -s - (a : ZMod p) ∧
      ∀ x ∈ S, ∀ incoming outgoing : Bool,
        x + (if incoming then (a : ZMod p) else 0) +
          (if outgoing then (b : ZMod p) else 0) = 0 →
        incoming = outgoing ∧ x = if incoming then s else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, hAvoid⟩ := exists_avoided_residue S hCard
  have ha : a ≠ 0 := by
    intro h
    exact hAvoid (by simpa only [h, neg_zero] using hZero)
  have hb : -s - a ≠ 0 := by
    intro h
    have hEq : -a = s := by linear_combination h
    exact hAvoid (hEq.symm ▸ hFull)
  refine ⟨Units.mk0 a ha, Units.mk0 (-s - a) hb, rfl, ?_⟩
  intro x hx incoming outgoing hSum
  exact path_vertex_residue (S := (S : Set (ZMod p))) hComplement hAvoid hx
    incoming outgoing hSum

end Erdos319Sharp
