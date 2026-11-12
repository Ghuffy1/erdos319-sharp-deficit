import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Erdos319Sharp

/-- Complement symmetry rules out selecting only one of the two incident edges. -/
theorem path_vertex_residue {R : Type*} [CommRing R]
    {S : Set R} {s a x : R}
    (hcomplement : ∀ z ∈ S, s - z ∈ S)
    (havoid : -a ∉ S) (hx : x ∈ S)
    (incoming outgoing : Bool)
    (hzero : x + (if incoming then a else 0) +
      (if outgoing then -s - a else 0) = 0) :
    incoming = outgoing ∧ x = if incoming then s else 0 := by
  cases incoming <;> cases outgoing
  · simpa using hzero
  · change x + 0 + (-s - a) = 0 at hzero
    have hxsa : x = s + a := by linear_combination hzero
    have hnegative : -a ∈ S := by
      have hmember := hcomplement x hx
      have heq : s - x = -a := by rw [hxsa]; ring
      rwa [heq] at hmember
    exact (havoid hnegative).elim
  · change x + a + 0 = 0 at hzero
    have hxnegative : x = -a := by linear_combination hzero
    exact (havoid (hxnegative ▸ hx)).elim
  · refine ⟨rfl, ?_⟩
    change x = s
    change x + a + (-s - a) = 0 at hzero
    linear_combination hzero

/-- Adjacent equal edge indicators are constant on a finite path. -/
theorem path_edges_constant (edge : ℕ → Bool) (k : ℕ)
    (hstep : ∀ i, i + 1 < k → edge i = edge (i + 1)) :
    ∀ i, i < k → edge i = edge 0 := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      exact (hstep i hi).symm.trans (ih (Nat.lt_of_succ_lt hi))

theorem exists_avoided_residue {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) (hcard : S.card < q) :
    ∃ a : ZMod q, -a ∉ S := by
  classical
  have hnotall : ¬ ∀ z : ZMod q, z ∈ S := by
    intro hall
    have heq : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    have : q < q := by simpa only [heq, Finset.card_univ, ZMod.card] using hcard
    exact (lt_irrefl q) this
  obtain ⟨z, hz⟩ := not_forall.mp hnotall
  exact ⟨-z, by simpa using hz⟩

end Erdos319Sharp
