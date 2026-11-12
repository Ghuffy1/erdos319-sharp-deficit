import Erdos319Sharp.Target

set_option autoImplicit false

open Filter
open scoped Topology

noncomputable section

namespace Erdos319Sharp

/-- The normalized number of omissions for an arbitrary support size. -/
def normalizedOmissions (N k : ℕ) : ℝ :=
  ((N : ℝ) - k) * Real.log (Real.log (N : ℝ)) /
    ((N : ℝ) * Real.log (Real.log (Real.log (N : ℝ))))

/-- The construction obligation, quantified over every sufficiently large ambient size. -/
def SharpUpperWitnesses : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Primitive A ∧
      normalizedOmissions N A.card < Real.exp (-Real.eulerMascheroniConstant) + ε

/-- The lower bound obligation applies to every primitive support and signing. -/
def SharpLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Primitive A →
      Real.exp (-Real.eulerMascheroniConstant) - ε < normalizedOmissions N A.card

theorem normalizedOmissions_maxSize (N : ℕ) :
    normalizedOmissions N (maxSize N) = normalizedDeficit N := rfl

theorem normalizedOmissions_antitone {N : ℕ}
    (hlog : 0 ≤ Real.log (Real.log (N : ℝ)))
    (hden : 0 ≤ (N : ℝ) * Real.log (Real.log (Real.log (N : ℝ)))) :
    Antitone (normalizedOmissions N) := by
  intro j k hjk
  unfold normalizedOmissions
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_right _ hlog
  exact sub_le_sub_left (by exact_mod_cast hjk) _

theorem sharpAsymptotic_of_bounds
    (hupper : SharpUpperWitnesses) (hlower : SharpLowerBound) : SharpAsymptotic := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have heps : 0 < (Real.exp (-Real.eulerMascheroniConstant) - a) / 2 := by
      linarith
    filter_upwards [hlower _ heps] with N hN
    obtain ⟨A, hA, hprimitive, hcard⟩ := maxSize_attained N
    have hbound := hN A hA hprimitive
    rw [hcard, normalizedOmissions_maxSize] at hbound
    linarith
  · intro b hb
    have heps : 0 < (b - Real.exp (-Real.eulerMascheroniConstant)) / 2 := by
      linarith
    filter_upwards [hupper _ heps, eventually_positive_scale] with N hN hscale
    obtain ⟨A, hA, hprimitive, hbound⟩ := hN
    have hmono := normalizedOmissions_antitone hscale.2.1.le
      (mul_pos hscale.1 hscale.2.2).le (card_le_maxSize hA hprimitive)
    rw [normalizedOmissions_maxSize] at hmono
    linarith

theorem bounds_of_sharpAsymptotic (hsharp : SharpAsymptotic) :
    SharpUpperWitnesses ∧ SharpLowerBound := by
  constructor
  · intro ε hε
    have hbound := (tendsto_order.mp hsharp).2
      (Real.exp (-Real.eulerMascheroniConstant) + ε) (by linarith)
    filter_upwards [hbound] with N hN
    obtain ⟨A, hA, hprimitive, hcard⟩ := maxSize_attained N
    refine ⟨A, hA, hprimitive, ?_⟩
    simpa [hcard, normalizedOmissions_maxSize] using hN
  · intro ε hε
    have hbound := (tendsto_order.mp hsharp).1
      (Real.exp (-Real.eulerMascheroniConstant) - ε) (by linarith)
    filter_upwards [hbound, eventually_positive_scale] with N hN hscale
    intro A hA hprimitive
    have hmono := normalizedOmissions_antitone hscale.2.1.le
      (mul_pos hscale.1 hscale.2.2).le (card_le_maxSize hA hprimitive)
    rw [normalizedOmissions_maxSize] at hmono
    exact hN.trans_le hmono

theorem sharpAsymptotic_iff_bounds :
    SharpAsymptotic ↔ SharpUpperWitnesses ∧ SharpLowerBound :=
  ⟨bounds_of_sharpAsymptotic, fun h => sharpAsymptotic_of_bounds h.1 h.2⟩

end Erdos319Sharp
