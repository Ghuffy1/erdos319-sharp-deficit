import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

theorem primePowerMultiplicity_eq_cardFactors (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    primePowerMultiplicity N n = ArithmeticFunction.cardFactors n := by
  classical
  let T := fun p : ℕ => (Finset.Icc 1 (n.factorization p)).image (fun a => p ^ a)
  let S := ((Finset.Icc 1 N).filter IsPrimePow).filter (fun q => q ∣ n)
  have hSub : S ⊆ n.primeFactors.biUnion T := by
    intro q hq
    obtain ⟨hqPP, hqn⟩ := Finset.mem_filter.mp hq
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff q).mp (Finset.mem_filter.mp hqPP).2
    have hpDiv : p ∣ n :=
      (show p ∣ p ^ a from by simpa only [pow_one] using pow_dvd_pow p ha).trans hqn
    have hpMem : p ∈ n.primeFactors := hp.mem_primeFactors hpDiv hn.ne'
    have haLe : a ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn.ne').mp hqn
    exact Finset.mem_biUnion.mpr ⟨p, hpMem,
      Finset.mem_image.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha, haLe⟩, rfl⟩⟩
  have hCard : (n.primeFactors.biUnion T).card ≤ ∑ p ∈ n.primeFactors, n.factorization p := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro p hp
    dsimp [T]
    simpa using (Finset.card_image_le :
      ((Finset.Icc 1 (n.factorization p)).image (fun a => p ^ a)).card ≤
        (Finset.Icc 1 (n.factorization p)).card)
  have hOmega : ArithmeticFunction.cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    simp only [Finsupp.sum, Nat.support_factorization]
  apply Nat.le_antisymm
  · change S.card ≤ ArithmeticFunction.cardFactors n
    rw [hOmega]
    exact (Finset.card_le_card hSub).trans hCard
  · rw [ArithmeticFunction.cardFactors_apply]
    exact primeFactor_length_le_primePowerMultiplicity N n hn hnN

end Erdos319Sharp
