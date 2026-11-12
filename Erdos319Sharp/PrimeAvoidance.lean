import Erdos319Sharp.Baseline

set_option autoImplicit false

open Finset Erdos319Formal

noncomputable section

namespace Erdos319Sharp

def primeAvoidanceDensity (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (1 : ℝ) / p)

def primeAvoiders (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)

def primeHitBoth (P Q : Finset ℕ) (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N \ (primeAvoiders P N ∪ primeAvoiders Q N)

theorem primeAvoidanceDensity_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    primeAvoidanceDensity P = coprimeDensity (P.prod id) :=
  (coprimeDensity_primeProduct P hP).symm

theorem primeAvoidanceDensity_pos_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < primeAvoidanceDensity P ∧ primeAvoidanceDensity P ≤ 1 := by
  have hProd : 0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)
  rw [primeAvoidanceDensity_eq P hP]
  exact ⟨coprimeDensity_pos hProd, coprimeDensity_le_one hProd⟩

theorem primeAvoidanceDensity_lt_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPne : P.Nonempty) : primeAvoidanceDensity P < 1 := by
  have hProd : 0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)
  obtain ⟨p, hp⟩ := hPne
  have hpLe : p ≤ P.prod id := Nat.le_of_dvd hProd (Finset.dvd_prod_of_mem id hp)
  have hProdOne : 1 < P.prod id := (hP p hp).one_lt.trans_le hpLe
  rw [primeAvoidanceDensity_eq P hP, coprimeDensity]
  apply (div_lt_one (by exact_mod_cast hProd)).mpr
  exact_mod_cast Nat.totient_lt (P.prod id) hProdOne

theorem primeAvoiders_eq_coprimePrefix (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    primeAvoiders P N = coprimePrefix (P.prod id) N := by
  have hRange : Finset.Icc 1 N = Finset.Ico 1 (1 + N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  unfold primeAvoiders coprimePrefix
  rw [hRange]
  apply Finset.filter_congr
  intro n hn
  constructor
  · intro h
    exact Nat.coprime_prod_left_iff.mpr (fun p hp => ((hP p hp).coprime_iff_not_dvd).mpr (h p hp))
  · intro h p hp
    exact ((hP p hp).coprime_iff_not_dvd).mp (Nat.coprime_prod_left_iff.mp h p hp)

theorem primeAvoiders_card_error (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    |(primeAvoiders P N).card - primeAvoidanceDensity P * (N : ℝ)| ≤ (P.prod id : ℕ) := by
  have hProd : 0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)
  rw [primeAvoiders_eq_coprimePrefix P N hP, primeAvoidanceDensity_eq P hP]
  exact (coprimePrefix_card_error (P.prod id) N hProd).trans (by exact_mod_cast Nat.totient_le (P.prod id))

theorem primeAvoidanceDensity_union (P Q : Finset ℕ) (hPQ : Disjoint P Q) :
    primeAvoidanceDensity (P ∪ Q) = primeAvoidanceDensity P * primeAvoidanceDensity Q := by
  unfold primeAvoidanceDensity
  exact Finset.prod_union hPQ

theorem primeAvoiders_union (P Q : Finset ℕ) (N : ℕ) :
    primeAvoiders (P ∪ Q) N = primeAvoiders P N ∩ primeAvoiders Q N := by
  ext n
  simp only [primeAvoiders, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨⟨hn, fun p hp => h p (Finset.mem_union_left Q hp)⟩,
      ⟨hn, fun p hp => h p (Finset.mem_union_right P hp)⟩⟩
  · rintro ⟨⟨hn, hP⟩, ⟨_, hQ⟩⟩
    refine ⟨hn, ?_⟩
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hQ p hp

theorem mem_primeHitBoth {P Q : Finset ℕ} {N n : ℕ} :
    n ∈ primeHitBoth P Q N ↔ n ∈ Finset.Icc 1 N ∧
      (∃ p ∈ P, p ∣ n) ∧ (∃ p ∈ Q, p ∣ n) := by
  classical
  simp only [primeHitBoth, primeAvoiders, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hNot⟩
    have hP : ¬ ∀ p ∈ P, ¬ p ∣ n := fun h => hNot (Or.inl ⟨hn, h⟩)
    have hQ : ¬ ∀ p ∈ Q, ¬ p ∣ n := fun h => hNot (Or.inr ⟨hn, h⟩)
    push_neg at hP hQ
    exact ⟨hn, hP, hQ⟩
  · rintro ⟨hn, ⟨p, hp, hpn⟩, ⟨q, hq, hqn⟩⟩
    refine ⟨hn, ?_⟩
    rintro (hP | hQ)
    · exact hP.2 p hp hpn
    · exact hQ.2 q hq hqn

theorem primeHitBoth_card_identity (P Q : Finset ℕ) (N : ℕ) :
    ((primeHitBoth P Q N).card : ℝ) + (primeAvoiders P N).card + (primeAvoiders Q N).card =
      N + (primeAvoiders (P ∪ Q) N).card := by
  have hSub : primeAvoiders P N ∪ primeAvoiders Q N ⊆ Finset.Icc 1 N :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hDiff := Finset.card_sdiff_add_card_eq_card hSub
  have hUnion := Finset.card_union_add_card_inter (primeAvoiders P N) (primeAvoiders Q N)
  rw [← primeAvoiders_union] at hUnion
  have hN : (Finset.Icc 1 N).card = N := by simp
  change (primeHitBoth P Q N).card + _ = _ at hDiff
  rw [hN] at hDiff
  have h : (primeHitBoth P Q N).card + (primeAvoiders P N).card + (primeAvoiders Q N).card =
      N + (primeAvoiders (P ∪ Q) N).card := by omega
  exact_mod_cast h

theorem primeHitBoth_card_lower (P Q : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint P Q) :
    (N : ℝ) * (1 - primeAvoidanceDensity P) * (1 - primeAvoidanceDensity Q) ≤
      (primeHitBoth P Q N).card + 3 * ((P ∪ Q).prod id : ℕ) := by
  have hUnionPrime : ∀ p ∈ P ∪ Q, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hQ p hp
  have hEP := (abs_le.mp (primeAvoiders_card_error P N hP)).2
  have hEQ := (abs_le.mp (primeAvoiders_card_error Q N hQ)).2
  have hEU := (abs_le.mp (primeAvoiders_card_error (P ∪ Q) N hUnionPrime)).1
  rw [primeAvoidanceDensity_union P Q hPQ] at hEU
  have hIdentity := primeHitBoth_card_identity P Q N
  have hProdP : 0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hProdQ : 0 < Q.prod id := Finset.prod_pos (fun p hp => (hQ p hp).pos)
  have hPeriod : (P ∪ Q).prod id = P.prod id * Q.prod id := Finset.prod_union hPQ
  have hDP : ((P.prod id : ℕ) : ℝ) ≤ ((P ∪ Q).prod id : ℕ) := by
    exact_mod_cast (show P.prod id ≤ (P ∪ Q).prod id by
      rw [hPeriod]
      exact Nat.le_mul_of_pos_right _ hProdQ)
  have hDQ : ((Q.prod id : ℕ) : ℝ) ≤ ((P ∪ Q).prod id : ℕ) := by
    exact_mod_cast (show Q.prod id ≤ (P ∪ Q).prod id by
      rw [hPeriod, Nat.mul_comm]
      exact Nat.le_mul_of_pos_right _ hProdP)
  nlinarith only [hEP, hEQ, hEU, hIdentity, hDP, hDQ]

end Erdos319Sharp
