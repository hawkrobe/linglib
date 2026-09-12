import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Conditionals.PremiseSemantic

/-!
# Kratzer (1989): An Investigation of the Lumps of Thought

This file formalizes the paper's argument that counterfactual reasoning needs the lumping
relation between propositions, on the situation-semantic premise semantics of
`Conditionals.PremiseSemantic`. A proposition lumps another at a world when every part of
the world at which the first holds is one at which the second holds too. The analysis of §4.2
adds true propositions to the antecedent of a counterfactual while preserving consistency;
taken at face value it predicts (§4.3) that if Paula weren't buying a pound of apples, the
Atlantic Ocean might be drying up, since the true disjunction that Paula is buying apples or
the Atlantic is drying up can be added consistently to the antecedent and, with it, yields
the consequent. The repair of §4.4 is that a proposition brings along everything it lumps:
in a world where the Atlantic is not drying up, every situation where the disjunction holds
is one where Paula is buying apples, so the disjunction lumps the first disjunct, which
contradicts the antecedent, and the spurious might-counterfactual is blocked while the
proposition that the Atlantic is not drying up survives and settles the question.

## Implementation notes

The model has three worlds, the actual one, one where only Paula's purchase differs, and one
where the Atlantic dries, and two parts of the actual world, one supporting only the purchase
and one supporting only the Atlantic's calm; the second is what keeps the calm from lumping
the purchase. The base set holds (9a), (9b), and (9d); the moon disjunction (9e) runs in
parallel. The crucial set is the library's, which follows the 2012 revision of the paper in
dropping the 1989 closure of the premises other than the antecedent under logical
consequence; the argument does not turn on it. The analysis of §4.2 is `naiveMight`,
which quantifies over consistent premise sets with no lumping closure.

## References

* [kratzer-1989]
* [kratzer-2012] — Chapter 5, the revised version of the paper
* [lewis-1973] — the similarity analysis the paper argues against
-/

namespace Kratzer1989

open Conditionals.Counterfactual Conditionals.PremiseSemantic

/-- The situations: three worlds and two parts of the actual world. -/
inductive Sit
  | actual
  | noApples
  | atlantic
  | purchase
  | calm
  deriving DecidableEq, Repr, Fintype

/-- Parthood: the two partial situations are parts of the actual world. -/
protected def Sit.le (a b : Sit) : Prop :=
  a = b ∨ ((a = .purchase ∨ a = .calm) ∧ b = .actual)

instance : DecidableRel Sit.le := λ _ _ => by unfold Sit.le; infer_instance

instance : PartialOrder Sit where
  le := Sit.le
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := Sit) (· ≤ ·) := λ a b => inferInstanceAs (Decidable (Sit.le a b))

instance (s : Sit) : Decidable (IsMax s) := inferInstanceAs (Decidable (∀ b, s ≤ b → b ≤ s))

/-- (9a): Paula is buying a pound of apples. -/
def pa : Set Sit := {.purchase, .actual}

/-- The Atlantic Ocean is drying up. -/
def ad : Set Sit := {.atlantic}

/-- (9b): the Atlantic Ocean is not drying up. -/
def notAd : Set Sit := {.calm, .actual, .noApples}

/-- (9d): Paula is buying a pound of apples or the Atlantic Ocean is drying up. -/
def paOrAd : Set Sit := pa ∪ ad

/-- The antecedent of (10a): Paula is not buying a pound of apples. -/
def notPa : Set Sit := {.noApples, .atlantic}

/-- The base set of facts at the actual world: (9a), (9b), and (9d). -/
def base : Set (Set Sit) := {pa, notAd, paOrAd}

/-- Decide a claim about the situations and propositions. -/
scoped macro "decide_sit" : tactic =>
  `(tactic| ((try simp only [pa, ad, notAd, paOrAd, notPa, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_sInter, Set.sInter_insert,
      Set.sInter_singleton, mem_worlds, Set.mem_compl_iff]) <;> decide))

/-- The disjunction lumps its first disjunct at the actual world (§4.4): the Atlantic is not
drying up in any part of it. -/
theorem lumps_paOrAd_pa : Lumps paOrAd pa Sit.actual := ⟨by decide_sit, by decide_sit⟩

/-- The calm of the Atlantic does not lump the purchase: a part of the actual world supports
the first without the second. -/
theorem not_lumps_notAd_pa : ¬ Lumps notAd pa Sit.actual := λ h =>
  (by decide_sit : Sit.calm ∉ pa) (h.localImpl (by decide) (by decide_sit))

/-- Nor does it lump the disjunction. -/
theorem not_lumps_notAd_paOrAd : ¬ Lumps notAd paOrAd Sit.actual := λ h =>
  (by decide_sit : Sit.calm ∉ paOrAd) (h.localImpl (by decide) (by decide_sit))

/-! ### The analysis of §4.2 and its failure (§4.3) -/

section Naive

variable {S : Type*} [Preorder S]

/-- The premise sets of the analysis of §4.2: consistent subsets of the facts and the
antecedent that contain the antecedent, with no closure under lumping. -/
def naiveSet (Fw : Set (Set S)) (p : Set S) : Set (Set (Set S)) :=
  {A | A ⊆ insert p Fw ∧ p ∈ A ∧ IsConsistent A}

/-- The might-counterfactual of §4.2: some way of consistently adding facts to the antecedent
never makes the consequent incompatible. -/
def naiveMight (Fw : Set (Set S)) (p q : Set S) : Prop :=
  ∃ A ∈ naiveSet Fw p, ∀ A' ∈ naiveSet Fw p, A ⊆ A' → IsCompatible q A'

end Naive

/-- (10a) under the analysis of §4.2: adding the disjunction to the antecedent keeps the
premises consistent and makes the Atlantic's drying compatible with every extension. -/
theorem naiveMight_atlantic : naiveMight base notPa ad := by
  refine ⟨{notPa, paOrAd}, ⟨by simp [base, Set.insert_subset_iff], by simp,
    ⟨.atlantic, by decide_sit⟩⟩, ?_⟩
  rintro A' ⟨_, hp, s, hw, hs⟩ hAA'
  have hpaOrAd : s ∈ paOrAd := hs paOrAd (hAA' (by simp))
  have hnotPa : s ∈ notPa := hs notPa hp
  have hs' : s = .atlantic := by
    revert hnotPa hpaOrAd; clear hs hw hp hAA'; revert s; decide_sit
  subst hs'
  refine ⟨.atlantic, by decide_sit, ?_⟩
  intro t ht
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · decide_sit
  · exact hs t ht

/-! ### The repair (§4.4) -/

/-- (10a) under lumping: no consistent lumping-closed premise set keeps the Atlantic's drying
compatible. The disjunction cannot be added, since it brings along the purchase, which
contradicts the antecedent; and once the Atlantic's calm is added the consequent is out. -/
theorem not_mightCF_atlantic : ¬ mightCF base Sit.actual notPa ad := by
  rintro ⟨A, hA, hall⟩
  have hpa : pa ∉ A := λ h => by
    obtain ⟨s, hw, hs⟩ := hA.consistent
    have h₁ := hs pa h
    have h₂ := hs notPa hA.antecedent_mem
    revert h₁ h₂; clear hs hw; revert s; decide_sit
  have hpaOrAd : paOrAd ∉ A := λ h =>
    hpa (hA.lumping_closed paOrAd h pa (by simp [base]) lumps_paOrAd_pa)
  have hA' : IsCrucialSet base Sit.actual notPa {notPa, notAd} :=
    { subset_insert := by simp [base, Set.insert_subset_iff]
      antecedent_mem := by simp
      consistent := ⟨.noApples, by decide_sit⟩
      lumping_closed := by
        intro q hq r hr hl
        rcases Set.mem_insert_iff.mp hq with rfl | hq
        · exact absurd hl.holds (by decide_sit)
        · rw [Set.mem_singleton_iff] at hq
          subst hq
          rcases hr with rfl | rfl | rfl
          · exact absurd hl not_lumps_notAd_pa
          · simp
          · exact absurd hl not_lumps_notAd_paOrAd }
  have hsub : A ⊆ {notPa, notAd} := by
    intro t ht
    rcases hA.subset_insert ht with rfl | rfl | rfl | rfl
    · simp
    · exact absurd ht hpa
    · simp
    · exact absurd ht hpaOrAd
  obtain ⟨s, hw, hs⟩ := hall _ hA' hsub
  have h₁ := hs ad (Set.mem_insert _ _)
  have h₂ := hs notAd (by simp)
  revert h₁ h₂; clear hs hw; revert s; decide_sit

/-- The dual: under lumping, if Paula weren't buying apples the Atlantic would not be
drying up. -/
theorem wouldCF_notAd : wouldCF base Sit.actual notPa adᶜ :=
  not_not.mp (mightCF_iff_not_wouldCF_compl.not.mp not_mightCF_atlantic)

end Kratzer1989
