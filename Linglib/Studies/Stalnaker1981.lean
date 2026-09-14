import Linglib.Semantics.Conditionals.Counterfactual
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-!
# Stalnaker (1981): A Defense of Conditional Excluded Middle

This file formalizes [stalnaker-1981]'s defense of the selection-function analysis of
conditionals against [lewis-1973]'s comparative-similarity analysis. The two differ by the limit
assumption, that every possible antecedent has closest worlds, and the uniqueness assumption,
that it has at most one; in the logic of conditionals the first is the consequence condition
and the second is conditional excluded middle, which is equivalent to the distribution of a
conditional over a disjunctive consequent (`cem_iff_distribution`). Uniqueness is neutralized
by supervaluation: the selection functions in use correspond to orderings with ties, and a
conditional is true when every completion makes it true, so conditional excluded middle stays
valid while [quine-1950]'s two counterfactuals about Bizet and Verdi come out neither true nor
false rather than, as for Lewis, both false (`bizet_italian_indet`, `bizet_verdi_cem`,
`bizet_cem_fails_universal`); distribution likewise separates the analyses
(`distribution_needs_uniqueness`, `distribution_fails_bizetverdi`). Because Lewis's antecedents
are necessity operators, his analysis predicts a scope ambiguity between a quantifier inside
and outside a counterfactual, as with the woman President Carter would have appointed to the
Supreme Court; selection predicts none, the two scopes coinciding (`selection_scope`), and
indeterminacy rather than ambiguity explains why no particular woman would have been appointed
(`court_no_particular_woman`).

The limit assumption cannot be neutralized in the same way, and dropping it has bizarre
consequences: for a line a little less than an inch long, Lewis's analysis makes *if the line
had been more than one inch long, it would not have been x inches long* true for every length
x, so that there is no length the line might have had, and the consequence condition fails
(`lewisWould_longer_ne`, `not_lewisMight_longer_eq`, `not_consequence_lewisWould`). Finally,
Lewis's *might* as the dual of *would* collapses into *would* under conditional excluded
middle; reading *might* instead as a possibility operator over the whole conditional keeps
Lewis's formulation, *if A, might B* true exactly when *if A, would not-B* is not true, for a
possible antecedent (`selectionalMight_iff`), and separates *might* from *would* through
indeterminacy (`might_would_asymmetry`).

## Implementation notes

The conditional logic of the first section is abstract: a conditional operator on
propositions with right weakening, agglomeration and a valid tautological consequent, the
finite form of the consequence condition. Lewis's truth condition without the limit assumption
is stated on lengths ordered by similarity to the actual length. The selection-similarity
correspondence of the paper's opening, the Moore-paradoxical status of denying a *would* while
affirming a *might*, and the Kennedy example are not formalized.

## References

* [stalnaker-1981]
* [lewis-1973]
* [quine-1950]
* [van-fraassen-1966]
-/

namespace Stalnaker1981

open Conditionals (SimilarityOrdering selectionConditional)
open Conditionals.Counterfactual

/-! ### Conditional excluded middle and distribution -/

section ConditionalLogic

variable {W : Type*} (cond : Set W → Set W → Set W)

/-- The finite consequence condition: a conditional operator weakens its consequent,
agglomerates consequents, and has every tautological consequent. -/
structure ConsequenceCondition : Prop where
  mono : ∀ A B C, B ⊆ C → cond A B ⊆ cond A C
  agg : ∀ A B C, cond A B ∩ cond A C ⊆ cond A (B ∩ C)
  taut : ∀ A, cond A Set.univ = Set.univ

/-- Conditional excluded middle: a conditional or its opposite holds everywhere. -/
def CEM : Prop := ∀ A B, cond A B ∪ cond A Bᶜ = Set.univ

/-- Distribution: a conditional with a disjunctive consequent yields one with a disjunct. -/
def Distribution : Prop := ∀ A B C, cond A (B ∪ C) ⊆ cond A B ∪ cond A C

/-- Under the consequence condition, conditional excluded middle and distribution are
equivalent. -/
theorem cem_iff_distribution (h : ConsequenceCondition cond) :
    CEM cond ↔ Distribution cond := by
  constructor
  · intro hcem A B C w hw
    rcases (Set.eq_univ_iff_forall.1 (hcem A B) w) with hB | hB
    · exact Or.inl hB
    · refine Or.inr (h.mono A (Bᶜ ∩ (B ∪ C)) C ?_ (h.agg A _ _ ⟨hB, hw⟩))
      rintro x ⟨hx, hxB | hxC⟩
      · exact absurd hxB hx
      · exact hxC
  · intro hdist A B
    refine Set.eq_univ_of_forall λ w => hdist A B Bᶜ ?_
    rw [Set.union_compl_self, h.taut]
    trivial

end ConditionalLogic

/-! ### Selection: excluded middle and scope -/

section Selection

variable {W : Type*} (s : Conditionals.SelectionFunction W)

/-- A determinate selection function validates conditional excluded middle. -/
theorem selection_cem (A B : W → Prop) (w : W) :
    selectionConditional s A B w ∨ selectionConditional s A (λ v => ¬ B v) w :=
  Classical.em _

/-- Under selection, a quantifier inside the consequent and one outside the conditional
coincide: there is no scope ambiguity. -/
theorem selection_scope {ι : Type*} (A : W → Prop) (F : ι → W → Prop) (w : W) :
    selectionConditional s A (λ v => ∃ x, F x v) w ↔ ∃ x, selectionConditional s A (F x) w :=
  Iff.rfl

end Selection

/-! ### Bizet and Verdi -/

section BizetVerdi

/-- The worlds of the Bizet–Verdi example: the actual world, and the two closest worlds in
which the composers are compatriots. -/
inductive BVWorld
  | actual | bothItalian | bothFrench
  deriving Repr, DecidableEq, Fintype

/-- The similarity ordering: the actual world is closest to itself, and the two compatriot
worlds tie. -/
def bvSim : SimilarityOrdering BVWorld := .ofBool
  (λ | .actual, .actual, _ => true
     | .actual, .bothItalian, .bothFrench => true
     | .actual, .bothFrench, .bothItalian => true
     | _, w₁, w₂ => w₁ == w₂)
  (by decide) (by decide)

/-- Bizet and Verdi are compatriots. -/
def compatriots : BVWorld → Prop
  | .bothItalian | .bothFrench => True
  | .actual => False

instance : DecidablePred compatriots := λ w => by cases w <;> unfold compatriots <;> infer_instance

/-- Bizet is Italian. -/
def bizetItalian : BVWorld → Prop
  | .bothItalian => True
  | _ => False

instance : DecidablePred bizetItalian := λ w => by
  cases w <;> unfold bizetItalian <;> infer_instance

/-- Verdi is French. -/
def verdiFrench : BVWorld → Prop
  | .bothFrench => True
  | _ => False

instance : DecidablePred verdiFrench := λ w => by cases w <;> unfold verdiFrench <;> infer_instance

/-- *If Bizet and Verdi had been compatriots, Bizet would have been Italian* is neither true
nor false: the closest compatriot worlds disagree. -/
theorem bizet_italian_indet :
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .indet := by decide

/-- *If Bizet and Verdi had been compatriots, Verdi would have been French* is neither true
nor false. -/
theorem verdi_french_indet :
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .indet := by decide

/-- Conditional excluded middle holds for the example under supervaluation: the disjunction of
the conditional and its opposite is not false. -/
theorem bizet_verdi_cem :
    selectionalCounterfactual bvSim compatriots bizetItalian .actual ⊔
      selectionalCounterfactual bvSim compatriots (λ w => ¬ bizetItalian w) .actual ≠ .false :=
  cem_selectional bvSim compatriots bizetItalian .actual

/-- On the universal analysis both counterfactuals are false, and excluded middle fails. -/
theorem bizet_cem_fails_universal :
    ¬ universalCounterfactual bvSim compatriots bizetItalian .actual ∧
    ¬ universalCounterfactual bvSim compatriots (λ w => ¬ bizetItalian w) .actual :=
  ⟨by decide, by decide⟩

/-- Quine's inference: *if they had been compatriots, Bizet would have been Italian or Verdi
French* is true on the universal analysis, but neither disjunct's conditional is, so
distribution fails. -/
theorem distribution_fails_bizetverdi :
    universalCounterfactual bvSim compatriots (λ w => bizetItalian w ∨ verdiFrench w) .actual ∧
    ¬ universalCounterfactual bvSim compatriots bizetItalian .actual ∧
    ¬ universalCounterfactual bvSim compatriots verdiFrench .actual :=
  ⟨by decide, by decide, by decide⟩

/-- Under supervaluation the disjunctive conditional is true while each disjunct's conditional
is indeterminate: distribution holds on every completion but not on the supervaluation, whose
closest worlds are not unique. -/
theorem distribution_needs_uniqueness :
    selectionalCounterfactual bvSim compatriots (λ w => bizetItalian w ∨ verdiFrench w) .actual
      = .true ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .indet ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .indet :=
  ⟨by decide, by decide, by decide⟩

end BizetVerdi

/-! ### The Supreme Court appointment -/

section Court

/-- The worlds of the appointment example: the actual world, with no vacancy, and two equally
close worlds in which a vacancy is filled by a different woman. -/
inductive CourtWorld
  | actual | w1 | w2
  deriving Repr, DecidableEq, Fintype

/-- The similarity ordering: the two vacancy worlds tie. -/
def courtSim : SimilarityOrdering CourtWorld := .ofBool
  (λ | .actual, .actual, _ => true
     | .actual, .w1, .w2 => true
     | .actual, .w2, .w1 => true
     | _, w₁, w₂ => w₁ == w₂)
  (by decide) (by decide)

/-- A vacancy occurs. -/
def vacancy : CourtWorld → Prop
  | .actual => False
  | _ => True

instance : DecidablePred vacancy := λ w => by cases w <;> unfold vacancy <;> infer_instance

/-- The women who might be appointed. -/
inductive Woman
  | a | b
  deriving DecidableEq, Fintype

/-- Woman `a` is appointed in the first vacancy world, woman `b` in the second. -/
def appointed : Woman → CourtWorld → Prop
  | .a, .w1 => True
  | .b, .w2 => True
  | _, _ => False

instance (x : Woman) : DecidablePred (appointed x) := λ w => by
  cases x <;> cases w <;> unfold appointed <;> infer_instance

instance : DecidablePred (λ w => ∃ x, appointed x w) := λ w =>
  Fintype.decidableExistsFintype (p := λ x => appointed x w)

/-- On the universal analysis the narrow scope, *he would have appointed some woman*, is true
while the wide scope, *some woman is such that he would have appointed her*, is false: a
scope ambiguity Lewis's analysis predicts and speakers do not perceive. -/
theorem court_scope_universal :
    universalCounterfactual courtSim vacancy (λ w => ∃ x, appointed x w) .actual ∧
    ¬ ∃ x, universalCounterfactual courtSim vacancy (appointed x) .actual :=
  ⟨by decide, by decide⟩

/-- Under supervaluation the narrow scope is true while each woman's conditional is
indeterminate: there is no particular woman he would have appointed, by underdetermination
rather than ambiguity. -/
theorem court_no_particular_woman :
    selectionalCounterfactual courtSim vacancy (λ w => ∃ x, appointed x w) .actual = .true ∧
    ∀ x, selectionalCounterfactual courtSim vacancy (appointed x) .actual = .indet :=
  ⟨by decide, by decide⟩

end Court

/-! ### The limit assumption -/

section Limit

/-- Lewis's truth condition without the limit assumption, for a line that is actually less than
an inch long, on lengths ordered by closeness to the actual length: some antecedent-length
verifies the consequent and so does every antecedent-length at least as close. -/
def lewisWould (A B : Set ℚ) : Prop := ∃ j ∈ A, j ∈ B ∧ ∀ k ∈ A, k ≤ j → k ∈ B

/-- Lewis's *might*: the dual of *would*. -/
def lewisMight (A B : Set ℚ) : Prop := ¬ lewisWould A Bᶜ

/-- The line is more than one inch long. -/
def longer : Set ℚ := {ℓ | 1 < ℓ}

/-- For every length, *if the line had been more than one inch long, it would not have been
that long* is true: below any length over an inch there is a closer one. -/
theorem lewisWould_longer_ne (x : ℚ) : lewisWould longer {ℓ | ℓ ≠ x} := by
  by_cases hx : 1 < x
  · refine ⟨(1 + x) / 2, by show 1 < (1 + x) / 2; linarith, ?_, λ k hk hkj hkx => ?_⟩
    · show (1 + x) / 2 ≠ x
      intro h; linarith
    · have : 1 < k := hk
      rw [hkx] at hkj
      linarith
  · refine ⟨2, by show (1 : ℚ) < 2; norm_num, ?_, λ k hk _ hkx => ?_⟩
    · show (2 : ℚ) ≠ x
      intro h; exact hx (by rw [← h]; norm_num)
    · have : 1 < k := hk
      rw [hkx] at this
      exact hx this

/-- So there is no length the line might have had, on Lewis's *might*. -/
theorem not_lewisMight_longer_eq (x : ℚ) : ¬ lewisMight longer {x} := λ h =>
  h (by simpa [Set.compl_def] using lewisWould_longer_ne x)

/-- Without the limit assumption the consequence condition fails: the consequents
*not x inches long*, over all lengths over an inch, jointly entail *at most an inch long*, each
conditional is true, and the conditional with the entailed consequent is false. -/
theorem not_consequence_lewisWould :
    (⋂ x ∈ longer, {ℓ : ℚ | ℓ ≠ x}) ⊆ longerᶜ ∧
    (∀ x ∈ longer, lewisWould longer {ℓ | ℓ ≠ x}) ∧ ¬ lewisWould longer longerᶜ := by
  refine ⟨λ ℓ hℓ hℓA => ?_, λ x _ => lewisWould_longer_ne x, ?_⟩
  · exact (Set.mem_iInter₂.1 hℓ ℓ hℓA) rfl
  · rintro ⟨j, hj, hjc, -⟩
    exact hjc hj

end Limit

/-! ### Might -/

section Might

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W) (A B : W → Prop)
  [DecidablePred A] [DecidablePred B] (w : W)

/-- *Might* as a possibility operator over the conditional keeps Lewis's formulation: *if A,
might B* is true exactly when *if A, would not-B* is not true. -/
theorem selectionalMight_iff (h : (sim.closestWorlds w (Finset.univ.filter A)).Nonempty) :
    selectionalMight sim A B w ↔ selectionalCounterfactual sim A (λ v => ¬ B v) w ≠ .true := by
  obtain ⟨w₀, hw₀⟩ := h
  unfold selectionalMight selectionalCounterfactual
  split_ifs <;> simp_all

/-- In the Bizet–Verdi example both *might* conditionals are true while both *would*
conditionals are indeterminate: *might* and *would* part, as they cannot on Lewis's dual
under excluded middle. -/
theorem might_would_asymmetry :
    selectionalMight bvSim compatriots bizetItalian .actual ∧
    selectionalMight bvSim compatriots verdiFrench .actual ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .indet ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .indet :=
  ⟨by decide, by decide, by decide, by decide⟩

end Might

end Stalnaker1981
