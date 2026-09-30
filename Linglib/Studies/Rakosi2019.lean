/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Dynamic.PPCDRT
public import Linglib.Fragments.Hungarian.Reciprocals
public import Linglib.Data.Examples.Rakosi2019

/-!
# Rákosi (2019): Reciprocal anaphors in singular constructions in Hungarian

This file formalizes [rakosi-2019]: the reciprocal *egymás* takes any antecedent that denotes
a plurality, whether or not the plurality is coded morphosyntactically, while a plural
reflexive requires a plural antecedent and a plural verb. Over the paper's examples, a
reciprocal is acceptable exactly when its antecedent is semantically plural
(`reciprocal_iff_semanticPlural`), a plural reflexive exactly when the verb agrees in the
plural (`reflexivePl_iff_verb_pl`), and a singular reflexive exactly when it agrees in the
singular (`reflexiveSg_iff_verb_sg`); each of the four constructions with a singular verb, the
quantified antecedents of §3, the singular coordinate noun phrases of §4, the collective nouns
of §5 and the pro-dropped singular variables of §6, licenses the reciprocal
(`reciprocal_with_singular_verb`). The inclusive reflexive of §2 is set apart: it is never
read as a bound variable (`inclusive_not_bound`), so it is no counterexample, and the reciprocal
is excluded in its construction. The semantic side is the plural-assignment semantics of
`PPCDRT`: reciprocity at a jointly defined state makes the antecedent denote two or more
individuals (`reciprocity_implies_multiple_individuals`), the plurality a reciprocal feeds on,
whereas binding is satisfied by a singleton state (`binding_compatible_with_singleton`), which
is why a reflexive's plurality is a matter of φ-agreement instead. The reciprocal itself carries no
number feature (`egymas_no_number_feature`), the reflexive inflects (`reflexive_number_paradigm`).

## References

* [rakosi-2019]
* [dalrymple-haug-2024]
-/

@[expose] public section

namespace Rakosi2019

open PPCDRT Data.Examples Hungarian.Reciprocals
open Examples (all)

/-! ### The rows -/

/-- The anaphor of a row: the reciprocal, a singular or plural reflexive bound by its
antecedent, or the inclusive reflexive of §2. -/
inductive Anaphor
  | reciprocal
  | reflexiveSg
  | reflexivePl
  | inclusiveReflexive
  deriving DecidableEq

/-- The anaphor a row records. -/
def anaphor? (e : Datum) : Option Anaphor :=
  e.parse? "anaphor" [("reciprocal", .reciprocal), ("reflexiveSg", .reflexiveSg),
    ("reflexivePl", .reflexivePl), ("inclusiveReflexive", .inclusiveReflexive)]

/-- The verb agrees in the plural. -/
def VerbPlural (e : Datum) : Prop := e.feature? "verb" = some "pl"

/-- The antecedent denotes a plurality. -/
def SemanticPlural (e : Datum) : Prop := e.feature? "semanticPlural" = some "yes"

instance (e : Datum) : Decidable (VerbPlural e) := by unfold VerbPlural; infer_instance
instance (e : Datum) : Decidable (SemanticPlural e) := by
  unfold SemanticPlural; infer_instance

/-! ### The asymmetry -/

/-- A reciprocal is acceptable exactly when its antecedent is semantically plural. -/
theorem reciprocal_iff_semanticPlural :
    ∀ e ∈ all, anaphor? e = some .reciprocal → (e.judgment = .acceptable ↔ SemanticPlural e) := by
  decide

/-- A plural reflexive is acceptable exactly when the verb agrees in the plural. -/
theorem reflexivePl_iff_verb_pl :
    ∀ e ∈ all, anaphor? e = some .reflexivePl → (e.judgment = .acceptable ↔ VerbPlural e) := by
  decide

/-- A singular reflexive is acceptable exactly when the verb agrees in the singular. -/
theorem reflexiveSg_iff_verb_sg :
    ∀ e ∈ all, anaphor? e = some .reflexiveSg → (e.judgment = .acceptable ↔ ¬ VerbPlural e) := by
  decide

/-- Each of the four constructions of §§3–6 licenses the reciprocal under a singular verb. -/
theorem reciprocal_with_singular_verb :
    ∀ c ∈ ["quantified", "coordinate", "collective", "boundPro"], ∃ e ∈ all,
      e.feature? "antecedent" = some c ∧ anaphor? e = some .reciprocal ∧ ¬ VerbPlural e ∧
        e.judgment = .acceptable := by
  decide

/-- The inclusive reflexive of §2 is never read as a bound variable, so it is no plural
reflexive with a singular antecedent. -/
theorem inclusive_not_bound :
    ∀ e ∈ all, anaphor? e = some .inclusiveReflexive →
      e.readings.lookup "bound variable" ≠ some .acceptable := by
  decide

/-! ### The semantics of the two anaphoric relations -/

/-- Reciprocity at a state where both discourse referents are defined makes the antecedent
denote two or more individuals, under any distribution. This is the plurality a reciprocal
requires of its antecedent. -/
theorem reciprocity_implies_multiple_individuals {E : Type*} {uAnaph uAnt : ℕ}
    {S : PluralAssign ℕ E} {Δ : Set ℕ} (hdef : ∃ s ∈ S, s uAnaph ≠ ⊥ ∧ s uAnt ≠ ⊥)
    (h : reciprocityCond uAnaph uAnt S Δ) : (PCDRT.value uAnt S).Nontrivial := by
  obtain ⟨s, hs, hAnaph, hAnt⟩ := hdef
  obtain ⟨a, ha⟩ := Flat.ne_bot_iff_exists.mp hAnaph
  obtain ⟨b, hb⟩ := Flat.ne_bot_iff_exists.mp hAnt
  exact nontrivial_value_of_reciprocityCond h hs ha hb

/-- Binding is satisfied by a singleton state mapping both discourse referents to one value:
reflexive binding imposes no plurality on the denotation. -/
theorem binding_compatible_with_singleton {E : Type*} (e : E) (uAnaph uAnt : ℕ) :
    bindingCond uAnaph uAnt
      {PartialAssign.update (PartialAssign.update ⊥ uAnaph e) uAnt e} ∅ := by
  intro g hg
  obtain rfl : g = _ := hg
  by_cases h : uAnaph = uAnt
  · subst h; rfl
  · simp [PartialAssign.update_at, h]

/-! ### The forms -/

/-- *egymás* is invariable: it bears no number feature, consistent with a plurality
requirement that is semantic rather than a matter of agreement. -/
theorem egymas_no_number_feature : egymas.number = none := rfl

/-- The reflexive inflects for number, *maga* against *maguk*, and must match the verb. -/
theorem reflexive_number_paradigm :
    maga.number = some .singular ∧ maguk.number = some .plural := ⟨rfl, rfl⟩

end Rakosi2019
