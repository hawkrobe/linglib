module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.Counting

/-!
# Ladusaw (1979): Polarity Sensitivity as Inherent Scope Relations

This file formalizes the licensing condition of [ladusaw-1979]: a negative polarity item is
acceptable only in the scope of a downward-entailing expression, one that reverses
entailment among its arguments, so that the affective environments of the earlier
literature are characterized rather than listed. Over the library's inventory of licensing
environments, `IsDownwardEntailing` reads off the entailment signature recorded for each,
every environment credited to the dissertation as a licenser is downward entailing
(`cited_environments_de`), questions are not (`question_not_de`), and every
downward-entailing environment licenses the weak polarity items
(`ladusaw_generalization`). The determiners behind three of these environments are
downward entailing in the substrate's generalized-quantifier semantics in exactly the
argument where they license: *no* in its scope and its restrictor, *few* in its scope, and
*every* in its restrictor but not in its scope (`determiner_monotonicity`), so the scope
relation the dissertation makes inherent to polarity items decides where *any* may occur
under each.

## Implementation notes

The dissertation's scan in the library has no text layer and was not checked for this pass; the
statements follow the generalization as the substrate records it, with the environments' strengths
taken from `LicensingContext.strength`, and `environments` is the list of licensers the substrate
has credited to the dissertation. The distinction of anti-additive from merely downward-entailing
licensers, and with it the strong polarity items, postdates the dissertation and is left to the
studies of the later papers. Questions license weak items in the substrate by another mechanism, so
the converse of the generalization is not stated.

## References

* [ladusaw-1979]
-/

@[expose] public section

namespace Ladusaw1979

open PolarityItem Quantifier Quantifier.GQ

/-- An environment is downward entailing when its recorded entailment signature reverses
entailment, that is, carries a strength on the scale of downward-entailing licensers. -/
def IsDownwardEntailing (c : LicensingContext) : Prop :=
  c.strength ≠ ⊥

instance (c : LicensingContext) : Decidable (IsDownwardEntailing c) :=
  inferInstanceAs (Decidable (c.strength ≠ ⊥))

-- UNVERIFIED: the list is the substrate's record, not checked against the dissertation.
/-- The licensing environments credited to the dissertation are negation, negative quantifiers,
*without*, the restrictor of a universal, *few*, *at most*, the antecedent of a conditional,
*before*, *too … to*, and the clausal comparative. -/
def environments : List LicensingContext :=
  [.negation, .nobody, .withoutClause, .universalRestrictor, .few, .atMost,
    .conditionalAntecedent, .beforeClause, .tooTo, .clausalComparative]

/-- Every environment credited to the dissertation is downward entailing. -/
theorem cited_environments_de : ∀ c ∈ environments, IsDownwardEntailing c := by decide

/-- Questions are not downward entailing. -/
theorem question_not_de : ¬ IsDownwardEntailing .question := by decide

/-- A downward-entailing environment licenses the weak polarity items, which is the
dissertation's generalization. -/
theorem ladusaw_generalization (c : LicensingContext) (hc : IsDownwardEntailing c)
    (e : PolarityItem) (he : e.licensor = some .weak) : c.Licenses e := by
  cases c <;> first
    | exact absurd hc (by decide)
    | exact .inl ⟨rfl, .weak, he, by decide, .inl rfl⟩

variable {α : Type*}

/-- *every* is not downward entailing in its scope. With a witness in the domain, a scope true of
everything shrinks to one true of nothing. -/
theorem every_not_scope_down [Nonempty α] : ¬ ScopeAntitone (every : GQ α) := fun h ↦
  h ⊤ (bot_le : (⊥ : α → Prop) ≤ ⊤) (fun _ _ ↦ trivial) (Classical.arbitrary α) trivial

/-- *no* reverses entailment in both arguments, *few* in its scope, and *every* in its restrictor
but not its scope, which is where each licenses a polarity item. -/
theorem determiner_monotonicity [Fintype α] [Nonempty α] :
    ScopeAntitone (no : GQ α) ∧ RestrictorAntitone (no : GQ α) ∧ ScopeAntitone (few : GQ α) ∧
      RestrictorAntitone (every : GQ α) ∧ ¬ ScopeAntitone (every : GQ α) :=
  ⟨scopeAntitone_no, restrictorAntitone_no, scopeAntitone_few, restrictorAntitone_every,
    every_not_scope_down⟩

end Ladusaw1979
