import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Counting
import Linglib.Fragments.English.Toy

/-!
# Ladusaw (1979): Polarity Sensitivity as Inherent Scope Relations

This file formalizes the licensing condition of [ladusaw-1979]: a negative polarity item is
acceptable only in the scope of a downward-entailing expression, one that reverses
entailment among its arguments, so that the affective environments of the earlier
literature are characterized rather than listed. Over the library's inventory of licensing
environments, `IsDownwardEntailing` reads off the entailment signature recorded for each,
every environment the dissertation established as a licenser is downward entailing
(`cited_environments_de`), questions are not (`question_not_de`), and every
downward-entailing environment licenses the weak polarity items
(`ladusaw_generalization`). The determiners behind three of these environments are
downward entailing in the substrate's generalized-quantifier semantics in exactly the
argument where they license: *no* in its scope and its restrictor, *few* in its scope, and
*every* in its restrictor but not in its scope (`determiner_monotonicity`), so the scope
relation the dissertation makes inherent to polarity items decides where *any* may occur
under each.

## Implementation notes

The dissertation was not available for this pass; the statements follow the generalization
as the substrate records it, with the environments' signatures taken from
`LicensingContext.properties`, whose citation lists mark the rows the dissertation
established. The distinction of anti-additive from merely downward-entailing licensers, and
with it the strong polarity items, postdates the dissertation and is left to the studies of
the later papers. Questions license weak items in the substrate by another mechanism, so the
converse of the generalization is not stated.

## References

* [ladusaw-1979]
-/

namespace Ladusaw1979

open Polarity Quantification
open Semantics.Montague (ToyEntity)

/-- An environment is downward entailing when its recorded entailment signature reverses
entailment, that is, carries a strength on the scale of downward-entailing licensers. -/
def IsDownwardEntailing (c : LicensingContext) : Prop :=
  c.properties.strawsonSignature.toDEStrength ≠ none

instance (c : LicensingContext) : Decidable (IsDownwardEntailing c) := by
  unfold IsDownwardEntailing; infer_instance

/-- Every environment whose classification the substrate credits to the dissertation is
downward entailing: negation, negative quantifiers, *without*, the restrictor of a universal,
*few*, *at most*, the antecedent of a conditional, *before*, *too … to*, and the clausal
comparative. -/
theorem cited_environments_de (c : LicensingContext)
    (h : "ladusaw-1979" ∈ c.properties.citations) : IsDownwardEntailing c := by
  revert h; cases c <;> decide

/-- Questions are not downward entailing. -/
theorem question_not_de : ¬ IsDownwardEntailing .question := by decide

/-- The generalization: a downward-entailing environment licenses the weak polarity items. -/
theorem ladusaw_generalization (c : LicensingContext) (hc : IsDownwardEntailing c) (e : Item)
    (he : e.licensor = some .weak) : c.licenses e := by
  cases c <;> first
    | exact absurd hc (by decide)
    | exact ⟨.weak, he, _, rfl, by decide⟩

/-- *every* is not downward entailing in its scope: with a witness in the domain, a scope
true of everything shrinks to one true of nothing. -/
theorem every_not_scope_down : ¬ ScopeDownwardMono (every_sem (α := ToyEntity)) :=
  λ h => h (λ _ => True) (λ _ => False) (λ _ => True) (λ _ hx => hx.elim) (λ _ _ => trivial)
    .john trivial

/-- Inherent scope relations: *no* reverses entailment in both arguments, *few* in its scope,
and *every* in its restrictor but not its scope, which is where each licenses a polarity
item. -/
theorem determiner_monotonicity :
    ScopeDownwardMono (no_sem (α := ToyEntity)) ∧ RestrictorDownwardMono (no_sem (α := ToyEntity)) ∧
      ScopeDownwardMono (few_sem (α := ToyEntity)) ∧
      RestrictorDownwardMono (every_sem (α := ToyEntity)) ∧
      ¬ ScopeDownwardMono (every_sem (α := ToyEntity)) :=
  ⟨no_scope_down, no_restrictor_down, few_scope_down, every_restrictor_down,
    every_not_scope_down⟩

end Ladusaw1979
