module

public import Mathlib.Order.Basic
public import Mathlib.Data.Set.Basic

/-!
# Rules of exponence

A rule of exponence, in Matthews's sense, pairs an exponent with a condition on the contexts it
applies in. This file defines the interface for types of such rules, rule sets, and
the specificity preorder of Kiparsky's Elsewhere Condition, under which a rule is more specific
when it applies in fewer contexts.

## Main definitions

* `Exponence.Rule`: a type of rules, each with an exponent and an applicability condition.
* `Exponence.RuleSet`: a list of rules, earlier rules winning ties.
* `Exponence.toPreorder`: the specificity preorder. It is not an instance, and each type of
  rules installs it itself.

## References

* [matthews-1991]
* [kiparsky-1973]
-/

@[expose] public section

namespace Morphology.Exponence

/-- `Rule R Ctx E` says that `R` is a type of rules of exponence, each carrying an exponent in
`E` and applying in a class of contexts in `Ctx`. -/
class Rule (R : Type*) (Ctx E : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → E
  /-- The condition on contexts under which a rule applies. -/
  Applies : R → Ctx → Prop

export Rule (exponent Applies)

/-- A rule set is a list of rules of exponence, earlier rules winning ties. -/
abbrev RuleSet (R : Type*) := List R

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E]

/-- The contexts in which a rule applies. -/
def applySet (r : R) : Set Ctx := {c | Applies r c}

@[simp] theorem mem_applySet {r : R} {c : Ctx} :
    c ∈ applySet r ↔ Applies r c :=
  Iff.rfl

/-- `r ≤ s` when `r` applies in a subset of the contexts `s` applies in. -/
@[reducible] def toPreorder : Preorder R := Preorder.lift (applySet (Ctx := Ctx) (E := E))

end Morphology.Exponence
