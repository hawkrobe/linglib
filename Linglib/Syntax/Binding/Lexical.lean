import Linglib.Syntax.Pronoun.Basic
import Linglib.Features.CoreferenceStatus

/-!
# The lexical interface to binding
[chomsky-1981]

The lexical half of binding theory, as a mixin. A carrier `α` is a `Binding.Lexicon`
when each of its pro-forms *declares* a `Features.BindingClass` — which binding
principle governs it. The framework-neutral binding engine
(`Syntax/Binding/Basic.lean`) reads a pro-form's declared class rather than recovering
it from surface form strings or lexicon-list membership: the lexical entry is the
source of truth for its own binding role.

The universal `Pronoun` record is the canonical instance (via its `bindingClass`
field). A syntactic theory's representation (`Word`, an HPSG synsem, …) can instance
it too — which is what lets the binding principles abstract over `[Binding.Lexicon α]`
instead of taking an explicit `classify : Word → Option BindingClass` parameter.

## Main declarations

* `Binding.Lexicon` — a carrier whose pro-forms declare a `BindingClass`.
* `Binding.Lexicon.{IsAnaphor, IsPronominal, IsRExpression}` — the Principle A / B / C
  partitions, read off the declaration.

## Implementation notes

The *per-kind* marker mixins (`Reflexive α`, `Personal α`, …) of the long-horizon design
attach to dedicated single-kind carriers, not to the universal `Pronoun` record (whose
`bindingClass` varies per entry, so no type-level "all of `α` is reflexive" holds). They
are deferred to the theory layer; the per-element `IsAnaphor`/… predicates here serve the
multi-kind record.
-/

namespace Binding

open Features (BindingClass)

/-- A carrier whose pro-forms declare a `Features.BindingClass` — the lexical interface
the binding engine reads. `none` is a bare φ-shell that declares no class. -/
class Lexicon (α : Type) where
  /-- The binding class `a` declares, if any. -/
  bindingClass : α → Option BindingClass

instance : Lexicon Pronoun := ⟨Pronoun.bindingClass⟩

namespace Lexicon

variable {α : Type} [Lexicon α]

/-- `a` declares a Principle-A anaphor (reflexive or reciprocal). -/
def IsAnaphor (a : α) : Prop :=
  bindingClass a = some .reflexive ∨ bindingClass a = some .reciprocal

/-- `a` declares a Principle-B pronominal. -/
def IsPronominal (a : α) : Prop := bindingClass a = some .pronoun

/-- `a` declares a Principle-C R-expression. -/
def IsRExpression (a : α) : Prop := bindingClass a = some .rExpression

instance (a : α) : Decidable (IsAnaphor a) := by unfold IsAnaphor; infer_instance
instance (a : α) : Decidable (IsPronominal a) := by unfold IsPronominal; infer_instance
instance (a : α) : Decidable (IsRExpression a) := by unfold IsRExpression; infer_instance

end Lexicon

end Binding
