import Mathlib.Tactic.TypeStar

/-!
# Denotation

This file defines `Semantics.Denotes`, the class of objects that have a denotation, and the
bracket notation `⟦x⟧` for it ([heim-kratzer-1998]). A lexical item, a reading, or a whole
sentence denotes in whatever domain its instance names, so the class gives the library one name
for the map from a semantic object to its meaning, whether that map is compositional or
stipulated per object. An object that denotes in the Montague type system denotes in
`Composition.Denotation E W M D`, a semantic type paired with a value in its domain, and is
thereby a terminal for the composition engine.

## Implementation notes

The class has one field, like `FunLike`: the parameters an interpretation is relativized to,
the model, context, index and assignment of [montague-1973] and [kaplan-1989], are not slots of
the class but Reader arguments of the domain `D`, in that order, so a Kaplanian expression
denotes a `Reference.Character`, an assignment-sensitive one an `Assignment E → _`, and an
intension a `W → _`. Instance resolution requires every type parameter of `D` to be fixed by
`α`; an object interpreted relative to data its type does not mention, a tree relative to a
lexicon, keeps an explicit interpretation function (`Composition.Tree.interp`, mathlib's
`Term.realize`) and gains an instance once its type is indexed by that data, as
`Conditional.Conditional W cond` is by its operator.

## Main definitions

* `Semantics.Denotes α D`: every object of `α` denotes in `D`; `⟦x⟧` is `Denotes.denote x`.

## References

* [heim-kratzer-1998]
* [montague-1973]
* [kaplan-1989]
-/

namespace Semantics

/-- `Denotes α D` says that every object of `α` denotes in `D`. -/
class Denotes (α : Type*) (D : outParam Type*) where
  /-- The denotation of `x`, written `⟦x⟧`. -/
  denote : α → D

/-- `⟦x⟧` is the denotation of `x`. -/
scoped notation:max (priority := high) "⟦" x "⟧" => Denotes.denote x

end Semantics
