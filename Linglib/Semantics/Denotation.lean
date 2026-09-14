import Mathlib.Tactic.TypeStar

/-!
# Denotation

This file defines `Semantics.Denotes`, the class of objects that have a denotation, and the
bracket notation `⟦x⟧` for it ([heim-kratzer-1998]). A lexical item, a reading, a tree, or a
whole sentence denotes in whatever domain its instance names, so the class gives the library one
name for the map from a semantic object to its meaning, whether that map is compositional or
stipulated per object.

## Main definitions

* `Semantics.Denotes α D`: every object of `α` denotes in `D`; `⟦x⟧` is `Denotes.denote x`.

## References

* [heim-kratzer-1998]
-/

namespace Semantics

/-- `Denotes α D` says that every object of `α` denotes in `D`. -/
class Denotes (α : Type*) (D : outParam Type*) where
  /-- The denotation of `x`, written `⟦x⟧`. -/
  denote : α → D

/-- `⟦x⟧` is the denotation of `x`. -/
scoped notation:arg (priority := high) "⟦" x "⟧" => Denotes.denote x

end Semantics
