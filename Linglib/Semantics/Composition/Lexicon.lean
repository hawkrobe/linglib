module

public import Linglib.Semantics.Composition.Ty

/-!
# Lexicons

A lexicon is a string-keyed lookup of denotations, polymorphic over an effect functor `M`
([bumford-charlow-2026]): an entry is a `Denotation E W M D`, a semantic type with an
`M`-computation in its domain. It is the `String`-leaved case of the leaf interpretation that
`Tree.interp` takes, whose leaves may instead be a fragment carrier interpreted through its
readings. Scope-takers live at `M = Cont R`, conventional-implicature items at `M = Writer P`,
and the default `M := Id` is the pure lexicon of Heim and Kratzer's type-driven composition.

## References

* [heim-kratzer-1998]
* [bumford-charlow-2026]
-/

@[expose] public section

namespace HeimKratzer

open Montague

/-- A lexicon looks up a string's `M`-effectful denotation, if it has one. -/
abbrev Lexicon (E W : Type) (M : Type → Type := Id) (D : Type := ℝ) :=
  String → Option (Denotation E W M D)

end HeimKratzer
