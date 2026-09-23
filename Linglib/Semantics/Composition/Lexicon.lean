module

public import Linglib.Semantics.Composition.Ty

/-!
# Lexicons

A lexicon is a string-keyed lookup of Montague denotations, polymorphic over an effect
functor `M` ([bumford-charlow-2024]): an entry is a `Denotation E W M D`, a semantic type with
an `M`-computation in its domain. It is the `String`-leaved case of the leaf interpretation
`Tree.interp` takes, whose leaves may instead be a fragment carrier interpreted through its
readings. Scope-takers live at `M = Cont R`, conventional-implicature
items at `M = Writer P`, and the default `M := Id` is the pure [heim-kratzer-1998] lexicon.

## Main definitions

* `Lexicon E W M D`: string-keyed lookup of `M`-effectful denotations.
* `Lexicon.lift`: embed a pure leaf interpretation into any effect via `pure`.

## References

* [heim-kratzer-1998]
* [bumford-charlow-2024]
-/

@[expose] public section

namespace Semantics.Montague

open Semantics.Composition

/-- A string-keyed lexicon of `M`-effectful denotations (default `Id`). -/
abbrev Lexicon (E W : Type) (M : Type → Type := Id) (D : Type := ℝ) :=
  String → Option (Denotation E W M D)

/-- Embed a pure leaf interpretation into the effect `M` by `pure`-lifting every entry. -/
def Lexicon.lift {E W D : Type} (M : Type → Type) [Pure M] {L : Type*}
    (lex : L → Option (Denotation E W Id D)) : L → Option (Denotation E W M D) :=
  λ w => (lex w).map (Sigma.map id λ _ => pure)

end Semantics.Montague
