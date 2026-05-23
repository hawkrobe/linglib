import Mathlib.Data.Set.Basic

/-!
# Alternative Sources

A common abstraction over the many "alternative-generation" mechanisms
in formal pragmatics. Different theories generate different competitor
sets for the same expression:

- @cite{katzir-2007} structural alternatives — substitution/deletion/
  contraction over a parse tree, using items in the lexicon ∪ subtrees
- @cite{buccola-kriz-chemla-2018} conceptual alternatives — including
  competitors not realizable by linguistic material
- @cite{sauerland-alexiadou-2020} Meaning First — alternatives drawn
  at the thought-structure level, prior to compression
- @cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025}
  indirect alternatives — pronounceable expressions equivalent in
  meaning to an unpronounceable Katzir alternative

All of these are functions `S → Set S`. We give that function type a
name so that pragmatic competition operators (`violatesMP`,
`violatesMaximize`, `violatesMCIs`, `violatesAvoidAmbiguity`) can be
parameterized over the alternative source rather than hardcoding any
single one.

This follows mathlib's pattern of bundling a function-shaped abstraction
under a structural alias (cf. `Filter`, `Order.Hom`) rather than as a
typeclass — there is no canonical alternative source per carrier type,
since different theories supply different sources for the same parse.
-/

set_option autoImplicit false

namespace Alternatives

universe u

/-- An alternative source assigns to each expression a set of competitors.

Theory-specific instances of this signature live elsewhere:
`Alternatives.Structural.katzirSource` (Katzir 2007),
`Alternatives.Indirect.indirectFrom` (Jeretič et al. 2025), etc. -/
abbrev AlternativeSource (S : Type u) : Type u := S → Set S

end Alternatives
