/-!
# Coordinate-structure symmetry

The structural-symmetry parameter of a coordinate phrase (`&P`): whether one
conjunct is structurally more prominent (c-commands the other) or the structure
is flat / multidominant. This is a syntactic structural primitive — the three
groups of analyses for selection-violating coordination ([schwarzer-2026])
disagree precisely on this parameter.
-/

namespace Minimalist

/-- Structural symmetry of a coordinate phrase.

    The three groups of analyses for selection-violating coordination
    ([schwarzer-2026]) disagree on this parameter:
    - **Bottom-up accounts** assume `asymmetric` structure: the first conjunct
      is structurally more prominent (c-commands the second), so only it must
      satisfy the selector's c-selectional requirements.
    - **Linear/temporal closeness accounts** are compatible with either, but
      their predictions derive from linear/temporal order, not structure.
    - **Symmetric accounts** ([neeleman-etal-2022], [przepiorkowski-2024])
      posit flat or multidominance structures with no structural prominence. -/
inductive CoordSymmetry where
  /-- Flat or multidominance: no conjunct is structurally more prominent. -/
  | symmetric
  /-- Binary `&P`: first conjunct is structurally more prominent
      (c-commands the second conjunct). -/
  | asymmetric
  deriving DecidableEq, Repr, BEq

end Minimalist
