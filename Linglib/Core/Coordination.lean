/-!
# Coordination Types

Shared types for cross-linguistic coordination morphology, used by
Fragment lexicons and Phenomena/Coordination studies.

## CoordRole

The role of a coordination morpheme in the @cite{mitrovic-sauerland-2014}
decomposition and beyond:
- `j` — set intersection (conjunction proper)
- `mu` — subset/additive (MU particle)
- `disj` — disjunction
- `advers` — adversative ("but")

## Boundness

Whether a morpheme is a free word or a bound clitic/suffix.
Relevant to acquisition: @cite{clark-2017} argues free morphemes
are acquired more readily than bound ones.
-/

namespace Core.Coordination

/-- Role of a coordination morpheme. -/
inductive CoordRole where
  /-- J particle: set intersection / conjunction proper
      (English "and", Hungarian "és", Georgian "da") -/
  | j
  /-- MU particle: subset/additive
      (Hungarian "is", Georgian "-c", Japanese "mo") -/
  | mu
  /-- Disjunction (English "or", Hungarian "vagy") -/
  | disj
  /-- Adversative (English "but", Hungarian "de") -/
  | advers
  deriving DecidableEq, Repr, BEq

/-- Morphological boundness: free word vs bound clitic/suffix. -/
inductive Boundness where
  /-- Independent word (Hungarian "is", English "and") -/
  | free
  /-- Clitic or suffix (Georgian "-c", Latin "-que") -/
  | bound
  deriving DecidableEq, Repr, BEq

end Core.Coordination
