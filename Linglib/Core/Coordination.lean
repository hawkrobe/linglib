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
- `negDisj` — negative disjunction ("nor")
- `negCoord` — negative coordination ("neither...nor")

## Boundness

Whether a morpheme is a free word or a bound clitic/suffix.
Relevant to acquisition: @cite{clark-2017} argues free morphemes
are acquired more readily than bound ones.

## CoordEntry

Unified coordination morpheme entry used by all Fragment lexicons.

## ConjunctionStrategy

Cross-linguistic conjunction strategy from @cite{mitrovic-sauerland-2014}:
languages vary in which semantic pieces (J, MU, type-shifter) are
overtly realized.
-/

namespace Core.Coordination

/-- Role of a coordination morpheme. -/
inductive CoordRole where
  /-- J particle: set intersection / conjunction proper
      (English "and", Hungarian "es", Georgian "da") -/
  | j
  /-- MU particle: subset/additive
      (Hungarian "is", Georgian "-c", Japanese "mo") -/
  | mu
  /-- Disjunction (English "or", Hungarian "vagy") -/
  | disj
  /-- Adversative (English "but", Hungarian "de") -/
  | advers
  /-- Negative disjunction (Irish "na" = "nor") -/
  | negDisj
  /-- Negative coordination (Latin "neque/nec" = "neither...nor") -/
  | negCoord
  deriving DecidableEq, Repr, BEq

/-- Morphological boundness: free word vs bound clitic/suffix. -/
inductive Boundness where
  /-- Independent word (Hungarian "is", English "and") -/
  | free
  /-- Clitic or suffix (Georgian "-c", Latin "-que") -/
  | bound
  deriving DecidableEq, Repr, BEq

/-- A coordination morpheme entry, used by all Fragment lexicons. -/
structure CoordEntry where
  /-- Surface form of the morpheme. -/
  form : String
  /-- Gloss / translation. -/
  gloss : String
  /-- Role in the M&S decomposition. -/
  role : CoordRole
  /-- Whether this morpheme is free or bound. -/
  boundness : Boundness
  /-- Does this morpheme also serve as an additive/focus particle? -/
  alsoAdditive : Bool := false
  /-- Does this morpheme also serve as a quantifier particle?
      Japanese "mo" and "ka" both do — this field tracks the
      coordination-quantification connection. -/
  alsoQuantifier : Bool := false
  /-- Can this morpheme be used in correlative (bisyndetic) patterns?
      Latin "et...et", "aut...aut". -/
  correlative : Bool := false
  /-- Notes on usage or distribution. -/
  note : String := ""
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Conjunction Strategy (@cite{mitrovic-sauerland-2014})
-- ============================================================================

/--
Cross-linguistic conjunction strategy.

@cite{mitrovic-sauerland-2014} decompose DP conjunction into three
semantic pieces: J (set intersection), MU (subset), and a type-shifter.
Languages vary in which pieces are overtly realized.
-/
inductive ConjunctionStrategy where
  /-- Only J particle overt (e.g., English "and", Hungarian "es", Georgian "da") -/
  | jOnly
  /-- Only MU particles overt (e.g., Japanese "mo...mo", Hungarian "is...is",
      Georgian "-c...-c") -/
  | muOnly
  /-- Both J and MU overt (e.g., Hungarian "is es...is", Georgian "-c da...-c") -/
  | jMu
  deriving DecidableEq, Repr

/--
Number of overt functional morphemes per strategy.

Under @cite{mitrovic-sauerland-2016}, the underlying structure always has 3 semantic pieces
(J + MU1 + MU2). What varies is how many are pronounced.
-/
def ConjunctionStrategy.overtMorphemeCount : ConjunctionStrategy → Nat
  | .jOnly  => 1  -- only J pronounced
  | .muOnly => 2  -- both MUs pronounced
  | .jMu    => 3  -- J + both MUs pronounced

/--
Under @cite{mitrovic-sauerland-2016}, there are always 3 semantic pieces.
The transparency ratio measures how many are overtly realized.
-/
def ConjunctionStrategy.semanticPieceCount : Nat := 3

/--
@cite{mitrovic-sauerland-2016} + Transparency Principle predicts: more overt morphemes -> easier
to acquire (closer to 1-to-1 form-meaning mapping).
-/
def ConjunctionStrategy.predictedTransparency : ConjunctionStrategy → Nat :=
  ConjunctionStrategy.overtMorphemeCount

-- ============================================================================
-- Structural Symmetry (@cite{schwarzer-2026})
-- ============================================================================

/--
Structural symmetry of a coordinate phrase.

The three groups of analyses for selection-violating coordination
(@cite{schwarzer-2026}) disagree on this parameter:
- **Bottom-up accounts** assume `asymmetric` structure: the first conjunct
  is structurally more prominent (c-commands the second), so only it must
  satisfy the selector's c-selectional requirements.
- **Linear/temporal closeness accounts** are compatible with either, but
  their predictions derive from linear/temporal order, not structure.
- **Symmetric accounts** (@cite{neeleman-etal-2022}, @cite{przepiorkowski-2024})
  posit flat or multidominance structures with no structural prominence.
-/
inductive CoordSymmetry where
  /-- Flat or multidominance: no conjunct is structurally more prominent. -/
  | symmetric
  /-- Binary &P: first conjunct is structurally more prominent
      (c-commands the second conjunct). -/
  | asymmetric
  deriving DecidableEq, Repr, BEq

end Core.Coordination
