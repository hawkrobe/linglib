import Linglib.Core.Relativization.Basic
import Linglib.Datasets.WALS.Features.F90D
import Linglib.Datasets.WALS.Features.F122A
import Linglib.Datasets.WALS.Features.F123A

/-!
# `RelativizationProfile`: per-language relativization typology

A WALS-style summary of a language's relativization system. Captures the
two strategy dimensions (Chs 122/123), the relative-clause position with
respect to the head noun, and the lowest position on the
@cite{keenan-comrie-1977} Accessibility Hierarchy that can be
relativized.

Per-language values live in `Fragments/{Lang}/Relativization.lean` as
`def relativization : RelativizationProfile`. WALS-aggregate cross-
linguistic findings live in `Typology/Relativization/Basic.lean`.

## Layer placement

Located in `Typology/` (not `Core/`) per the @cite{wals-2013}-aligned
substrate convention: typological summary records that aggregate
cross-linguistic data at the per-language level live alongside the other
domain summaries (`Typology/WordOrder.lean`, `Typology/Adposition.lean`,
`Typology/Indefinite.lean`, etc.). The lower-level relativization
primitives (`AHPosition`, `RCPosition`, `NPRelType`, `RelClauseMarker`)
remain in `Core/Relativization/Basic.lean` since they're framework-
agnostic structural pieces, not typological summaries.
-/

namespace Typology.Relativization

-- ============================================================================
-- Subject relativization strategies (WALS Ch 122)
-- ============================================================================

/-- WALS Ch 122: strategy used to relativize the subject position. -/
inductive SubjRelStrategy where
  /-- The relativized position is empty. E.g., English "the man [that _ left]". -/
  | gap
  /-- A resumptive pronoun fills the position. E.g., dialectal Arabic. -/
  | pronounRetention
  /-- A dedicated wh-element / relative pronoun fills the position and
      typically fronts. E.g., German "der Mann [der ging]". -/
  | relativePronoun
  /-- The head noun (or a full NP) is repeated inside the RC. -/
  | nonReduction
  /-- The language productively uses more than one of the above for
      subjects. WALS does not distinguish a "mixed" category; this is
      used only in our profiles. -/
  | mixed
  deriving DecidableEq, Repr

-- ============================================================================
-- Oblique relativization strategies (WALS Ch 123)
-- ============================================================================

/-- WALS Ch 123: strategy used to relativize oblique positions, or
whether obliques can be relativized at all. -/
inductive OblRelStrategy where
  /-- Gap on obliques (often with preposition stranding). -/
  | gap
  /-- Resumptive pronoun on obliques (more common than for subjects). -/
  | pronounRetention
  /-- Relative pronoun on obliques. E.g., English "in which", German "in der". -/
  | relativePronoun
  /-- Head noun repeated inside the RC. -/
  | nonReduction
  /-- Multiple strategies productively used. WALS does not distinguish a
      "mixed" category; used only in our profiles. -/
  | mixed
  /-- Obliques cannot be relativized at all in this language. -/
  | notRelativizable
  deriving DecidableEq, Repr

-- ============================================================================
-- Internally-headed strategy (WALS Ch 90D)
-- ============================================================================

/-- WALS Ch 90D: status of the internally-headed strategy in a language.

WALS distinguishes whether the internally-headed strategy is the dominant
relativization pattern, co-dominant with another (RelN, NRel, correlative,
double-headed), present as a non-dominant alternative, merely attested, or
absent entirely. -/
inductive InternallyHeadedStrategy where
  /-- Internally-headed is the dominant strategy. -/
  | dominant
  /-- Co-dominant with a relative-noun construction. -/
  | coRelN
  /-- Co-dominant with a noun-relative construction. -/
  | coNRel
  /-- Co-dominant with a correlative construction. -/
  | coCorrelative
  /-- Co-dominant with a double-headed construction. -/
  | coDoubleHeaded
  /-- Present as a non-dominant alternative. -/
  | nondominant
  /-- Attested but not dominant or co-dominant (WALS lumps this as "exists"). -/
  | attested
  /-- The internally-headed strategy is not attested in this language.
      WALS 90D codes only languages that *have* the strategy in some form, so
      this case is for hand-coded profiles whose Fragment asserts absence. -/
  | absent
  deriving DecidableEq, Repr

-- ============================================================================
-- Profile structure
-- ============================================================================

/-- A language's relativization profile: WALS Chs 122/123 strategies plus
RC position and AH cut-off. -/
structure RelativizationProfile where
  /-- Strategy used for relativizing subjects (Ch 122). -/
  subjStrategy : SubjRelStrategy
  /-- Strategy used for relativizing obliques (Ch 123). -/
  oblStrategy : OblRelStrategy
  /-- Position of the relative clause with respect to the head noun. -/
  rcPosition : Core.RCPosition
  /-- Lowest @cite{keenan-comrie-1977} AH position that can be relativized. -/
  lowestRelativizable : Core.AHPosition
  /-- Status of the head-internal relativization strategy (WALS 90D). Defaults
      to `.absent`, since most languages outside East Asia, Mesoamerica, and a
      few isolates lack this construction. -/
  internallyHeaded : InternallyHeadedStrategy := .absent
  /-- Free-text notes on the relativization system, including
      `@cite{...}` keys for hand-coded values. -/
  notes : String := ""
  deriving Repr, DecidableEq

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert a WALS 122A subject relativization value to `SubjRelStrategy`.
    WALS does not distinguish a "mixed" category, so languages whose
    profile is `.mixed` cannot be grounded against WALS via this converter
    alone. -/
def fromWALS122A : Datasets.WALS.F122A.SubjectRelativization → SubjRelStrategy
  | .relativePronoun => .relativePronoun
  | .nonReduction    => .nonReduction
  | .pronounRetention => .pronounRetention
  | .gap             => .gap

/-- Convert a WALS 123A oblique relativization value to `OblRelStrategy`.
    WALS `.notPossible` becomes `.notRelativizable`; `.mixed` profiles
    cannot be grounded against WALS via this converter. -/
def fromWALS123A : Datasets.WALS.F123A.ObliqueRelativization → OblRelStrategy
  | .relativePronoun => .relativePronoun
  | .nonReduction    => .nonReduction
  | .pronounRetention => .pronounRetention
  | .gap             => .gap
  | .notPossible     => .notRelativizable

/-- Convert a WALS 90D internally-headed value to `InternallyHeadedStrategy`.
    WALS does not code an `.absent` case (the chapter only sampled languages
    that *have* the strategy), so absence is asserted by hand in the Fragment. -/
def fromWALS90D : Datasets.WALS.F90D.InternallyHeadedRelativeClauses →
    InternallyHeadedStrategy
  | .relativeClauseDominant   => .dominant
  | .orReln                   => .coRelN
  | .orNrel                   => .coNRel
  | .orCorrelative            => .coCorrelative
  | .orDoubleHeaded           => .coDoubleHeaded
  | .occursAsNondominantType  => .nondominant
  | .exists_                  => .attested

end Typology.Relativization
