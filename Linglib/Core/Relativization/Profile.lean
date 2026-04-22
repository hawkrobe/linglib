import Linglib.Core.Relativization.Basic
import Linglib.Core.Relativization.Hierarchy
import Linglib.Core.WALS.Features.F122A
import Linglib.Core.WALS.Features.F123A

/-!
# `RelativizationProfile`: per-language relativization typology

A WALS-style summary of a language's relativization system, suitable for
inclusion as one field of `Core.Typology.LanguageProfile`. Captures the
two strategy dimensions (Chs 122/123), the relative-clause position with
respect to the head noun, and the lowest position on the
@cite{keenan-comrie-1977} Accessibility Hierarchy that can be
relativized.

The Fragment for each language defines its `RelativizationProfile`
inside `Fragments/{Lang}/Typology.lean`; the cross-linguistic sample in
`Phenomena/Relativization/Typology.lean` aggregates Fragment values via
`LanguageProfile.relativization`.
-/

namespace Core.Relativization

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
  /-- Free-text notes on the relativization system, including
      `@cite{...}` keys for hand-coded values. -/
  notes : String := ""
  deriving Repr, DecidableEq

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert a WALS 122A subject relativization value to `SubjRelStrategy`.
    WALS does not distinguish a "mixed" category, so languages whose
    profile is `.mixed` cannot be grounded against WALS via this
    converter alone — see the per-language theorems in
    `Phenomena/Relativization/Typology.lean`. -/
def fromWALS122A : Core.WALS.F122A.SubjectRelativization → SubjRelStrategy
  | .relativePronoun => .relativePronoun
  | .nonReduction    => .nonReduction
  | .pronounRetention => .pronounRetention
  | .gap             => .gap

/-- Convert a WALS 123A oblique relativization value to `OblRelStrategy`.
    WALS `.notPossible` becomes `.notRelativizable`; `.mixed` profiles
    cannot be grounded against WALS via this converter. -/
def fromWALS123A : Core.WALS.F123A.ObliqueRelativization → OblRelStrategy
  | .relativePronoun => .relativePronoun
  | .nonReduction    => .nonReduction
  | .pronounRetention => .pronounRetention
  | .gap             => .gap
  | .notPossible     => .notRelativizable

end Core.Relativization
