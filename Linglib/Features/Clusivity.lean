import Linglib.Features.Person

/-!
# Clusivity systems — typology of inclusive/exclusive distinctions
@cite{cysouw-2009}

System-level typology of how a language encodes the inclusive/exclusive
distinction in 1pl pronouns. Per-referent person *categories*
(`s1`, `minIncl`, `augIncl`, `excl`, ...) live in
`Features/Person.lean::Category`; this file classifies *systems* by which
of those categories they grammatically distinguish.

The substrate cut is intentionally finer than WALS Ch 39 (which collapses
plain inclExcl with minimal-augmented into a single "inclusive/exclusive"
value). The minimal-augmented type — which licenses a 1-dual-inclusive
form in addition to a 1pl-inclusive — is the typologically distinctive
property of Tagalog (*kata* / *tayo*), several other Philippine languages,
and many Australian languages.

Scope: pronominal clusivity (independent personal pronouns). Verbal
clusivity (WALS Ch 40, `Pronoun.InclusiveExclusiveVerbal`) is a
separately-marked phenomenon that may dissociate from pronominal clusivity
(e.g. some Athabaskan languages). The five-value enum here is a first-cut
typology; @cite{cysouw-2009} discusses additional minor types
(degenerate-minimal-augmented, composite-unit-augmented) that this
substrate does not currently distinguish.
-/

set_option autoImplicit false

namespace Features.Clusivity

/-- Cysouw 2009 typology of pronominal clusivity systems.

The cuts: (a) is incl/excl distinguished at all? (b) is the inclusive
itself further split into minimal vs augmented? -/
inductive System where
  /-- No clusivity distinction; 1pl is one category (English *we*,
      German *wir*, Standard Mandarin *wǒmen*). -/
  | noClusivity
  /-- Plain incl/excl: separate 1pl forms for 1+2(+3) vs 1+3
      (Indonesian *kita*/*kami*, Tok Pisin *yumi*/*mipela*,
      Mandarin colloquial *zánmen*/*wǒmen*). -/
  | inclExcl
  /-- Minimal-augmented: inclusive further splits into minimal (1+2 only,
      surfaces as a 1-dual-inclusive form) vs augmented (1+2+others); the
      exclusive remains a single category. Tagalog *kata*/*tayo*/*kami*
      (per @cite{schachter-otanes-1972} Chart 7), many Australian
      languages. -/
  | minimalAugmented
  /-- Unit-augmented: minimal-augmented plus a separate 1+2+1 form
      ("we two and one other"); rare (e.g. Rembarrnga). -/
  | unitAugmented
  /-- No grammatical number distinction in pronouns at all (Pirahã *ti*
      'I/we'); the clusivity question is moot. -/
  | numberIndifferent
  deriving DecidableEq, Repr

namespace System

/-- The 1st-person `Features.Person.Category` distinctions a system
    grammatically encodes. Captures Cysouw 2009's typology operationally:
    `.noClusivity` collapses 1+2 and 1+3 into a single 1pl
    (modeled here by listing only `.augIncl`, since `.augIncl` is the
    closest catch-all for collapsed first-person plural); `.inclExcl`
    distinguishes them; `.minimalAugmented` and `.unitAugmented` further
    split inclusive into minimal (`.minIncl`) vs augmented (`.augIncl`).
    `.numberIndifferent` languages have no plural form, so only `.s1`. -/
def distinguishedCategories : System → List Features.Person.Category
  | .noClusivity        => [.augIncl]                     -- single 1pl form
  | .inclExcl           => [.augIncl, .excl]              -- 1+2(+3) vs 1+3
  | .minimalAugmented   => [.minIncl, .augIncl, .excl]    -- + 1+2 minimal
  | .unitAugmented      => [.minIncl, .augIncl, .excl]    -- + 1+2+1 not in Category
  | .numberIndifferent  => []                             -- no 1pl distinction

/-- A system grammatically distinguishes inclusive from exclusive iff
    its first-person inventory contains an exclusive category. Derived
    from `distinguishedCategories` (was a stipulated pattern-match before
    the 0.230.544 audit). -/
def hasInclExcl (s : System) : Bool :=
  s.distinguishedCategories.contains .excl

/-- A system distinguishes minimal-inclusive from augmented-inclusive iff
    its first-person inventory contains the minimal-inclusive category. -/
def hasMinimalAugmented (s : System) : Bool :=
  s.distinguishedCategories.contains .minIncl

end System

end Features.Clusivity
