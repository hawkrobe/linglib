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
property of Tagalog (*kitá* vs *tayo*), several other Philippine languages,
and many Australian languages.
-/

set_option autoImplicit false

namespace Features.Clusivity

/-- Cysouw 2009 typology of clusivity systems.

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
      surfaces as a 1-dual-inclusive form) vs augmented (1+2+3); the
      exclusive remains a single category. Tagalog *kitá*/*tayo*/*kami*,
      many Australian languages. -/
  | minimalAugmented
  /-- Unit-augmented: minimal-augmented plus a separate 1+2+1 form
      ("we two and one other"); rare (e.g. Rembarrnga). -/
  | unitAugmented
  /-- No grammatical number distinction in pronouns at all (Pirahã *ti*
      'I/we'); the clusivity question is moot. -/
  | numberIndifferent
  deriving DecidableEq, Repr

namespace System

/-- All five system types in canonical order. -/
def all : List System :=
  [.noClusivity, .inclExcl, .minimalAugmented, .unitAugmented, .numberIndifferent]

/-- Does the system grammatically distinguish inclusive from exclusive? -/
def hasInclExcl : System → Bool
  | .noClusivity        => false
  | .numberIndifferent  => false
  | _                   => true

/-- Does the system distinguish minimal-inclusive from augmented-inclusive
    (i.e., is there a separate "we two" form for speaker + addressee only)? -/
def hasMinimalAugmented : System → Bool
  | .minimalAugmented => true
  | .unitAugmented    => true
  | _                 => false

end System

end Features.Clusivity
