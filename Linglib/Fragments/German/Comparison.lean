import Linglib.Syntax.Comparative

/-!
# German comparative data

German compares with *X ist größer als Y*: the particle *als* marks the
standard, the bound affix *-er* marks degree (never periphrastic for
adjectives), and the superlative is morphological (*am größten*). German is
absent from the 167-language WALS Ch 121A sample; its particle classification
is derived from the construction's anatomy (`als.type`), consistent with
[stassen-2013]'s criteria (the chapter cites German for the comparative affix)
and [haspelmath-2001]'s Standard Average European comparative-particle
feature. WALS Ch 81A classifies German as lacking a dominant word order (V2
main clauses, verb-final subordinate clauses).
-/

set_option autoImplicit false

namespace German.Comparison

open Comparative

/-- The *als*-comparative: particle-marked standard, bound degree affix. -/
def als : Comparative :=
  { standardMarker := some "als"
  , caseAssignment := .derived
  , degreeMarker := some "-er"
  , degreeMorphology := true }

/-- Bound comparative affix *-er*; no free degree word for adjectives. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative (*am größten*). -/
def superlative : SuperlativeStrategy := .morphological

end German.Comparison
