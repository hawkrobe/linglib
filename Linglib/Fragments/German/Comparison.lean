import Linglib.Syntax.Comparative

/-!
# German comparative profile

German marks the standard of comparison with the particle *als*, degree with the
bound affix *-er* (*größer*, never periphrastic for adjectives), and the superlative
morphologically (*am größten*). German is absent from the 167-language WALS Ch 121A
sample; the particle classification applies [stassen-2013]'s criteria (the chapter
cites German for the comparative affix) and matches [haspelmath-2001]'s Standard
Average European comparative-particle feature. No `basicOrder` is coded: WALS
Ch 81A classifies German as lacking a dominant word order (V2 main clauses,
verb-final subordinate clauses).
-/

set_option autoImplicit false

namespace German.Comparison

open Comparative

/-- German comparative profile. -/
def comparison : ComparativeProfile :=
  { language := "German"
  , iso := "deu"
  , comparativeType := .particle
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X ist größer als Y"
  , standardMarker := "als"
  , degreeMarker := "-er (suffix)" }

end German.Comparison
