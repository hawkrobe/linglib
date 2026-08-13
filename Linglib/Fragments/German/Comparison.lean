import Linglib.Syntax.Comparative

/-!
# German comparative data

German marks the standard of comparison with the particle *als*, degree with the
bound affix *-er* (*größer*, never periphrastic for adjectives), and the
superlative morphologically (*am größten*). German is absent from the
167-language WALS Ch 121A sample, so `comparativeType` is coded here: it applies
[stassen-2013]'s criteria (the chapter cites German for the comparative affix)
and matches [haspelmath-2001]'s Standard Average European comparative-particle
feature. WALS Ch 81A classifies German as lacking a dominant word order (V2 main
clauses, verb-final subordinate clauses).
-/

set_option autoImplicit false

namespace German.Comparison

open Comparative

/-- Particle comparative — grammar-based coding; German is uncoded in
    WALS Ch 121A. -/
def comparativeType : ComparativeType := .particle

/-- Bound comparative affix *-er*; no free degree word for adjectives. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative (*am größten*). -/
def superlative : SuperlativeStrategy := .morphological

/-- Illustrative comparative. -/
def comparativeForm : String := "X ist größer als Y"

/-- The comparative particle marking the standard. -/
def standardMarker : String := "als"

/-- The bound comparative affix. -/
def degreeMarker : String := "-er"

end German.Comparison
