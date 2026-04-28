/-!
# Temporal Connective Typology — substrate
@cite{giannakidou-2002} @cite{karttunen-1974}

Type-level enums + per-language data record for the cross-linguistic
typology of the durative/eventive *until* distinction following
@cite{giannakidou-2002}.

## The four strategies

1. **Three-way lexicalization** (e.g., Greek): separate lexemes for
   *before*, durative *until*, and eventive NPI-*until*.
2. **Two-way lexicalization** (e.g., Icelandic, Finnish): separate
   lexemes for durative *until* and eventive NPI-*until*; *before* may
   or may not be one of them.
3. **Ambiguity** (e.g., English): a single *until* lexeme is ambiguous
   between durative (positive contexts) and eventive/NPI (negative
   contexts).
4. **PPI replacement** (e.g., Dutch, German): durative *until* cannot
   co-occur with negation; a separate PPI supplies the 'not before'
   meaning without negation.

## What lives here vs. `Phenomena/TemporalConnectives/Studies/Giannakidou2002.lean`

This file holds the substrate types (the strategy enum + the per-language
record schema). Per-language entries + sample-restricted typological
theorems + Fragment grounding live in the Giannakidou 2002 study file.
-/

namespace Typology.TemporalConnectives

/-- How a language handles the durative/eventive *until* distinction
    (@cite{giannakidou-2002}). -/
inductive UntilStrategy where
  /-- Three distinct lexemes: *before*, durative *until*, eventive NPI-*until*.
      Greek: *prin*, *mexri*, *para monon*. -/
  | threeWay
  /-- Two distinct lexemes: durative *until* and eventive NPI-*until*.
      Icelandic: *flanga til*, *fyrr en*. Finnish: *kunnes*, *ennenkuin*. -/
  | twoWay
  /-- Single ambiguous lexeme, disambiguated by negation context.
      English: *until*. -/
  | ambiguous
  /-- Durative *until* blocked under negation; PPI replaces NPI-*until*.
      Dutch: *tot*, *pas*. German: *bis*, *erst*. -/
  | ppiReplacement
  deriving DecidableEq, Repr

/-- A language's strategy for the two-*until* distinction. -/
structure UntilTypologyEntry where
  language : String
  strategy : UntilStrategy
  /-- Surface form for durative *until*. -/
  durativeForm : String
  /-- Surface form for eventive *until* (NPI or PPI). -/
  eventiveForm : String
  /-- Is the eventive form morphologically built on *before*?
      (@cite{karttunen-1974}'s identity NPI-*until* = ¬*before*.) -/
  eventiveMorphBeforeBased : Bool
  /-- Does the language have overt perfective/imperfective marking?
      Orthogonal to the lexicalization choice. -/
  hasOvertAspect : Bool
  deriving Repr

end Typology.TemporalConnectives
