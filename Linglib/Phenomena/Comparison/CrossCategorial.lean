/-!
# Cross-Categorial Comparison Constructions

Construction-level data on Wellwood's (2015) cross-categorial parallels:
comparison constructions apply uniformly across nominal, verbal, and
adjectival domains, sharing the same DegP template.

This file focuses on the **construction-level** parallels: all three
domains use the same morphosyntactic template (`much`/`more` + comparative
morphology). The measured-domain-level predictions (mereological status,
dimensional restriction) are in `Studies/Wellwood2015/`.

## References

- Wellwood, A. (2015). On the semantics of comparison across categories.
- Bresnan, J. (1973). Syntax of the comparative clause construction.
- Hackl, M. (2000). Comparative quantifiers.
-/

namespace Phenomena.Comparison.CrossCategorial

-- ════════════════════════════════════════════════════
-- § 1. Cross-Categorial Parallels
-- ════════════════════════════════════════════════════

/-- A cross-categorial comparison construction template:
    the same DegP shell applies across syntactic categories. -/
structure CrossCategorialDatum where
  /-- Syntactic domain (nominal, verbal, adjectival) -/
  domain : String
  /-- Example comparative sentence -/
  comparativeExample : String
  /-- Example equative sentence -/
  equativeExample : String
  /-- The degree word used -/
  degreeWord : String
  deriving Repr

def crossCategorialExamples : List CrossCategorialDatum :=
  [ { domain := "adjectival"
    , comparativeExample := "Kim is taller than Lee"
    , equativeExample := "Kim is as tall as Lee"
    , degreeWord := "-er / as...as" }
  , { domain := "nominal"
    , comparativeExample := "Kim bought more coffee than Lee"
    , equativeExample := "Kim bought as much coffee as Lee"
    , degreeWord := "more / as much...as" }
  , { domain := "verbal"
    , comparativeExample := "Kim ran more than Lee"
    , equativeExample := "Kim ran as much as Lee"
    , degreeWord := "more / as much...as" }
  , { domain := "adverbial"
    , comparativeExample := "Kim ran faster than Lee"
    , equativeExample := "Kim ran as fast as Lee"
    , degreeWord := "-er / as...as" }
  ]

-- ════════════════════════════════════════════════════
-- § 2. Bresnan's Decomposition (Morphosyntax)
-- ════════════════════════════════════════════════════

/-- Bresnan (1973): `more` = `much` + `-er`.

    This decomposition predicts:
    - `much` is the degree head (selecting the measured domain)
    - `-er` is the comparative morpheme (introducing the standard)
    - Their combination `more` is suppletive for `much + -er`

    The same pattern holds across domains:
    - "more coffee" = much + -er + coffee
    - "more quickly" = much + -er + quickly
    - "taller" = -er + tall (no overt `much` for adjectives) -/
structure BresnanDecompositionDatum where
  surface : String
  underlying : String
  domain : String
  deriving Repr

def bresnanDecomposition : List BresnanDecompositionDatum :=
  [ { surface := "more coffee", underlying := "much-er coffee"
    , domain := "nominal" }
  , { surface := "ran more", underlying := "ran much-er"
    , domain := "verbal" }
  , { surface := "taller", underlying := "-er tall"
    , domain := "adjectival" }
  , { surface := "more quickly", underlying := "much-er quickly"
    , domain := "adverbial" }
  ]

end Phenomena.Comparison.CrossCategorial
