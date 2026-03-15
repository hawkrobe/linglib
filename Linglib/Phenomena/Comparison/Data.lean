import Linglib.Phenomena.Comparison.Typology

/-!
# Comparison Constructions: Overview
@cite{heim-2001} @cite{kennedy-2007} @cite{klein-1980} @cite{schwarzschild-2008} @cite{stassen-2013} @cite{wellwood-2015}

Empirical data on comparison constructions across languages. This directory
collects phenomena specifically about **constructions that compare** — the
syntactic and semantic mechanisms languages use to express comparative,
equative, and superlative meanings.

Comparison constructions are distinct from **gradability** (the property of
predicates that admit degree modification) and **imprecision** (tolerance-based
approximate truth). A predicate can be gradable without appearing in any
comparison construction, and comparison constructions apply across syntactic
categories (nominal, verbal, adjectival — @cite{wellwood-2015}).

## Organization

```
Comparison/
├── Data.lean — this file: cross-construction overview
├── Typology.lean — WALS 121 cross-linguistic typology + Stassen 1985
├── Comparative/
│ ├── Data.lean — basic comparative judgments, phrasal vs. clausal
│ ├── Differential.lean — "3 inches taller", factor phrases
│ └── Subcomparative.lean — "longer than the desk is wide"
├── Equative/
│ └── Data.lean — "as tall as", at-least vs. exactly readings
├── Superlative/
│ └── Data.lean — absolute vs. relative, focus
├── DegreeQuestion/
│ └── Data.lean — "how tall", negative islands, modal obviation
├── CrossCategorial.lean — construction-level cross-categorial parallels
└── Studies/
    ├── Kennedy2007.lean — degree semantics bridge
    └── Kennedy2007Typology.lean — typology–fragment bridge
```

## Typological types

Cross-linguistic comparative construction types (`ComparativeType`,
`ComparativeType1985`) and their parameters (`CaseAssignment`,
`FixedCaseEncoding`, `DegreeWordType`, `SuperlativeStrategy`) are defined
in `Typology.lean` and re-exported here.
-/

namespace Phenomena.Comparison

-- Re-export typological types for convenience
open Phenomena.Comparison.Typology

-- ════════════════════════════════════════════════════
-- § 1. Comparison Construction Types
-- ════════════════════════════════════════════════════

/-- The major comparison construction types found cross-linguistically. -/
inductive ComparisonConstruction where
  | comparative     -- "taller than", "more expensive than"
  | equative        -- "as tall as"
  | superlative     -- "tallest", "most expensive"
  | excessive       -- "too tall" (implicit comparison to a standard)
  | sufficiency     -- "tall enough" (implicit comparison to a standard)
  | degreeQuestion  -- "how tall" (comparison to answer alternatives)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Comparison Domain (Cross-Categorial)
-- ════════════════════════════════════════════════════

/-- What is being compared — the syntactic category of the gradable
    expression, following @cite{wellwood-2015}.

    The key insight: comparison constructions apply uniformly across
    categories; what varies is the measured domain (entity, event, state). -/
inductive ComparisonDomain where
  | adjectival   -- "taller than", "more expensive than"
  | nominal      -- "more coffee than", "fewer books than"
  | verbal       -- "ran more than", "sang louder than"
  | adverbial    -- "more quickly than", "as carefully as"
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Degree Morphology
-- ════════════════════════════════════════════════════

/-- How degree comparison is morphologically realized in a given form.

    This is orthogonal to `DegreeWordType` (in `Typology.lean`), which
    classifies whether a *language* has degree marking at all.
    `DegreeMorphology` classifies a specific *form*: English "taller" is
    synthetic, "more tall" is analytic, "better" is suppletive — all in
    a language that `DegreeWordType` classifies as `.hasDegreeWord`. -/
inductive DegreeMorphology where
  | synthetic   -- "-er"/"-est" (English, German)
  | analytic    -- "more"/"most" (English, French)
  | suppletive  -- "good"/"better"/"best" (English, Latin)
  | mixed       -- both synthetic and analytic available
  deriving DecidableEq, BEq, Repr

end Phenomena.Comparison
