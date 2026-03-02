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
categories (nominal, verbal, adjectival — Wellwood 2015).

## Organization

```
Comparison/
├── Data.lean — this file: cross-construction overview
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
├── CrossCategorial.lean — construction-level Wellwood-style parallels
├── Typology.lean — WALS 121 cross-linguistic typology (from Gradability/)
└── TypologyBridge.lean — typology–fragment bridge (from Gradability/)
```

-/

namespace Phenomena.Comparison

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
-- § 2. Comparative Strategy
-- ════════════════════════════════════════════════════

/-- How the standard of comparison is introduced syntactically.
    These strategies may co-occur within a single language. -/
inductive ComparativeStrategy where
  | phrasalThan   -- "taller than Bill" — DP complement of *than*
  | clausalThan   -- "taller than Bill is" — CP complement of *than*
  | exceed        -- "surpass Bill in height" — exceed predicate
  | conjoined     -- "Bill is tall, Mary is taller" — juxtaposition
  | locational    -- "tall from Bill" — locative marker (many languages)
  | particle      -- degree word + standard marker
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Comparison Domain (Cross-Categorial)
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
-- § 4. Degree Morphology
-- ════════════════════════════════════════════════════

/-- How degree comparison is morphologically encoded. -/
inductive DegreeMorphology where
  | synthetic   -- "-er"/"-est" (English, German)
  | analytic    -- "more"/"most" (English, French)
  | suppletive  -- "good"/"better"/"best" (English, Latin)
  | mixed       -- both synthetic and analytic available
  deriving DecidableEq, BEq, Repr

end Phenomena.Comparison
