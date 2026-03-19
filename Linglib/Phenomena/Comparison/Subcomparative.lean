/-!
# Subcomparatives
@cite{bhatt-pancheva-2004} @cite{kennedy-1999} @cite{lechner-2004} @cite{schwarzschild-2008}

Empirical data on subcomparatives — comparative constructions where the
matrix and embedded predicates differ ("longer than the desk is wide").

## Key Empirical Patterns

1. **Subcomparatives require clausal standards**: "*taller than wide" is
   ungrammatical; the standard must be a full clause.
2. **Cross-dimensional comparison**: subcomparatives compare different
   scales, so the degrees must be commensurable (both measured in inches,
   for example).
3. **Cross-linguistic variation**: subcomparatives are unavailable in
   many languages (German allows them freely; Japanese restricts them).

-/

namespace Phenomena.Comparison.Subcomparative

-- ════════════════════════════════════════════════════
-- § 1. Basic Subcomparative Data
-- ════════════════════════════════════════════════════

/-- A subcomparative judgment. -/
structure SubcomparativeDatum where
  sentence : String
  acceptable : Bool
  /-- The matrix predicate (e.g., "long") -/
  matrixPredicate : String
  /-- The embedded predicate (e.g., "wide") -/
  embeddedPredicate : String
  /-- Are the dimensions commensurable? -/
  commensurable : Bool
  deriving Repr

def subcomparativeExamples : List SubcomparativeDatum :=
  [ { sentence := "The table is longer than the desk is wide"
    , acceptable := true
    , matrixPredicate := "long", embeddedPredicate := "wide"
    , commensurable := true }
  , { sentence := "The building is taller than the field is wide"
    , acceptable := true
    , matrixPredicate := "tall", embeddedPredicate := "wide"
    , commensurable := true }
  , { sentence := "??The soup is hotter than the dress is expensive"
    , acceptable := false
    , matrixPredicate := "hot", embeddedPredicate := "expensive"
    , commensurable := false }
  , { sentence := "More students passed than professors failed"
    , acceptable := true
    , matrixPredicate := "many (students)", embeddedPredicate := "many (professors)"
    , commensurable := true }
  ]

-- ════════════════════════════════════════════════════
-- § 2. Cross-Linguistic Availability
-- ════════════════════════════════════════════════════

/-- Cross-linguistic variation in subcomparative availability. -/
structure SubcomparativeTypologyDatum where
  language : String
  available : Bool
  note : String := ""
  deriving Repr

def typologyData : List SubcomparativeTypologyDatum :=
  [ { language := "English", available := true }
  , { language := "German", available := true }
  , { language := "French", available := true }
  , { language := "Japanese", available := false
    , note := "No clausal comparatives of this type" }
  , { language := "Mandarin", available := false
    , note := "Exceed-type comparatives don't support subcomparatives" }
  ]

end Phenomena.Comparison.Subcomparative
