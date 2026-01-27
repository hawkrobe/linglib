/-
# Hurford's Constraint: Empirical Data

Disjunctions where one disjunct entails the other are infelicitous,
unless exhaustification can rescue them.

## The Pattern

- "#John is American or Californian" (Californian ⊂ American) — BAD
- "Mary read some or all of the books" (some ⊂ all after exh) — OK (rescued)

## Key References

- Hurford, J. (1974). Exclusive or inclusive disjunction. Foundations of Language.
- Chierchia, Fox & Spector (2012). Scalar implicature as a grammatical phenomenon.
- Fox & Spector (2018). Economy and embedded exhaustification.
-/

namespace Phenomena.ScalarImplicatures.Hurford

-- ============================================================================
-- PART 1: Hurford Constraint Data Structure
-- ============================================================================

/--
A potential Hurford violation: a disjunction "A or B" where
one disjunct entails the other.
-/
structure HurfordDatum where
  /-- The disjunction sentence -/
  sentence : String
  /-- First disjunct -/
  disjunctA : String
  /-- Second disjunct -/
  disjunctB : String
  /-- Which direction is the entailment? -/
  entailmentDirection : String  -- "A ⊆ B" or "B ⊆ A"
  /-- Is the sentence felicitous? -/
  felicitous : Bool
  /-- If felicitous, how is it rescued? -/
  rescueMethod : Option String
  deriving Repr

-- ============================================================================
-- PART 2: Unrescued Violations (Infelicitous)
-- ============================================================================

/--
Classic Hurford violation: hyponym or hypernym.
"#John is American or Californian" — Californian entails American.
-/
def americanCalifornian : HurfordDatum :=
  { sentence := "#John is American or Californian"
  , disjunctA := "American"
  , disjunctB := "Californian"
  , entailmentDirection := "B ⊆ A"  -- Californian ⊆ American
  , felicitous := false
  , rescueMethod := none
  }

/--
"#John is a bachelor or unmarried" — bachelor entails unmarried.
-/
def bachelorUnmarried : HurfordDatum :=
  { sentence := "#John is a bachelor or unmarried"
  , disjunctA := "bachelor"
  , disjunctB := "unmarried"
  , entailmentDirection := "A ⊆ B"  -- bachelor ⊆ unmarried
  , felicitous := false
  , rescueMethod := none
  }

/--
"#The number is even or divisible by 2"
-/
def evenDivisibleBy2 : HurfordDatum :=
  { sentence := "#The number is even or divisible by 2"
  , disjunctA := "even"
  , disjunctB := "divisible by 2"
  , entailmentDirection := "A = B"  -- equivalent
  , felicitous := false
  , rescueMethod := none
  }

-- ============================================================================
-- PART 3: Rescued Violations (Felicitous)
-- ============================================================================

/--
Rescued by exhaustification: "some or all".
exh(some) = "some but not all", which doesn't entail "all".
-/
def someOrAll : HurfordDatum :=
  { sentence := "Mary read some or all of the books"
  , disjunctA := "some"
  , disjunctB := "all"
  , entailmentDirection := "B ⊆ A"  -- all ⊆ some (before exh)
  , felicitous := true
  , rescueMethod := some "exh(some) = some but not all"
  }

/--
Rescued: "possible or necessary".
exh(possible) = "possible but not necessary", doesn't entail "necessary".
-/
def possibleOrNecessary : HurfordDatum :=
  { sentence := "It's possible or even necessary that John will come"
  , disjunctA := "possible"
  , disjunctB := "necessary"
  , entailmentDirection := "B ⊆ A"  -- necessary ⊆ possible
  , felicitous := true
  , rescueMethod := some "exh(possible) breaks entailment"
  }

/--
Rescued: "three or all" (distant entailing disjunction).
exh(three) = "exactly three", which doesn't entail "all".
-/
def threeOrAll : HurfordDatum :=
  { sentence := "John solved three or all of the problems"
  , disjunctA := "three"
  , disjunctB := "all"
  , entailmentDirection := "B ⊆ A"  -- all ⊆ at-least-three
  , felicitous := true
  , rescueMethod := some "exh(three) = exactly three"
  }

-- ============================================================================
-- PART 4: Collections
-- ============================================================================

/-- Infelicitous Hurford violations. -/
def violations : List HurfordDatum :=
  [americanCalifornian, bachelorUnmarried, evenDivisibleBy2]

/-- Felicitous (rescued) cases. -/
def rescuedCases : List HurfordDatum :=
  [someOrAll, possibleOrNecessary, threeOrAll]

/-- All Hurford data. -/
def allHurfordData : List HurfordDatum :=
  violations ++ rescuedCases

-- ============================================================================
-- PART 5: Basic Theorems About the Data
-- ============================================================================

/-- All violations are infelicitous. -/
theorem violations_infelicitous : violations.all (·.felicitous == false) := by
  native_decide

/-- All rescued cases are felicitous. -/
theorem rescued_felicitous : rescuedCases.all (·.felicitous == true) := by
  native_decide

/-- All rescued cases have a rescue method. -/
theorem rescued_have_method : rescuedCases.all (·.rescueMethod.isSome) := by
  native_decide

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Data Provided

| Example | Felicitous | Rescue |
|---------|------------|--------|
| American or Californian | No | — |
| bachelor or unmarried | No | — |
| some or all | Yes | exh(some) |
| possible or necessary | Yes | exh(possible) |
| three or all | Yes | exh(three) |

## Interface for Theory

`Theories/NeoGricean/ScaleSemantics.lean` provides:
- `HurfordSemantic World` with semantic content
- `HurfordSemantic.isRescued` predicate

Theory can prove:
```
theorem hurford_rescue_iff_exh_breaks_entailment (h : HurfordSemantic World) :
    h.isRescued ↔ ¬(exhIE h.alts h.disjunctA ⊆ₚ h.disjunctB) ∨ ...
```
-/

end Phenomena.ScalarImplicatures.Hurford
