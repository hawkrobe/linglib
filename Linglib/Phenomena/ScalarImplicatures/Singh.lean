/-
# Singh's Asymmetry: Empirical Data

Order matters in disjunctions with scalar terms.
"A or B, or both" is OK, but "#both, or A or B" is odd.

## The Pattern

Singh (2008) observed:
- "Mary read A or B, or both" (weak-first) - Felicitous
- "#Mary read both, or A or B" (strong-first) - Infelicitous

Fox & Spector (2018) explain this via economy:
- In weak-first, exh can be embedded in "A or B" (strengthening)
- In strong-first, exh in "both" would be vacuous (blocked)

## Key References

- Singh, R. (2008). On the interpretation of disjunction.
- Fox & Spector (2018). Economy and embedded exhaustification.
-/

namespace Phenomena.ScalarImplicatures.Singh

-- ============================================================================
-- PART 1: Singh Asymmetry Data Structure
-- ============================================================================

/--
A Singh-style disjunction where one disjunct is stronger than the other.
-/
structure SinghDatum where
  /-- The full sentence -/
  sentence : String
  /-- The weaker disjunct (e.g., "A or B") -/
  weakerDisjunct : String
  /-- The stronger disjunct (e.g., "A and B" / "both") -/
  strongerDisjunct : String
  /-- Is the weaker mentioned first? -/
  weakerFirst : Bool
  /-- Is the sentence felicitous? -/
  felicitous : Bool
  deriving Repr

-- ============================================================================
-- PART 2: Weak-First Cases (Felicitous)
-- ============================================================================

/--
Classic Singh example: weak-first is OK.
"Mary solved problem A or B, or both"
-/
def orThenBoth : SinghDatum :=
  { sentence := "Mary solved problem A or problem B, or both"
  , weakerDisjunct := "A or B"
  , strongerDisjunct := "both"
  , weakerFirst := true
  , felicitous := true
  }

/--
"John ate cake or pie, or both"
-/
def cakeOrPieOrBoth : SinghDatum :=
  { sentence := "John ate cake or pie, or both"
  , weakerDisjunct := "cake or pie"
  , strongerDisjunct := "both"
  , weakerFirst := true
  , felicitous := true
  }

/--
"It's possible or necessary that it will rain"
-/
def possibleOrNecessary : SinghDatum :=
  { sentence := "It's possible or even necessary that it will rain"
  , weakerDisjunct := "possible"
  , strongerDisjunct := "necessary"
  , weakerFirst := true
  , felicitous := true
  }

-- ============================================================================
-- PART 3: Strong-First Cases (Infelicitous)
-- ============================================================================

/--
Strong-first is odd: "#both, or A or B"
-/
def bothThenOr : SinghDatum :=
  { sentence := "#Mary solved both, or problem A or problem B"
  , weakerDisjunct := "A or B"
  , strongerDisjunct := "both"
  , weakerFirst := false
  , felicitous := false
  }

/--
"#John ate both, or cake or pie"
-/
def bothThenCakeOrPie : SinghDatum :=
  { sentence := "#John ate both, or cake or pie"
  , weakerDisjunct := "cake or pie"
  , strongerDisjunct := "both"
  , weakerFirst := false
  , felicitous := false
  }

/--
"#It's necessary or possible that it will rain"
(Strong-first with modals)
-/
def necessaryOrPossible : SinghDatum :=
  { sentence := "?It's necessary or at least possible that it will rain"
  , weakerDisjunct := "possible"
  , strongerDisjunct := "necessary"
  , weakerFirst := false
  , felicitous := false  -- degraded, though "at least" helps
  }

-- ============================================================================
-- PART 4: Collections
-- ============================================================================

/-- Weak-first (felicitous) cases. -/
def weakFirstCases : List SinghDatum :=
  [orThenBoth, cakeOrPieOrBoth, possibleOrNecessary]

/-- Strong-first (infelicitous) cases. -/
def strongFirstCases : List SinghDatum :=
  [bothThenOr, bothThenCakeOrPie, necessaryOrPossible]

/-- All Singh data. -/
def allSinghData : List SinghDatum :=
  weakFirstCases ++ strongFirstCases

-- ============================================================================
-- PART 5: Basic Theorems About the Data
-- ============================================================================

/-- Weak-first cases are felicitous. -/
theorem weakFirst_felicitous : weakFirstCases.all (·.felicitous == true) := by
  native_decide

/-- Strong-first cases are infelicitous. -/
theorem strongFirst_infelicitous : strongFirstCases.all (·.felicitous == false) := by
  native_decide

/-- All weak-first cases have weakerFirst = true. -/
theorem weakFirst_order : weakFirstCases.all (·.weakerFirst == true) := by
  native_decide

/-- All strong-first cases have weakerFirst = false. -/
theorem strongFirst_order : strongFirstCases.all (·.weakerFirst == false) := by
  native_decide

/--
**The Singh Asymmetry**: felicitous ↔ weakerFirst
(at the data level; theory explains WHY)
-/
theorem singh_asymmetry :
    allSinghData.all (fun d => d.felicitous == d.weakerFirst) := by
  native_decide

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Data Provided

| Example | Order | Felicitous |
|---------|-------|------------|
| A or B, or both | weak-first | Yes |
| cake or pie, or both | weak-first | Yes |
| #both, or A or B | strong-first | No |
| #both, or cake or pie | strong-first | No |

## Interface for Theory

`Theories/NeoGricean/ScaleSemantics.lean` provides:
- `SinghSemantic World` with semantic content
- `SinghSemantic.exhBreaksEntailment` predicate
- `SinghSemantic.predictedFelicitous` predicate

Theory (`Theories/NeoGricean/FoxSpector2018.lean`) can prove:
```
theorem singh_from_economy (s : SinghSemantic World) :
    s.predictedFelicitous ↔ s.weakerFirst ∧ s.exhBreaksEntailment
```

## Key Insight

The asymmetry `felicitous ↔ weakerFirst` is captured by `singh_asymmetry`.
Fox & Spector (2018) EXPLAIN this via economy on embedded exhaustification.
-/

end Phenomena.ScalarImplicatures.Singh
