/-
# Gradable Nouns and Nominal Degree Semantics

Morzycki (2009) "Degree modification of gradable nouns: size adjectives
and adnominal degree morphemes" Natural Language Semantics 17:175-203.

## Core Insight

Gradable nouns (idiot, fan, smoker) have **degree arguments** and denote
**measure functions**, just like gradable adjectives:

```
⟦tall⟧ = λx.ιd[x is d-tall]     : e → d
⟦idiot⟧ = λx.ιd[x is d-idiotic] : e → d
```

## Key Phenomena

"Big idiot" has a DEGREE reading (high idiocy), not just physical size.
This reading:
1. Only available in attributive position (Position Generalization)
2. Only available for BIGNESS adjectives (Bigness Generalization)

## Formal Analysis

Size adjectives in degree readings are introduced by MEASN:

```
⟦MEASN⟧ = λg.λm.λx. [min{d : d ∈ scale(g) ∧ m(d)} ≤ g(x)] ∧ [standard(g) ≤ g(x)]
```

The Bigness Generalization follows from scale structure:
- For "big": min{d : big(d)} is some positive threshold
- For "small": min{d : small(d)} = d₀ (always the scale minimum)
  → The size adjective becomes vacuous!

## References

- Morzycki, M. (2009). Degree modification of gradable nouns.
  Natural Language Semantics, 17(3), 175-203.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification,
  and the semantics of gradable predicates. Language, 81(2), 345-381.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

namespace Montague.Lexicon.GradableNouns

-- ============================================================================
-- PART 1: Degrees and Scales
-- ============================================================================

/-- A degree on a scale (discretized) -/
inductive Degree where
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | d9 | d10
  deriving Repr, DecidableEq, BEq, Ord

def Degree.toNat : Degree → Nat
  | .d0 => 0 | .d1 => 1 | .d2 => 2 | .d3 => 3 | .d4 => 4
  | .d5 => 5 | .d6 => 6 | .d7 => 7 | .d8 => 8 | .d9 => 9 | .d10 => 10

instance : LE Degree where
  le d1 d2 := d1.toNat ≤ d2.toNat

instance : LT Degree where
  lt d1 d2 := d1.toNat < d2.toNat

instance : DecidableRel (α := Degree) (· ≤ ·) :=
  fun d1 d2 => inferInstanceAs (Decidable (d1.toNat ≤ d2.toNat))

instance : DecidableRel (α := Degree) (· < ·) :=
  fun d1 d2 => inferInstanceAs (Decidable (d1.toNat < d2.toNat))

def allDegrees : List Degree := [.d0, .d1, .d2, .d3, .d4, .d5, .d6, .d7, .d8, .d9, .d10]

/-- d0 is the minimum degree -/
theorem d0_is_minimum : ∀ d : Degree, Degree.d0 ≤ d := by
  intro d; cases d <;> decide

-- ============================================================================
-- PART 2: Gradable Nouns as Measure Functions
-- ============================================================================

/-- A gradable noun maps individuals to degrees.
    ⟦idiot⟧ = λx.ιd[x is d-idiotic] -/
structure GradableNoun (Entity : Type) where
  name : String
  /-- The measure function: entity → degree -/
  measure : Entity → Degree
  /-- The contextual standard for this predicate -/
  standard : Degree

/-- Apply POS to a gradable noun: λx. standard(g) ≤ g(x) -/
def GradableNoun.pos {E : Type} (n : GradableNoun E) : E → Bool :=
  fun x => n.standard ≤ n.measure x

-- ============================================================================
-- PART 3: Size Adjectives
-- ============================================================================

/-- Size adjectives measure "size" of objects including degrees.
    They're characterized by their polarity (big vs small). -/
inductive SizePolarity where
  | big    -- measures bigness (positive)
  | small  -- measures smallness (negative/inverted)
  deriving Repr, DecidableEq, BEq

/-- Big: maps degrees to their "bigness" (same ordering as the degree scale) -/
def bigness (d : Degree) : Degree := d

/-- Small: maps degrees to their "smallness" (inverted ordering)
    d0 is maximally small, d10 is minimally small -/
def smallness (d : Degree) : Degree :=
  match d with
  | .d0 => .d10 | .d1 => .d9 | .d2 => .d8 | .d3 => .d7 | .d4 => .d6
  | .d5 => .d5 | .d6 => .d4 | .d7 => .d3 | .d8 => .d2 | .d9 => .d1 | .d10 => .d0

/-- Standard for "big" (contextual, but typically middling) -/
def bigStandard : Degree := .d5

/-- Standard for "small" (contextual) -/
def smallStandard : Degree := .d5

/-- POS applied to size adjective: λd. standard(size) ≤ size(d) -/
def posBig (d : Degree) : Bool := bigStandard ≤ bigness d
def posSmall (d : Degree) : Bool := smallStandard ≤ smallness d

-- ============================================================================
-- PART 4: The MEASN Morpheme
-- ============================================================================

/-!
## MEASN: The Key to Degree Readings

```
⟦MEASN⟧ = λg.λm.λx. [min{d : d ∈ scale(g) ∧ m(d)} ≤ g(x)] ∧ [standard(g) ≤ g(x)]
```

This requires:
1. x's degree on g's scale ≥ minimum degree satisfying the size predicate
2. x meets the standard for the gradable noun (you must BE an idiot)
-/

/-- Find minimum degree satisfying a predicate -/
def minDegree (p : Degree → Bool) : Option Degree :=
  allDegrees.find? p

/-- MEASN composition: combines size adjective with gradable noun -/
def measN {E : Type}
    (noun : GradableNoun E)
    (sizeAdj : Degree → Bool)  -- The [POS size-adj] predicate on degrees
    : E → Bool :=
  fun x =>
    match minDegree sizeAdj with
    | none => false  -- No degree satisfies the size adjective
    | some minD =>
        -- x's degree must be ≥ minimum satisfying size adj
        -- AND x must meet the noun's standard
        minD ≤ noun.measure x ∧ noun.standard ≤ noun.measure x

-- ============================================================================
-- PART 5: Computing "big idiot" and "small idiot"
-- ============================================================================

/-- Example: an "idiot" gradable noun with standard at d3 -/
def idiotNoun {E : Type} (measure : E → Degree) : GradableNoun E :=
  { name := "idiot"
  , measure := measure
  , standard := .d3  -- You need at least d3 idiocy to count as an idiot
  }

/-- "big idiot" = MEASN(idiot)(POS big) -/
def bigIdiot {E : Type} (noun : GradableNoun E) : E → Bool :=
  measN noun posBig

/-- "small idiot" = MEASN(idiot)(POS small) -/
def smallIdiot {E : Type} (noun : GradableNoun E) : E → Bool :=
  measN noun posSmall

-- ============================================================================
-- PART 6: The Bigness Generalization - Key Theorems
-- ============================================================================

/-- Minimum degree satisfying "big" is d5 (the bigness standard) -/
theorem min_big_is_d5 : minDegree posBig = some .d5 := by native_decide

/-- Minimum degree satisfying "small" is d0 (the scale minimum!) -/
theorem min_small_is_d0 : minDegree posSmall = some .d0 := by native_decide

/-- Key insight: d0 ALWAYS satisfies smallness because it's maximally small -/
theorem d0_satisfies_small : posSmall .d0 = true := by native_decide

/-- d0 is the unique minimum for smallness -/
theorem d0_is_min_for_small : ∀ d : Degree, posSmall d → .d0 ≤ d := by
  intro d _
  exact d0_is_minimum d

/-!
## Why "small idiot" fails (Bigness Generalization)

For "small idiot":
- min{d : posSmall(d)} = d0 (by `min_small_is_d0`)
- So the condition becomes: d0 ≤ idiot(x) ∧ standard(idiot) ≤ idiot(x)
- But d0 ≤ idiot(x) is ALWAYS true (d0 is minimum)
- So "small idiot" ≡ "idiot" — the size adjective is vacuous!

For "big idiot":
- min{d : posBig(d)} = d5
- So the condition becomes: d5 ≤ idiot(x) ∧ d3 ≤ idiot(x)
- This is substantive: requires HIGH idiocy (≥ d5)
-/

/-- "small idiot" is equivalent to just "idiot" (size adj is vacuous) -/
theorem small_idiot_vacuous {E : Type} (noun : GradableNoun E) (x : E) :
    smallIdiot noun x = noun.pos x := by
  simp only [smallIdiot, measN, min_small_is_d0]
  simp only [GradableNoun.pos]
  -- d0 ≤ noun.measure x is always true
  have h : Degree.d0 ≤ noun.measure x := d0_is_minimum _
  simp only [h, true_and]

/-- "big idiot" is MORE restrictive than just "idiot" -/
theorem big_idiot_restrictive {E : Type} (noun : GradableNoun E)
    (h : noun.standard < .d5) :
    ∀ x, bigIdiot noun x → noun.pos x := by
  intro x hbig
  simp only [bigIdiot, measN, min_big_is_d5, GradableNoun.pos] at *
  simp only [decide_eq_true_eq] at *
  exact hbig.2

-- ============================================================================
-- PART 7: Worked Example
-- ============================================================================

/-- A simple entity type for examples -/
inductive Person where
  | george | sarah | floyd
  deriving Repr, DecidableEq, BEq

/-- George is very idiotic (d8), Sarah is somewhat (d4), Floyd is not (d1) -/
def idiocyMeasure : Person → Degree
  | .george => .d8
  | .sarah => .d4
  | .floyd => .d1

def exampleIdiot : GradableNoun Person := idiotNoun idiocyMeasure

-- Test the predictions
#eval exampleIdiot.pos .george    -- true (d8 ≥ d3)
#eval exampleIdiot.pos .sarah     -- true (d4 ≥ d3)
#eval exampleIdiot.pos .floyd     -- false (d1 < d3)

#eval bigIdiot exampleIdiot .george   -- true (d8 ≥ d5 and d8 ≥ d3)
#eval bigIdiot exampleIdiot .sarah    -- false (d4 < d5)
#eval bigIdiot exampleIdiot .floyd    -- false

#eval smallIdiot exampleIdiot .george -- true (vacuous! same as "idiot")
#eval smallIdiot exampleIdiot .sarah  -- true (same as "idiot")
#eval smallIdiot exampleIdiot .floyd  -- false (not an idiot)

/-- George is an idiot -/
theorem george_is_idiot : exampleIdiot.pos .george = true := by native_decide

/-- George is a BIG idiot -/
theorem george_is_big_idiot : bigIdiot exampleIdiot .george = true := by native_decide

/-- Sarah is an idiot but NOT a big idiot -/
theorem sarah_is_idiot_not_big :
    exampleIdiot.pos .sarah = true ∧ bigIdiot exampleIdiot .sarah = false := by
  constructor <;> native_decide

/-- "Small idiot" gives same result as "idiot" (vacuous!) -/
theorem small_idiot_same_as_idiot :
    smallIdiot exampleIdiot .george = exampleIdiot.pos .george ∧
    smallIdiot exampleIdiot .sarah = exampleIdiot.pos .sarah ∧
    smallIdiot exampleIdiot .floyd = exampleIdiot.pos .floyd := by
  constructor
  · rw [small_idiot_vacuous]
  constructor
  · rw [small_idiot_vacuous]
  · rw [small_idiot_vacuous]

-- ============================================================================
-- PART 8: Connection to Threshold Semantics
-- ============================================================================

/-!
## Unified Threshold Pattern

| Domain | Scale | Threshold | Source |
|--------|-------|-----------|--------|
| Adjectives | height(x) | θ_tall (uncertain) | LassiterGoodman2017 |
| Generics | prevalence(F,K) | θ_gen (uncertain) | TesslerGoodman2019 |
| Gradable nouns | degree(N,x) | min{d : big(d)} | Morzycki2009 |

All three share:
1. **Measure function**: maps entities to degrees on a scale
2. **Threshold comparison**: predicate true iff degree ≥ threshold
3. **Scale structure effects**: polarity/direction matters

Key difference: RSA models make threshold uncertain and infer it pragmatically.
Morzycki's analysis has a deterministic threshold (the minimum satisfying bigness).
-/

/-- Abstract threshold predicate: the common pattern -/
structure ThresholdPredicate (Entity : Type) where
  /-- Name of the predicate -/
  name : String
  /-- Measure function: entity → degree -/
  measure : Entity → Degree
  /-- The threshold degree -/
  threshold : Degree

/-- Threshold predicate semantics: true iff measure(x) ≥ threshold -/
def ThresholdPredicate.apply {E : Type} (p : ThresholdPredicate E) (x : E) : Bool :=
  p.threshold ≤ p.measure x

/-- "big idiot" as a threshold predicate -/
def bigIdiotAsThreshold {E : Type} (measure : E → Degree) : ThresholdPredicate E :=
  { name := "big idiot"
  , measure := measure
  , threshold := .d5  -- min{d : posBig(d)}
  }

/-- Equivalence: bigIdiot = threshold predicate with θ = d5 (when standard ≤ d5)

When the noun's standard is at most d5, "big N" is equivalent to
checking if the degree exceeds d5 (the bigness threshold). -/
theorem bigIdiot_is_threshold_example :
    bigIdiot exampleIdiot .george = (bigIdiotAsThreshold idiocyMeasure).apply .george ∧
    bigIdiot exampleIdiot .sarah = (bigIdiotAsThreshold idiocyMeasure).apply .sarah ∧
    bigIdiot exampleIdiot .floyd = (bigIdiotAsThreshold idiocyMeasure).apply .floyd := by
  constructor <;> [native_decide; constructor <;> native_decide]

end Montague.Lexicon.GradableNouns
