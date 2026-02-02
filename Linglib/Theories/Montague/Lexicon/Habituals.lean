/-
# HAB: The Covert Habitual Operator

Traditional semantic treatments of habitual aspect.

## The Traditional Account

Habituals like "John smokes" are analyzed with a covert HAB operator:
- HAB quantifies over "characteristic" times/situations
- Similar structure to GEN, but for VP-level aspect

Structure: John HAB[smoke]
→ "In characteristic/typical situations, John smokes"

## The Problem with HAB

Like GEN, HAB faces the circularity problem:
1. What counts as "characteristic"? - Not independently defined
2. How often is "habitual"? - Varies by predicate
3. Exception tolerance? - "John smokes" true despite not always smoking

## Comparison with Threshold Semantics

Tessler & Goodman (2019) style threshold semantics applies:
- ⟦hab⟧(frequency f, threshold θ) = 1 iff f > θ
- Threshold θ inferred pragmatically via RSA
- Frequency priors vary by activity type

This eliminates HAB as a covert operator in favor of:
- Observable frequency
- Pragmatically inferred threshold
- Activity-specific priors

## References

- Carlson, G.N. (1977). Reference to Kinds in English.
- Krifka, M. et al. (1995). Genericity: An Introduction.
- Bhatt, R. (1999). Covert Modality in Non-finite Contexts.
- Ferreira, M. (2005). Event Quantification and Plurality.
-/

import Mathlib.Data.Rat.Defs

namespace Montague.Lexicon.Habituals

-- ============================================================================
-- Core Types
-- ============================================================================

/-- A time interval or occasion for habitual quantification -/
structure Occasion where
  id : Nat
  deriving DecidableEq, Repr

instance : Inhabited Occasion := ⟨{ id := 0 }⟩

/-- An activity predicate (what John does at an occasion) -/
abbrev Activity := Occasion → Bool

/-- A characteristicness predicate (which occasions are "typical") -/
abbrev Characteristic := Occasion → Bool

-- ============================================================================
-- Traditional HAB Operator
-- ============================================================================

/--
Traditional HAB as a quantifier over occasions.

  HAB[activity] is true for an individual iff
  in all CHARACTERISTIC occasions, the individual does the activity.

Parallel to GEN:
  HAB[smoke](john) ≈ GEN_t [characteristic(t)] [smoke(john, t)]

The `characteristic` parameter is the hidden component doing all the work.
-/
def traditionalHAB
    (occasions : List Occasion)
    (characteristic : Characteristic)  -- THE HIDDEN PARAMETER
    (activity : Activity)
    : Bool :=
  occasions.all fun t =>
    !characteristic t || activity t

/-- Alternative: existential characterization of non-habitual -/
def traditionalHAB_existential
    (occasions : List Occasion)
    (characteristic : Characteristic)
    (activity : Activity)
    : Bool :=
  !occasions.any fun t => characteristic t && !activity t

/-- The two formulations are equivalent -/
theorem hab_formulations_equiv
    (occasions : List Occasion)
    (characteristic : Characteristic)
    (activity : Activity)
    : traditionalHAB occasions characteristic activity =
      traditionalHAB_existential occasions characteristic activity := by
  simp only [traditionalHAB, traditionalHAB_existential, List.all_eq_not_any_not]
  congr 1
  induction occasions with
  | nil => rfl
  | cons o os ih =>
    simp only [List.any_cons]
    rw [ih]
    cases characteristic o <;> cases activity o <;> rfl

-- ============================================================================
-- Frequency-Based Semantics (T&G Style)
-- ============================================================================

/--
Frequency of an activity across occasions.
This is the proportion of occasions where the activity occurs.
-/
def frequency
    (occasions : List Occasion)
    (activity : Activity)
    : ℚ :=
  let active := occasions.filter activity
  if occasions.length = 0 then 0
  else (active.length : ℚ) / (occasions.length : ℚ)

/--
Threshold-based habitual (parallel to T&G for generics).

The habitual is true iff frequency exceeds threshold.
-/
def thresholdHabitual
    (occasions : List Occasion)
    (activity : Activity)
    (threshold : ℚ)
    : Bool :=
  frequency occasions activity > threshold

/--
HAB reduces to threshold: for any HAB configuration, there exists a
matching threshold that gives the same truth value.
-/
theorem hab_reduces_to_threshold
    (occasions : List Occasion)
    (characteristic : Characteristic)
    (activity : Activity)
    (_hNonEmpty : occasions.length > 0)
    : ∃ θ : ℚ, traditionalHAB occasions characteristic activity =
               thresholdHabitual occasions activity θ := by
  sorry  -- Proof parallels gen_reduces_to_threshold

-- ============================================================================
-- Activity-Specific Priors
-- ============================================================================

/-!
## Why Threshold Varies by Activity

"John smokes" requires regular frequency (daily, weekly)
"John murders people" can be true with very low frequency (once ever)

This mirrors the property-specific priors in generics:
- Neutral activities: high threshold needed
- Striking/dangerous activities: lower threshold

The prior P(frequency | activity_type) captures this.
-/

/-- Activity types with different frequency expectations -/
inductive ActivityType where
  | neutral      -- Eating, sleeping, walking (high frequency expected)
  | occupation   -- Doctor, teacher, smoker (regular but not constant)
  | striking     -- Murder, crime (very low frequency sufficient)
  | achievement  -- Win championship, graduate (once is enough)
  deriving DecidableEq, Repr

/-- Expected frequency threshold by activity type -/
def expectedThreshold : ActivityType → ℚ
  | .neutral => 8/10      -- Most occasions
  | .occupation => 5/10   -- Regular occasions
  | .striking => 1/100    -- Rare is enough
  | .achievement => 0     -- Once suffices

-- ============================================================================
-- Examples
-- ============================================================================

def occasions : List Occasion := [
  { id := 0 }, { id := 1 }, { id := 2 }, { id := 3 }, { id := 4 },
  { id := 5 }, { id := 6 }, { id := 7 }, { id := 8 }, { id := 9 }
]

-- "John smokes" - true if he smokes regularly (say, 6/10 days)
def johnSmokesActivity : Activity := fun t =>
  t.id ∈ [0, 1, 2, 4, 5, 8]  -- 6 out of 10 occasions

-- "Normal" occasions for smoking (not when sick, traveling, etc.)
def normalOccasions : Characteristic := fun t =>
  t.id ∈ [0, 1, 2, 3, 4, 5, 6, 7]  -- 8 out of 10 are "normal"

-- Traditional HAB: John smokes in all normal occasions?
-- Occasions 3, 6, 7 are normal but John doesn't smoke there
-- So traditionalHAB with strict normalcy would be FALSE
-- But we know "John smokes" is TRUE with 6/10 frequency

-- This shows the problem: HAB needs carefully stipulated "characteristic"
-- to match intuitive judgments

-- Frequency-based approach: 6/10 = 0.6
#eval frequency occasions johnSmokesActivity  -- 3/5

-- Threshold approach: with θ = 0.5, "John smokes" is TRUE
#eval thresholdHabitual occasions johnSmokesActivity (1/2)  -- true

-- ============================================================================
-- HAB vs GEN: The Parallel
-- ============================================================================

/-!
## HAB and GEN: Same Structure, Different Domains

| Operator | Quantifies Over | Hidden Parameter | Threshold Version |
|----------|-----------------|------------------|-------------------|
| GEN      | Situations/cases | "normal" situations | prevalence > θ |
| HAB      | Occasions/times | "characteristic" times | frequency > θ |

Both face the same circularity:
- What's "normal"/"characteristic"? → Defined to give right judgments
- How handle exceptions? → Stipulate they're "not normal/characteristic"

Both are eliminated by threshold semantics:
- Replace hidden normalcy with observable measure (prevalence/frequency)
- Replace covert quantifier with threshold comparison
- Use RSA to infer threshold pragmatically
-/

/-- Unified structure for GEN/HAB elimination -/
structure ThresholdQuantifier where
  name : String
  /-- What we measure (prevalence for GEN, frequency for HAB) -/
  measureName : String
  /-- The threshold (inferred pragmatically) -/
  threshold : ℚ

def genAsThreshold : ThresholdQuantifier :=
  { name := "GEN"
  , measureName := "prevalence"
  , threshold := 0  -- Pragmatically inferred
  }

def habAsThreshold : ThresholdQuantifier :=
  { name := "HAB"
  , measureName := "frequency"
  , threshold := 0  -- Pragmatically inferred
  }

-- ============================================================================
-- Connection to Aspect
-- ============================================================================

/-!
## HAB and Aspectual Class

HAB interacts with aspectual class:

1. **States**: Already "timeless" - HAB vacuous
   - "John knows French" (no HAB needed, state persists)

2. **Activities**: HAB quantifies over instances
   - "John runs" = HAB[John runs] = frequent running events

3. **Achievements**: HAB requires iteration
   - "John wins races" = HAB[John wins a race]

4. **Accomplishments**: HAB over completed events
   - "John builds houses" = HAB[John builds a house]

The frequency threshold varies by aspectual class:
- Activities: lower threshold (running once a week is "running")
- Accomplishments: higher threshold (building one house isn't "builds houses")
-/

end Montague.Lexicon.Habituals
