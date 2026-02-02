/-
# Traditional Generic Semantics (GEN Operator)

This module formalizes the traditional covert GEN operator posited for
generic sentences like "Dogs bark", "Birds fly", etc.

## The Traditional Account

In the standard analysis (Krifka et al. 1995, Carlson 1977), generics involve:
1. A covert quantifier **GEN** over situations/cases
2. A **restrictor** (the kind)
3. A **nuclear scope** (the property)
4. A hidden **normalcy** parameter

Structure: GEN_s [Restrictor(s)] [NuclearScope(s)]

Example: "Dogs bark"
  → GEN_s [dog(x,s)] [bark(x,s)]
  → "In normal situations s where there's a dog x, x barks in s"

## The Problem with GEN

The `normal` parameter is doing all the work, but it's:
1. **Not observable** (covert)
2. **Context-dependent** (varies by property)
3. **Essentially circular** — "normal dog situations" are stipulated to be
   situations where dogs do the characteristic thing

## Comparison with RSA Treatment

Tessler & Goodman (2019) eliminate GEN via threshold semantics:
- Generic is true iff prevalence exceeds threshold
- Threshold is uncertain, inferred pragmatically
- Prior over prevalence varies by property

See `Theories/RSA/Implementations/TesslerGoodman2019.lean` for the RSA account
and `Theories/Comparisons/GenericSemantics.lean` for the formal comparison.

## References

- Carlson, G. (1977). Reference to Kinds in English.
- Krifka, M. et al. (1995). Genericity: An Introduction.
- Chierchia, G. (1995). Individual-Level Predicates as Inherent Generics.
- Tessler & Goodman (2019). The Language of Generalization.
-/

import Mathlib.Data.Rat.Defs

namespace Montague.Noun.Kind.Generics

-- ============================================================================
-- Core Types
-- ============================================================================

/-- A situation/case — the entities GEN quantifies over.

    In situation semantics, situations are parts of worlds that can be
    evaluated for truth of basic propositions. For generics, situations
    represent "cases" or "occasions" where the kind appears.

    For "Dogs bark", each situation s is a case where there is a dog
    that either barks or doesn't bark.
-/
structure Situation where
  /-- Identifier for the situation -/
  id : Nat
  deriving DecidableEq, Repr

instance : Inhabited Situation := ⟨{ id := 0 }⟩

/-- A restrictor is a property of situations (e.g., "there is a dog in s") -/
abbrev Restrictor := Situation → Bool

/-- A scope is a property of situations (e.g., "the dog barks in s") -/
abbrev Scope := Situation → Bool

/-- A normalcy predicate picks out "normal" or "characteristic" situations -/
abbrev NormalcyPredicate := Situation → Bool

-- ============================================================================
-- The Traditional GEN Operator
-- ============================================================================

/--
Traditional GEN as a quantifier over situations.

    GEN[restrictor][scope] is true iff
    in all NORMAL situations where restrictor holds, scope holds.

    This is essentially a restricted universal quantifier:
      ∀s. (normal(s) ∧ restrictor(s)) → scope(s)

    The key parameters:
    - `situations`: the domain of quantification (possible cases)
    - `normal`: which situations count as "normal" (the hidden parameter!)
    - `restrictor`: the kind property (e.g., "is a dog in s")
    - `scope`: the predicated property (e.g., "barks in s")

    **Critical observation**: The `normal` parameter is where all the
    context-sensitivity and exception-tolerance is hidden.
-/
def traditionalGEN
    (situations : List Situation)
    (normal : NormalcyPredicate)      -- THE HIDDEN PARAMETER
    (restrictor : Restrictor)
    (scope : Scope)
    : Bool :=
  situations.all fun s =>
    -- For all normal situations where restrictor holds, scope holds
    !(normal s && restrictor s) || scope s

/--
Alternative formulation: existential test for counterexamples.

GEN is true iff there's no normal restrictor-situation that fails the scope.
-/
def traditionalGEN_existential
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : Bool :=
  !situations.any fun s => normal s && restrictor s && !scope s

/-- The two formulations are equivalent -/
theorem gen_formulations_equiv
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : traditionalGEN situations normal restrictor scope =
      traditionalGEN_existential situations normal restrictor scope := by
  -- Both express: "no normal restrictor-situation fails the scope"
  -- One as ∀s. (normal ∧ restrictor → scope)
  -- Other as ¬∃s. (normal ∧ restrictor ∧ ¬scope)
  -- These are logically equivalent by De Morgan
  simp only [traditionalGEN, traditionalGEN_existential, List.all_eq_not_any_not]
  -- Need: !any(¬(¬(n∧r)∨s)) = !any(n∧r∧¬s)
  congr 1
  induction situations with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.any_cons]
    rw [ih]
    -- Show: ¬(¬(n∧r)∨s) = n∧r∧¬s for head element
    cases normal s <;> cases restrictor s <;> cases scope s <;> rfl

-- ============================================================================
-- The GenericTheory Structure (parallel to ModalTheory)
-- ============================================================================

/--
A semantic theory for generics.

Different theories of generics differ primarily in how they characterize
the "normal" situations. This structure captures what any GEN-based theory
must provide.

**Comparison with ModalTheory**:
| Aspect    | ModalTheory                  | GenericTheory                |
|-----------|------------------------------|------------------------------|
| Quantifier| Over accessible worlds       | Over normal situations       |
| Parameter | Accessibility R(w,w')        | Normalcy predicate normal(s) |
| Hidden?   | Often explicit               | Usually covert               |
-/
structure GenericTheory where
  /-- Name of the theory -/
  name : String
  /-- Academic citation -/
  citation : String
  /-- How to determine "normal" situations given context -/
  normalcyFunction : List Situation → NormalcyPredicate
  /-- Whether this theory allows exceptions (quasi-universal vs strict) -/
  allowsExceptions : Bool := true

/-- Evaluate a generic under a theory -/
def GenericTheory.eval
    (T : GenericTheory)
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : Bool :=
  traditionalGEN situations (T.normalcyFunction situations) restrictor scope

-- ============================================================================
-- Standard Theories
-- ============================================================================

/-- Strict universal GEN: all situations are "normal" -/
def strictUniversal : GenericTheory :=
  { name := "Strict Universal"
  , citation := "Naive universal quantification"
  , normalcyFunction := fun _ => fun _ => true
  , allowsExceptions := false }

/-- Majority-based GEN: "normal" = occurring more than half the time -/
def majorityBased (restrictor : Restrictor) : GenericTheory :=
  { name := "Majority-Based"
  , citation := "Simple prevalence threshold"
  , normalcyFunction := fun situations =>
      let restrictorSits := situations.filter restrictor
      let count := restrictorSits.length
      fun s => restrictor s && count > 0
  , allowsExceptions := true }

-- ============================================================================
-- The Circularity Problem
-- ============================================================================

/--
**The Problem with Traditional GEN**:

The `normal` parameter does all the explanatory work but is:

1. **Not observable** — it's covert, posited to explain judgments
2. **Context-dependent** — varies with the property being predicated
3. **Essentially circular** — defined to give the right results

Example: Why is "Dogs bark" true despite some dogs not barking?
- Traditional answer: Those dogs aren't in "normal" dog situations
- But what makes a situation normal? Being one where dogs bark.
- This is **not explanatory**.

Example: "Mosquitoes carry malaria" is true with ~1% prevalence
- Traditional answer: The "normal" mosquito situations are disease-carrying ones
- But what determines this? The prior expectation for disease properties.
- The "normalcy" is stipulated based on what we're trying to explain.

The RSA/Tessler-Goodman approach replaces "normalcy" with:
- Prevalence (observable, measurable)
- Threshold (uncertain, inferred pragmatically)
- Property-specific priors (explains why 1% can count as "normal" for rare properties)
-/
structure CircularityProblem where
  /-- The normalcy predicate is context-dependent -/
  normalcyVaries : GenericTheory → GenericTheory → Prop :=
    fun T1 T2 => T1.normalcyFunction ≠ T2.normalcyFunction
  /-- The normalcy is chosen to fit judgments, not independently motivated -/
  normalcyNotIndependent : Prop := True

-- ============================================================================
-- Prevalence-Based Alternative (interface to T&G)
-- ============================================================================

/--
Prevalence of a property within restrictor situations.

This is the proportion of restrictor-situations where the scope holds.
-/
def prevalence
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : ℚ :=
  let restrictorSits := situations.filter restrictor
  let scopeSits := restrictorSits.filter scope
  if restrictorSits.length = 0 then 0
  else (scopeSits.length : ℚ) / (restrictorSits.length : ℚ)

/--
Threshold-based generic (a la Tessler & Goodman).

The generic is true iff prevalence exceeds threshold.
This replaces the hidden "normalcy" with observable prevalence.
-/
def thresholdGeneric
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    (threshold : ℚ)
    : Bool :=
  prevalence situations restrictor scope > threshold

/-!
**Key Result**: GEN is eliminable via threshold semantics.

The theorem `gen_eliminable` proving this is in `Theories/Comparisons/GenericSemantics.lean`,
which connects traditional GEN to Tessler & Goodman's (2019) RSA approach.
-/

-- ============================================================================
-- Example: Dogs Bark
-- ============================================================================

/-- Example situations for "Dogs bark" -/
def dogSituations : List Situation := [
  { id := 0 },  -- Fido barking
  { id := 1 },  -- Fido barking
  { id := 2 },  -- Rex not barking (sleeping)
  { id := 3 },  -- Spot barking
  { id := 4 },  -- Max barking
]

/-- All situations involve dogs (restrictor = true) -/
def isDogSituation : Restrictor := fun _ => true

/-- Most dogs bark in these situations -/
def dogBarks : Scope := fun s =>
  match s.id with
  | 2 => false  -- Rex is sleeping
  | _ => true

/-- "Normal" = typical/expected situations (NOT sleeping) -/
def normalDogSituation : NormalcyPredicate := fun s =>
  s.id != 2  -- Sleeping is not "normal" for purposes of barking

-- "Dogs bark" is true under traditional GEN with appropriate normalcy
#eval traditionalGEN dogSituations normalDogSituation isDogSituation dogBarks
-- true

-- Prevalence is 4/5 = 0.8
#eval prevalence dogSituations isDogSituation dogBarks
-- 4/5

-- Threshold generic with θ = 0.5 also gives true
#eval thresholdGeneric dogSituations isDogSituation dogBarks (1/2)
-- true

/-!
## Related Theory

- `Theories/Montague/Lexicon/Kinds.lean` - Kind reference, bare plurals, DKP
- `Theories/RSA/Implementations/TesslerGoodman2019.lean` - RSA treatment of generics

## Empirical Data

- `Phenomena/Generics/Data.lean` - prevalence asymmetries, rare property generics
- `Phenomena/KindReference/Data.lean` - kind-level predicates, cross-linguistic patterns
-/

end Montague.Noun.Kind.Generics
