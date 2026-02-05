/-
# Numeral Theory Infrastructure

This module defines the `NumeralTheory` structure for organizing competing
semantic analyses of number words.

## Competing Analyses

Number words like "two" have (at least) two semantic analyses:

1. **Lower-bound** (Horn 1972): "two" means ≥2
   - Exact interpretation arises via scalar implicature
   - Implicature can be canceled (e.g., with partial speaker knowledge)

2. **Exact** (some formal semanticists): "two" means exactly 2
   - No implicature needed for exact interpretation
   - But cannot explain knowledge-state variation (G&S 2013)

## Architecture

Each analysis is a `NumeralTheory` instance containing:
- Core meaning function
- Derived RSA scenario (for pragmatic reasoning)
- Derived strength ordering (which numeral entails which)

The RSA machinery is agnostic to which theory is used — it just
needs an `RSAScenario`. Comparison theorems live in `Compare.lean`.

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Goodman, N. & Stuhlmüller, A. (2013). Knowledge and Implicature.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval

namespace TruthConditional.Determiner.Numeral

-- Core Types

/-- Number word utterances -/
inductive NumWord where
  | one | two | three | four | five
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert NumWord to its numeric value -/
def NumWord.toNat : NumWord → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .five => 5

instance : ToString NumWord where
  toString
    | .one => "one" | .two => "two" | .three => "three"
    | .four => "four" | .five => "five"

/-- Standard list of numeral utterances for RSA scenarios -/
def standardNumWords : List NumWord := [.one, .two, .three]

/-- Standard list of world states (cardinalities 0-3) -/
def standardWorlds : List Nat := [0, 1, 2, 3]

-- NumeralTheory Structure

/--
A semantic theory for number words.

Each theory specifies:
- `meaning`: The core semantic content — when is "n" true of cardinality k?
- Derived: RSA scenario, strength ordering

## Design Note

We use a structure (not a typeclass) following mathlib conventions:
theories are passed explicitly, not resolved by instance search.
This makes theory comparisons explicit and avoids ambiguity.
-/
structure NumeralTheory where
  /-- Name of the theory -/
  name : String
  /-- Academic citation -/
  citation : String
  /-- Core meaning function: is numeral `w` true when cardinality is `n`? -/
  meaning : NumWord → Nat → Bool
  /-- Utterances to consider (default: one, two, three) -/
  utterances : List NumWord := standardNumWords
  /-- World states to consider (default: 0, 1, 2, 3) -/
  worlds : List Nat := standardWorlds

-- Derived Notions

/--
Run L1 for a numeral theory using RSA.Eval (for #eval demonstrations).

This is the key connection: any numeral theory can be used with RSA.
-/
def NumeralTheory.runL1 (T : NumeralTheory) (w : NumWord) : List (Nat × ℚ) :=
  RSA.Eval.basicL1 T.utterances T.worlds
    (λ u n => boolToRat (T.meaning u n)) (λ _ => 1) 1 (λ _ => 0) w

/--
Strength ordering: `w₁` is stronger than `w₂` if `w₁` entails `w₂`.

In lower-bound semantics: "three" is stronger than "two" (3≥n → 2≥n).
In exact semantics: no numeral is stronger than another (disjoint).
-/
def NumeralTheory.strongerThan (T : NumeralTheory) (w₁ w₂ : NumWord) : Prop :=
  ∀ n, T.meaning w₁ n → T.meaning w₂ n

/--
Decidable strength comparison for computation.
-/
def NumeralTheory.isStrongerThan (T : NumeralTheory) (w₁ w₂ : NumWord) : Bool :=
  T.worlds.all λ n => !T.meaning w₁ n || T.meaning w₂ n

/--
Count worlds compatible with an utterance.

Key diagnostic: >1 means ambiguity exists (implicature possible).
-/
def NumeralTheory.compatibleCount (T : NumeralTheory) (w : NumWord) : Nat :=
  (T.worlds.filter (T.meaning w)).length

/--
List of worlds compatible with an utterance.
-/
def NumeralTheory.compatibleWorlds (T : NumeralTheory) (w : NumWord) : List Nat :=
  T.worlds.filter (T.meaning w)

/--
Is there semantic ambiguity for this utterance?

Ambiguity = more than one world compatible with the literal meaning.
This is necessary for implicature to arise.
-/
def NumeralTheory.hasAmbiguity (T : NumeralTheory) (w : NumWord) : Bool :=
  T.compatibleCount w > 1

-- Properties

/--
A theory has monotonic numerals if larger numerals are stronger.

Lower-bound semantics is monotonic: "three" entails "two" entails "one".
Exact semantics is NOT monotonic: numerals have disjoint denotations.
-/
def NumeralTheory.isMonotonic (T : NumeralTheory) : Prop :=
  T.strongerThan .three .two ∧ T.strongerThan .two .one

/--
Decidable monotonicity check.
-/
def NumeralTheory.checkMonotonic (T : NumeralTheory) : Bool :=
  T.isStrongerThan .three .two && T.isStrongerThan .two .one

/--
A theory is scalar if numerals form a Horn scale (each stronger than previous).
-/
def NumeralTheory.isScalar (T : NumeralTheory) : Prop :=
  T.isMonotonic ∧
  ∀ w₁ w₂ : NumWord, T.strongerThan w₁ w₂ → T.strongerThan w₂ w₁ → w₁ = w₂

end TruthConditional.Determiner.Numeral
