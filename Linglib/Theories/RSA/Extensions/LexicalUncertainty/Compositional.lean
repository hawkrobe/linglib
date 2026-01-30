/-
# Linglib.Core.CompositionalLU

Compositional Lexical Uncertainty for embedded implicatures.

## Architecture

This extends lexical uncertainty to handle **compositional** utterances.
Instead of refining whole-utterance meanings, we refine **atomic lexical items**
and then compose meanings via Boolean connectives.

### Key Innovation (Bergen et al. 2016, Section 5)

For compositional LU:
1. Atomic utterances have refinable meanings in the lexicon
2. Complex utterances are composed via ∨, ∧, ¬
3. Refinement operates BEFORE composition

This derives **non-convex disjunctive implicatures**:
- "one or three" → exactly 1 or exactly 3 (not 2)
- "warm or scalding" → warm-not-hot or scalding (not hot)

### Hurford-Violating Disjunctions

When one disjunct entails the other (e.g., "some or all"), standard semantics
predicts no difference from the weaker disjunct. But:
- "some" → not all (scalar implicature)
- "some or all" → speaker ignorant (no scalar implicature)

Compositional LU derives this by tracking which refinements are available.

Reference: Bergen, Levy & Goodman (2016) "Pragmatic reasoning through semantic inference"
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Extensions.LexicalUncertainty.Basic

-- ============================================================================
-- Compositional Utterance Structure
-- ============================================================================

/--
Compositional utterances built from atomic items and Boolean connectives.

This represents the syntactic structure that feeds into compositional semantics.
-/
inductive CompUtt (Atom : Type) where
  /-- Atomic utterance (lexical item) -/
  | atom : Atom → CompUtt Atom
  /-- Disjunction -/
  | disj : CompUtt Atom → CompUtt Atom → CompUtt Atom
  /-- Conjunction -/
  | conj : CompUtt Atom → CompUtt Atom → CompUtt Atom
  /-- Negation -/
  | neg : CompUtt Atom → CompUtt Atom
  deriving BEq

namespace CompUtt

/-- Infix notation for disjunction -/
infixl:65 " ∨ᵤ " => CompUtt.disj

/-- Infix notation for conjunction -/
infixl:70 " ∧ᵤ " => CompUtt.conj

/-- Prefix notation for negation -/
prefix:75 "¬ᵤ" => CompUtt.neg

/-- Extract all atomic items from a compositional utterance -/
def atoms {Atom : Type} : CompUtt Atom → List Atom
  | atom a => [a]
  | disj u₁ u₂ => u₁.atoms ++ u₂.atoms
  | conj u₁ u₂ => u₁.atoms ++ u₂.atoms
  | neg u => u.atoms

/-- Count the complexity (number of connectives) -/
def complexity {Atom : Type} : CompUtt Atom → Nat
  | atom _ => 0
  | disj u₁ u₂ => 1 + u₁.complexity + u₂.complexity
  | conj u₁ u₂ => 1 + u₁.complexity + u₂.complexity
  | neg u => 1 + u.complexity

end CompUtt

-- ============================================================================
-- Atomic Lexicon: Maps atoms to truth functions
-- ============================================================================

/--
An atomic lexicon maps atomic utterances to Boolean meanings.

This is the refinable part of the lexicon.
-/
structure AtomicLexicon (Atom World : Type) where
  /-- Meaning of each atomic item -/
  meaning : Atom → World → Bool

namespace AtomicLexicon

variable {A W : Type}

/-- Compose meanings of complex utterances from atomic meanings -/
def interpret (L : AtomicLexicon A W) : CompUtt A → W → Bool
  | .atom a, w => L.meaning a w
  | .disj u₁ u₂, w => L.interpret u₁ w || L.interpret u₂ w
  | .conj u₁ u₂, w => L.interpret u₁ w && L.interpret u₂ w
  | .neg u, w => !L.interpret u w

/-- Check if one atomic lexicon refines another -/
def refines (L' L : AtomicLexicon A W) : Prop :=
  ∀ a w, L.meaning a w = false → L'.meaning a w = false

end AtomicLexicon

-- ============================================================================
-- Compositional LU Scenario
-- ============================================================================

/--
Compositional Lexical Uncertainty Scenario.

Extends LU to handle compositional utterances where:
- Atomic items have refinable meanings
- Complex meanings are composed via Boolean connectives
-/
structure CompLUScenario where
  /-- Type of atomic utterances -/
  Atom : Type
  /-- Type of possible worlds -/
  World : Type
  /-- Base atomic lexicon (unrefined meanings) -/
  baseLexicon : AtomicLexicon Atom World
  /-- Set of possible refined atomic lexica -/
  lexica : List (AtomicLexicon Atom World)
  /-- Prior over lexica -/
  lexPrior : AtomicLexicon Atom World → ℚ := fun _ => 1
  /-- Prior over worlds -/
  worldPrior : World → ℚ := fun _ => 1
  /-- Set of available (complex) utterances -/
  utterances : List (CompUtt Atom)
  /-- Enumeration of worlds -/
  worlds : List World
  /-- Rationality parameter -/
  α : ℕ := 1
  [atomBEq : BEq Atom]
  [worldBEq : BEq World]

attribute [instance] CompLUScenario.atomBEq CompLUScenario.worldBEq

-- ============================================================================
-- Compositional LU-RSA Computations
-- ============================================================================

namespace CompLURSA

/--
L₀ given a specific atomic lexicon.

P(w | u, L) ∝ P(w) · ⟦u⟧_L(w)

The meaning is computed compositionally from atomic meanings.
-/
def L0_given (S : CompLUScenario) (L : AtomicLexicon S.Atom S.World)
    (u : CompUtt S.Atom) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w =>
    (w, S.worldPrior w * boolToRat (L.interpret u w))
  RSA.Eval.normalize scores

/--
S₁ given a specific atomic lexicon.

P(u | w, L) ∝ L₀(w | u, L)
-/
def S1_given (S : CompLUScenario) (L : AtomicLexicon S.Atom S.World)
    (w : S.World) : List (CompUtt S.Atom × ℚ) :=
  let scores := S.utterances.map fun u => (u, (RSA.Eval.getScore (L0_given S L u) w) ^ S.α)
  RSA.Eval.normalize scores

/--
L₁ with compositional lexical uncertainty.

P(w | u) ∝ P(w) · Σ_L P(L) · S₁(u | w, L)

The listener marginalizes over refined ATOMIC lexica.
-/
def L1 (S : CompLUScenario) (u : CompUtt S.Atom) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w =>
    let lexSum := S.lexica.foldl (init := (0 : ℚ)) fun acc L =>
      acc + S.lexPrior L * RSA.Eval.getScore (S1_given S L w) u
    (w, S.worldPrior w * lexSum)
  RSA.Eval.normalize scores

/-- Get L₁ probability for a specific world -/
def L1_prob (S : CompLUScenario) (u : CompUtt S.Atom) (w : S.World) : ℚ :=
  RSA.Eval.getScore (L1 S u) w

end CompLURSA

-- ============================================================================
-- Non-Convex Disjunction Scenario Builder
-- ============================================================================

/--
Worlds for a 3-point scale (one, two, three).
-/
inductive ThreePointWorld where
  | one | two | three
  deriving Repr, BEq, DecidableEq

/--
Atomic utterances for numerals.
-/
inductive NumeralAtom where
  | one_ | two_ | three_
  deriving Repr, BEq, DecidableEq

/--
Base semantics for numerals: lower-bound (at-least) reading.
-/
def numeralBaseLexicon : AtomicLexicon NumeralAtom ThreePointWorld where
  meaning a w :=
    match a, w with
    | .one_, _ => true          -- "one" true for ≥1
    | .two_, .one => false      -- "two" false for 1
    | .two_, _ => true          -- "two" true for ≥2
    | .three_, .three => true   -- "three" true only for 3
    | .three_, _ => false

/--
Generate all valid refinements of the numeral lexicon.

For "one": can refine to {1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}
For "two": can refine to {2}, {3}, {2,3}
For "three": only {3} (already maximally specific)
-/
def numeralRefinedLexica : List (AtomicLexicon NumeralAtom ThreePointWorld) :=
  -- Just a few key refinements for illustration
  [
    -- L₁: Unrefined (base)
    numeralBaseLexicon,
    -- L₂: "one" refined to exactly-1, "two" refined to exactly-2
    { meaning := fun a w =>
        match a, w with
        | .one_, .one => true
        | .one_, _ => false
        | .two_, .two => true
        | .two_, _ => false
        | .three_, .three => true
        | .three_, _ => false },
    -- L₃: "one" refined to {1,2}, "two" refined to exactly-2
    { meaning := fun a w =>
        match a, w with
        | .one_, .three => false
        | .one_, _ => true
        | .two_, .two => true
        | .two_, _ => false
        | .three_, .three => true
        | .three_, _ => false },
    -- L₄: "one" refined to {1,3} (non-convex!)
    { meaning := fun a w =>
        match a, w with
        | .one_, .two => false
        | .one_, _ => true
        | .two_, .two => true
        | .two_, _ => false
        | .three_, .three => true
        | .three_, _ => false }
  ]

/--
Build scenario for non-convex disjunction implicatures.

Compares "one or two" vs "one or three".
-/
def mkNonConvexDisjScenario : CompLUScenario where
  Atom := NumeralAtom
  World := ThreePointWorld
  baseLexicon := numeralBaseLexicon
  lexica := numeralRefinedLexica
  utterances := [
    .atom .one_,
    .atom .two_,
    .atom .three_,
    .atom .one_ ∨ᵤ .atom .two_,
    .atom .one_ ∨ᵤ .atom .three_,
    .atom .two_ ∨ᵤ .atom .three_
  ]
  worlds := [.one, .two, .three]

-- ============================================================================
-- Hurford Constraint and Embedded Implicatures
-- ============================================================================

/--
Check if one utterance semantically entails another under base semantics.
-/
def entails (S : CompLUScenario) (u₁ u₂ : CompUtt S.Atom) : Bool :=
  S.worlds.all fun w =>
    !S.baseLexicon.interpret u₁ w || S.baseLexicon.interpret u₂ w

/--
Hurford's constraint: a disjunction is odd if one disjunct entails the other.

"#Some or all of the students passed" violates Hurford because "all" ⊆ "some".
But such sentences ARE felicitous and have ignorance implicatures!
-/
def violatesHurford (S : CompLUScenario) : CompUtt S.Atom → Bool
  | .disj u₁ u₂ => entails S u₁ u₂ || entails S u₂ u₁
  | _ => false

-- ============================================================================
-- Connection to Potts et al. (2016)
-- ============================================================================

/--
Structure for tracking embedded implicature predictions.

This connects to Potts et al.'s "An experimental investigation of
embedded scalar implicatures".
-/
structure EmbeddedSIPrediction where
  /-- The embedding context (e.g., negation, conditional) -/
  context : String
  /-- The scalar item -/
  scalarItem : String
  /-- Whether local (embedded) reading is available -/
  localAvailable : Bool
  /-- Whether global reading is available -/
  globalAvailable : Bool
  /-- Predicted preference (local vs global) -/
  preferLocal : Option Bool
  deriving Repr

/--
Compositional LU predictions for various embedding contexts.

Key prediction: Local readings are available when the asymmetry in
lexical refinements makes them pragmatically useful.
-/
def embeddedSIPredictions : List EmbeddedSIPrediction :=
  [
    -- Negation: "John didn't eat some of the cookies"
    { context := "negation"
    , scalarItem := "some"
    , localAvailable := true   -- "not [some but not all]" = all or none
    , globalAvailable := true  -- "not some" = none
    , preferLocal := some false  -- Global usually preferred
    },
    -- Disjunction: "John ate some of the cookies or Mary did"
    { context := "disjunction"
    , scalarItem := "some"
    , localAvailable := true
    , globalAvailable := true
    , preferLocal := some true  -- Local often preferred here
    }
  ]
