/-
# Linglib.Core.LexicalUncertainty

Lexical Uncertainty extension to RSA.

## Architecture

Lexical uncertainty posits that speakers and listeners have uncertainty about
the semantic content of utterances. Rather than a fixed lexicon, there is a
set of possible lexica Λ, and pragmatic inference involves reasoning about
which lexicon is in use.

### Key Innovation (Bergen, Levy & Goodman 2016)

The marginalization over lexica happens at L₁, not L₀:
- L₀ is still parameterized by a specific lexicon L
- S₁ believes L₀ uses lexicon L (and is certain about it)
- L₁ is uncertain which lexicon S₁/L₀ are using, and marginalizes

### What This Derives

1. **M-implicatures**: Complex expressions → marked (low-probability) interpretations
2. **Ignorance implicatures**: "some or all" → speaker doesn't know which
3. **Non-convex disjunctive implicatures**: "one or three" ≠ "one or two"

Reference: Bergen, Levy & Goodman (2016) "Pragmatic reasoning through semantic inference"
-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.RSA
import Linglib.Core.Distribution

-- ============================================================================
-- Lexicon: A mapping from utterances to truth functions
-- ============================================================================

/--
A lexicon maps each utterance to a truth function over worlds.

In Bergen et al. (2016) notation:
  L(u, w) = 1 if w ∈ ⟦u⟧_L, else 0

For graded semantics, we allow values in [0,1].
-/
structure Lexicon (Utterance World : Type) where
  /-- The meaning function for this lexicon -/
  meaning : Utterance → World → ℚ

namespace Lexicon

variable {U W : Type}

/-- Create a lexicon from a Boolean satisfaction relation -/
def ofBool (satisfies : U → W → Bool) : Lexicon U W where
  meaning u w := boolToRat (satisfies u w)

/-- Create a lexicon from an RSAScenario's meaning function -/
def ofScenario {U W : Type} (utts : List U) (worlds : List W) (φ : U → W → ℚ) : Lexicon U W where
  meaning := φ

/-- Two lexica are equivalent if they assign the same meanings -/
def equiv (L₁ L₂ : Lexicon U W) : Prop :=
  ∀ u w, L₁.meaning u w = L₂.meaning u w

/-- Check if a lexicon is a refinement of another (logically implies) -/
def refines (L_refined L_base : Lexicon U W) : Prop :=
  ∀ u w, L_base.meaning u w = 0 → L_refined.meaning u w = 0

/-- Notation: L' ≤ₗ L means L' refines (is more specific than) L -/
notation:50 L' " ≤ₗ " L => refines L' L

end Lexicon

-- ============================================================================
-- LexicalUncertaintyScenario: RSA with multiple possible lexica
-- ============================================================================

/--
Lexical Uncertainty RSA Scenario.

Extends the basic RSA setup with:
- A set of possible lexica Λ
- A prior distribution over lexica

The semantic content of utterances is not fixed; rather, pragmatic inference
jointly determines both the interpretation AND the lexicon.
-/
structure LUScenario where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of possible worlds -/
  World : Type
  /-- Base semantic lexicon (unrefined meanings) -/
  baseLexicon : Lexicon Utterance World
  /-- Set of possible refined lexica -/
  lexica : List (Lexicon Utterance World)
  /-- Prior over lexica (default: uniform) -/
  lexPrior : Lexicon Utterance World → ℚ := fun _ => 1
  /-- Prior over worlds -/
  worldPrior : World → ℚ := fun _ => 1
  /-- Enumeration of utterances -/
  utterances : List Utterance
  /-- Enumeration of worlds -/
  worlds : List World
  /-- Rationality parameter. Higher values = more informative speaker. -/
  α : ℕ := 1
  /-- Null utterance cost (high, to discourage) -/
  nullCost : ℚ := 10
  [uttBEq : BEq Utterance]
  [worldBEq : BEq World]

attribute [instance] LUScenario.uttBEq LUScenario.worldBEq

-- ============================================================================
-- Lexical Refinement: Generating Λ from base semantics
-- ============================================================================

namespace LexicalRefinement

/--
A refinement of a truth function: a subset of worlds where it's true.

Given base meaning M : W → Bool, a valid refinement M' satisfies:
  ∀ w, M(w) = false → M'(w) = false

That is, M' can only narrow down the set of true worlds, not expand it.
-/
structure Refinement (W : Type) where
  /-- The refined meaning as a subset indicator -/
  meaning : W → Bool

/--
Check if one meaning refines another (is more specific).

M' refines M iff M' ⊆ M (as sets of worlds).
-/
def Refinement.isValidFor {W : Type} (r : Refinement W) (base : W → Bool) : Prop :=
  ∀ w, base w = false → r.meaning w = false

/--
Generate all valid refinements of a Boolean meaning over finite worlds.

For a base meaning true at n worlds, there are 2ⁿ - 1 valid non-trivial refinements
(excluding the empty refinement which would be contradictory).
-/
def allRefinements {W : Type} [DecidableEq W] (worlds : List W) (base : W → Bool)
    : List (Refinement W) :=
  -- Get worlds where base is true
  let trueWorlds := worlds.filter base
  -- Generate all non-empty subsets
  let subsets := trueWorlds.sublists.filter (·.length > 0)
  -- Convert each subset to a refinement
  subsets.map fun subset =>
    { meaning := fun w => subset.contains w }

/--
Generate all lexica from refinements of each utterance meaning.

This implements the "enrichment" procedure from Bergen et al. (2016) Section 4.3:
Λ consists of all lexica where each utterance meaning is a valid refinement.
-/
def generateLexica {U W : Type} [DecidableEq W] [DecidableEq U]
    (utterances : List U) (worlds : List W) (base : Lexicon U W)
    : List (Lexicon U W) :=
  -- For simplicity, we generate refinements for Boolean semantics
  -- Convert base to Boolean (threshold at 0.5)
  let baseBool : U → W → Bool := fun u w => base.meaning u w > 0
  -- Get refinements for each utterance
  let _uttRefinements : List (U × List (Refinement W)) :=
    utterances.map fun u => (u, allRefinements worlds (baseBool u))
  -- Take product over all utterances to get all possible lexica
  -- For now, just return the base lexicon and some key refinements
  -- (Full enumeration is exponential; we'll be selective)
  [base]

end LexicalRefinement

-- ============================================================================
-- LU-RSA Computations
-- ============================================================================

namespace LURSA

/--
L₀ given a specific lexicon.

P(w | u, L) ∝ P(w) · L(u, w)

This is the standard literal listener, but parameterized by lexicon L.
-/
def L0_given (S : LUScenario) (L : Lexicon S.Utterance S.World)
    (u : S.Utterance) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w => (w, S.worldPrior w * L.meaning u w)
  RSA.normalize scores

/--
S₁ given a specific lexicon.

P(u | w, L) ∝ L₀(w | u, L)^α

The speaker believes the literal listener is using lexicon L.
-/
def S1_given (S : LUScenario) (L : Lexicon S.Utterance S.World)
    (w : S.World) : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u => (u, (RSA.getScore (L0_given S L u) w) ^ S.α)
  RSA.normalize scores

/--
L₁ with lexical uncertainty: THE KEY INNOVATION.

P(w | u) ∝ P(w) · Σ_L P(L) · S₁(u | w, L)

The pragmatic listener:
1. Considers each possible lexicon L ∈ Λ
2. Reasons about what S₁ would do if using that lexicon
3. Marginalizes over lexica weighted by their prior probability

This is Equation (29) in Bergen et al. (2016).
-/
def L1 (S : LUScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w =>
    -- Sum over lexica: Σ_L P(L) · S1(u | w, L)
    let lexSum := S.lexica.foldl (init := (0 : ℚ)) fun acc L =>
      acc + S.lexPrior L * RSA.getScore (S1_given S L w) u
    (w, S.worldPrior w * lexSum)
  RSA.normalize scores

/--
Joint distribution over (World × Lexicon) given utterance.

P(w, L | u) ∝ P(w) · P(L) · S₁(u | w, L)

Useful for understanding which lexicon the listener infers.
-/
def L1_joint (S : LUScenario) (u : S.Utterance)
    : List ((S.World × Lexicon S.Utterance S.World) × ℚ) :=
  let pairs := S.worlds.flatMap fun w => S.lexica.map fun L => (w, L)
  let scores := pairs.map fun (w, L) =>
    let priorScore := S.worldPrior w * S.lexPrior L
    let s1Score := RSA.getScore (S1_given S L w) u
    ((w, L), priorScore * s1Score)
  RSA.normalize scores

/--
Marginal over lexica: P(L | u) = Σ_w P(w, L | u)

What lexicon does the listener think is being used?
-/
def L1_lexicon (S : LUScenario) [BEq (Lexicon S.Utterance S.World)]
    (u : S.Utterance) : List (Lexicon S.Utterance S.World × ℚ) :=
  let joint := L1_joint S u
  S.lexica.map fun L =>
    let lScores := joint.filter (·.1.2 == L) |>.map (·.2)
    (L, RSA.sumScores lScores)

-- ============================================================================
-- Convenience accessors
-- ============================================================================

/-- Get L₀ probability for a specific world given a lexicon -/
def L0_prob (S : LUScenario) (L : Lexicon S.Utterance S.World)
    (u : S.Utterance) (w : S.World) : ℚ :=
  RSA.getScore (L0_given S L u) w

/-- Get S₁ probability for a specific utterance given a lexicon -/
def S1_prob (S : LUScenario) (L : Lexicon S.Utterance S.World)
    (w : S.World) (u : S.Utterance) : ℚ :=
  RSA.getScore (S1_given S L w) u

/-- Get L₁ probability for a specific world (with lexical uncertainty) -/
def L1_prob (S : LUScenario) (u : S.Utterance) (w : S.World) : ℚ :=
  RSA.getScore (L1 S u) w

end LURSA

-- ============================================================================
-- Converting between LUScenario and RSAScenario
-- ============================================================================

/--
Create an LUScenario from basic components with a single lexicon.

This is the degenerate case: no lexical uncertainty, equivalent to standard RSA.
-/
def LUScenario.ofBasic {U W : Type} [BEq U] [BEq W]
    (utts : List U) (worlds : List W)
    (φ : U → W → ℚ) (prior : W → ℚ := fun _ => 1) (α : ℕ := 1) : LUScenario where
  Utterance := U
  World := W
  baseLexicon := Lexicon.ofScenario utts worlds φ
  lexica := [Lexicon.ofScenario utts worlds φ]
  lexPrior := fun _ => 1
  worldPrior := prior
  utterances := utts
  worlds := worlds
  α := α

/--
Project an LUScenario to an RSAScenario using the base lexicon.

Useful for comparing LU-RSA predictions to standard RSA.
-/
def LUScenario.toRSAScenario (S : LUScenario) [DecidableEq S.World] : RSAScenario :=
  RSAScenario.basic S.utterances S.worlds S.baseLexicon.meaning S.worldPrior S.α

-- ============================================================================
-- M-Implicature Scenario Builder
-- ============================================================================

/--
Build a scenario for M-implicatures (Horn 1984 / Division of Pragmatic Labor).

Given:
- Two semantically equivalent utterances (SHORT and long)
- Two interpretations (FREQ = common, rare = uncommon)
- Prior favoring FREQ

Lexical uncertainty predicts: SHORT → FREQ, long → rare
-/
def mkMImplicatureScenario {U W : Type} [BEq U] [BEq W]
    (SHORT long : U) (FREQ rare : W)
    (freqPrior : ℚ := 2/3) : LUScenario where
  Utterance := U
  World := W
  baseLexicon := { meaning := fun _ _ => 1 }  -- Both utterances true everywhere
  -- Three lexica: base + two where one utterance is specialized
  lexica := [
    -- L₁: Both utterances mean {FREQ, rare} (unrefined)
    { meaning := fun _ _ => 1 },
    -- L₂: SHORT means {FREQ}, long means {FREQ, rare}
    { meaning := fun u w => if u == SHORT then (if w == FREQ then 1 else 0) else 1 },
    -- L₃: SHORT means {FREQ, rare}, long means {rare}
    { meaning := fun u w => if u == long then (if w == rare then 1 else 0) else 1 },
    -- L₄: SHORT means {FREQ}, long means {rare}
    { meaning := fun u w =>
        if u == SHORT then (if w == FREQ then 1 else 0)
        else if u == long then (if w == rare then 1 else 0)
        else 1 }
  ]
  worldPrior := fun w => if w == FREQ then freqPrior else (1 - freqPrior)
  utterances := [SHORT, long]
  worlds := [FREQ, rare]

-- ============================================================================
-- Some-or-All Ignorance Implicature
-- ============================================================================

/--
Observation states for ignorance implicatures.

The speaker may:
- Know all passed (∀)
- Know some-but-not-all passed (∃¬∀)
- Be ignorant (?)
-/
inductive ObsState where
  | knowAll      -- Speaker observed all passed
  | knowSomeNot  -- Speaker observed some-but-not-all passed
  | ignorant     -- Speaker made no observation
  deriving Repr, BEq, DecidableEq

/--
World states for scalar scenarios.
-/
inductive ScalarWorld where
  | all     -- All passed
  | someNot -- Some but not all passed
  deriving Repr, BEq, DecidableEq

/--
Utterances for some-or-all ignorance implicatures.
-/
inductive SomeOrAllUtt where
  | all_
  | some_
  | someOrAll
  deriving Repr, BEq, DecidableEq

/--
Build a scenario for "some or all" ignorance implicatures.

Key prediction: "some or all" → speaker is ignorant
-/
def mkSomeOrAllScenario : LUScenario where
  Utterance := SomeOrAllUtt
  World := ObsState  -- Using observation states as "worlds" for this model
  baseLexicon := { meaning := fun u _ =>
    match u with
    | .all_ => 1  -- "all" compatible with knowAll
    | .some_ => 1  -- "some" compatible with all states (weak reading)
    | .someOrAll => 1  -- "some or all" compatible with all states
  }
  -- Lexica with different refinements of "some"
  lexica := [
    -- L₁: Unrefined (base)
    { meaning := fun u o =>
        match u, o with
        | .all_, .knowAll => 1
        | .all_, _ => 0
        | .some_, _ => 1
        | .someOrAll, _ => 1 },
    -- L₂: "some" refined to {knowSomeNot}
    { meaning := fun u o =>
        match u, o with
        | .all_, .knowAll => 1
        | .all_, _ => 0
        | .some_, .knowSomeNot => 1
        | .some_, _ => 0
        | .someOrAll, _ => 1 },
    -- L₃: "some" refined to {knowAll}
    { meaning := fun u o =>
        match u, o with
        | .all_, .knowAll => 1
        | .all_, _ => 0
        | .some_, .knowAll => 1
        | .some_, _ => 0
        | .someOrAll, _ => 1 }
  ]
  worldPrior := fun _ => 1  -- Uniform over observation states
  utterances := [.all_, .some_, .someOrAll]
  worlds := [.knowAll, .knowSomeNot, .ignorant]

-- ============================================================================
-- Theorems
-- ============================================================================

namespace LUTheorems

/--
With a single lexicon, LU-RSA reduces to standard RSA.

When |Λ| = 1, the marginalization is trivial and L₁_LU = L₁_standard.
-/
theorem single_lexicon_reduces_to_rsa {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utts : List U) (worlds : List W) (φ : U → W → ℚ)
    (prior : W → ℚ := fun _ => 1) (α : ℕ := 1) :
    let LU := LUScenario.ofBasic utts worlds φ prior α
    let S := RSAScenario.basic utts worlds φ prior α
    ∀ u w, LURSA.L1_prob LU u w = RSA.getScore (RSA.L1_world S u) w := by
  intro u w
  -- The proof requires showing that with single lexicon,
  -- the marginalization is trivial
  sorry  -- TODO: complete proof

/--
Symmetry breaking: semantically equivalent utterances can get different interpretations.

This is the key property that enables M-implicatures.
-/
theorem symmetry_breaking_possible :
    ∃ (S : LUScenario) (u₁ u₂ : S.Utterance) (w : S.World),
      -- u₁ and u₂ have same base meaning
      S.baseLexicon.meaning u₁ = S.baseLexicon.meaning u₂ ∧
      -- But different L₁ interpretations
      LURSA.L1_prob S u₁ w ≠ LURSA.L1_prob S u₂ w := by
  sorry  -- TODO: construct concrete counterexample

end LUTheorems
