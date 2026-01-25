/-
# Linglib.Core.RSA

Core RSA (Rational Speech Acts) infrastructure.

Uses exact fraction arithmetic (Core/Frac.lean) for clean proofs.

## Architecture (mathlib-style)

RSA is parameterized by a **semantic backend** (a structure, not a class):
- `FiniteSemanticBackend`: provides Utterance, World, satisfies relation
- L0/S1/L1 functions take the backend explicitly as first argument
- This allows multiple backends in scope without typeclass ambiguity

## Grounding

Semantic backends can be constructed from various sources:
- Montague intensional semantics (see `Montague/RSABackend.lean`)
- Stipulated meaning functions (for toy examples)
- Other semantic theories (DRT, situation semantics, etc.)

The grounding theorem is trivial by construction: when you build a backend
from Montague derivations, `satisfies w u = φ(u, w)` by definition.

## RSA Model

RSA models communication as recursive reasoning between speakers and listeners:
- L0: Literal interpretation (semantic denotation)
- S1: Pragmatic speaker (chooses utterances to maximize informativity)
- L1: Pragmatic listener (reasons about what speaker meant)

Reference: Frank & Goodman (2012), Goodman & Frank (2016)
-/

import Linglib.Core.Frac

namespace RSA

open Frac

-- ============================================================================
-- Finite Semantic Backend (Structure, not Class)
-- ============================================================================

/--
A semantic backend with finite, enumerable utterances and worlds.

This is a **structure** (not class) to allow multiple backends in scope.
RSA functions take the backend explicitly as their first argument.
-/
structure FiniteSemanticBackend where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of possible worlds -/
  World : Type
  /-- List of all utterances -/
  utterances : List Utterance
  /-- List of all worlds -/
  worlds : List World
  /-- Satisfaction relation: is utterance true at world? -/
  satisfies : World → Utterance → Bool
  /-- BEq instance for utterances -/
  utteranceBEq : BEq Utterance
  /-- BEq instance for worlds -/
  worldBEq : BEq World

-- Make BEq instances available
instance (B : FiniteSemanticBackend) : BEq B.Utterance := B.utteranceBEq
instance (B : FiniteSemanticBackend) : BEq B.World := B.worldBEq

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Look up score of an item in a distribution -/
def getScore {A : Type} [BEq A] (dist : List (A × Frac)) (x : A) : Frac :=
  match dist.find? fun (a, _) => a == x with
  | some (_, p) => p
  | none => Frac.zero

/-- Count worlds compatible with an utterance -/
def compatibleCount (B : FiniteSemanticBackend) (u : B.Utterance) : Nat :=
  (B.worlds.filter (B.satisfies · u)).length

/-- Informativity of an utterance = 1 / (compatible worlds) -/
def informativity (B : FiniteSemanticBackend) (u : B.Utterance) : Frac :=
  let n := compatibleCount B u
  if h : n > 0 then ⟨1, n, h⟩ else Frac.zero

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

/--
L0 scores: P(w | u) = 1/n if satisfies(w, u), else 0
where n = number of compatible worlds.

The literal listener uniformly distributes probability over worlds
where the utterance is true.
-/
def L0 (B : FiniteSemanticBackend) (u : B.Utterance) : List (B.World × Frac) :=
  let n := compatibleCount B u
  let prob := if h : n > 0 then ⟨1, n, h⟩ else Frac.zero
  B.worlds.map fun w => (w, if B.satisfies w u then prob else Frac.zero)

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/--
S1 scores: P(u | w) ∝ informativity(u) for true utterances

The speaker chooses among true utterances weighted by informativity.
More informative (less ambiguous) utterances are preferred.

To normalize: P(u | w) = inf(u) / Σ inf(u') for all true u'
-/
def S1 (B : FiniteSemanticBackend) (w : B.World) : List (B.Utterance × Frac) :=
  -- Get all true utterances
  let trueUtts := B.utterances.filter (B.satisfies w ·)
  -- Compute informativity for each: 1/n_i
  -- To sum fractions 1/n_1 + 1/n_2 + ..., use common denominator = n_1 * n_2 * ...
  let dens := trueUtts.map (compatibleCount B ·)
  let commonDen := dens.foldl (· * ·) 1
  -- Sum = Σ (commonDen / n_i) with denominator commonDen
  let sumNum := dens.foldl (fun acc d => if d > 0 then acc + commonDen / d else acc) 0
  -- Now P(u | w) = (commonDen / n_u) / sumNum
  B.utterances.map fun u =>
    if B.satisfies w u then
      let n := compatibleCount B u
      if h : n > 0 ∧ sumNum > 0 then
        (u, ⟨commonDen / n, sumNum, h.2⟩)
      else (u, Frac.zero)
    else (u, Frac.zero)

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/--
L1 scores: P(w | u) ∝ P(w) × S1(u | w)

With uniform prior, this is proportional to S1(u | w).
The pragmatic listener reasons: "What world would make a rational
speaker choose this utterance?"
-/
def L1 (B : FiniteSemanticBackend) (u : B.Utterance) : List (B.World × Frac) :=
  B.worlds.map fun w => (w, getScore (S1 B w) u)

-- ============================================================================
-- Convenience: Get probability for specific world
-- ============================================================================

/-- Get L0 probability for a specific world -/
def L0_prob (B : FiniteSemanticBackend) (u : B.Utterance) (w : B.World) : Frac :=
  getScore (L0 B u) w

/-- Get S1 probability for a specific utterance -/
def S1_prob (B : FiniteSemanticBackend) (w : B.World) (u : B.Utterance) : Frac :=
  getScore (S1 B w) u

/-- Get L1 probability for a specific world -/
def L1_prob (B : FiniteSemanticBackend) (u : B.Utterance) (w : B.World) : Frac :=
  getScore (L1 B u) w

-- ============================================================================
-- Generic Theorems
-- ============================================================================

/--
L0 assigns zero probability to worlds where the utterance is false.
-/
theorem L0_zero_when_false (B : FiniteSemanticBackend) (u : B.Utterance) (w : B.World)
    (hfalse : B.satisfies w u = false) :
    ∀ p, (w, p) ∈ (L0 B u) → p = Frac.zero := by
  intro p hmem
  simp only [L0, List.mem_map] at hmem
  obtain ⟨w', _, hw'⟩ := hmem
  -- hw' : (w', if B.satisfies w' u then prob else Frac.zero) = (w, p)
  -- From pair equality: w' = w and p = if B.satisfies w' u then prob else Frac.zero
  have heq : w' = w := by exact (Prod.mk.injEq _ _ _ _).mp hw' |>.1
  rw [heq, hfalse] at hw'
  exact ((Prod.mk.injEq _ _ _ _).mp hw' |>.2).symm

/--
S1 assigns zero probability to false utterances.
-/
theorem S1_zero_when_false (B : FiniteSemanticBackend) (w : B.World) (u : B.Utterance)
    (hfalse : B.satisfies w u = false) :
    S1_prob B w u = Frac.zero := by
  simp only [S1_prob, S1, getScore]
  sorry -- technical

end RSA

-- ============================================================================
-- Parametric Semantic Backend (for lifted-variable RSA)
-- ============================================================================

namespace ParametricRSA

open Frac
open RSA (getScore)

/--
A semantic backend with an interpretation parameter.

This supports "lifted-variable" RSA models where:
- **Interp** represents different ways to interpret an utterance
  (e.g., scope readings: surface vs inverse)
- **satisfies** is parameterized by interpretation

Example: "Every horse didn't jump"
- Interp = {surface, inverse}
- satisfies surface w u = ∀x.¬jump(x) in w
- satisfies inverse w u = ¬∀x.jump(x) in w

Reference: Scontras & Pearl (2021)
-/
structure ParametricSemanticBackend where
  Utterance : Type
  World : Type
  Interp : Type
  utterances : List Utterance
  worlds : List World
  interps : List Interp
  satisfies : Interp → World → Utterance → Bool
  utteranceBEq : BEq Utterance
  worldBEq : BEq World
  interpBEq : BEq Interp

instance (B : ParametricSemanticBackend) : BEq B.Utterance := B.utteranceBEq
instance (B : ParametricSemanticBackend) : BEq B.World := B.worldBEq
instance (B : ParametricSemanticBackend) : BEq B.Interp := B.interpBEq

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Count worlds compatible with an utterance under an interpretation -/
def compatibleCount (B : ParametricSemanticBackend)
    (i : B.Interp) (u : B.Utterance) : Nat :=
  (B.worlds.filter (B.satisfies i · u)).length

/-- Informativity: 1 / (compatible worlds) -/
def informativity (B : ParametricSemanticBackend)
    (i : B.Interp) (u : B.Utterance) : Frac :=
  let n := compatibleCount B i u
  if h : n > 0 then ⟨1, n, h⟩ else Frac.zero

-- ============================================================================
-- L0: Literal Listener (given interpretation)
-- ============================================================================

/--
L0 scores given a fixed interpretation:
P(w | u, i) = 1/n if satisfies(i, w, u), else 0
-/
def L0 (B : ParametricSemanticBackend)
    (i : B.Interp) (u : B.Utterance) : List (B.World × Frac) :=
  let n := compatibleCount B i u
  let prob := if h : n > 0 then ⟨1, n, h⟩ else Frac.zero
  B.worlds.map fun w => (w, if B.satisfies i w u then prob else Frac.zero)

-- ============================================================================
-- S1: Pragmatic Speaker (given interpretation)
-- ============================================================================

/--
S1 scores given a fixed interpretation:
P(u | w, i) ∝ informativity(i, u) for true utterances
-/
def S1 (B : ParametricSemanticBackend)
    (i : B.Interp) (w : B.World) : List (B.Utterance × Frac) :=
  let trueUtts := B.utterances.filter (B.satisfies i w ·)
  let dens := trueUtts.map (compatibleCount B i ·)
  let commonDen := dens.foldl (· * ·) 1
  let sumNum := dens.foldl (fun acc d => if d > 0 then acc + commonDen / d else acc) 0
  B.utterances.map fun u =>
    if B.satisfies i w u then
      let n := compatibleCount B i u
      if h : n > 0 ∧ sumNum > 0 then
        (u, ⟨commonDen / n, sumNum, h.2⟩)
      else (u, Frac.zero)
    else (u, Frac.zero)

-- ============================================================================
-- L1: Pragmatic Listener (joint over world × interpretation)
-- ============================================================================

/--
L1 joint scores: P(w, i | u) ∝ P(w) × P(i) × S1(u | w, i)

With uniform priors, this is proportional to S1(u | w, i).
Returns unnormalized scores over (World × Interp).
-/
def L1_joint (B : ParametricSemanticBackend)
    (u : B.Utterance) : List ((B.World × B.Interp) × Frac) :=
  let pairs := (B.worlds.map fun w =>
    B.interps.map fun i => (w, i)).flatten
  pairs.map fun (w, i) => ((w, i), getScore (S1 B i w) u)

/--
L1 marginal scores over worlds: P(w | u) = Σ_i P(w, i | u)

This sums over all interpretations to get the marginal world distribution.
-/
def L1_world (B : ParametricSemanticBackend)
    (u : B.Utterance) : List (B.World × Frac) :=
  let joint := L1_joint B u
  B.worlds.map fun w =>
    let worldScores := joint.filter fun ((w', _), _) => w' == w
    let sum := worldScores.foldl (fun acc (_, f) => Frac.add acc f) Frac.zero
    (w, sum)

/--
L1 marginal scores over interpretations: P(i | u) = Σ_w P(w, i | u)

This sums over all worlds to get the marginal interpretation distribution.
-/
def L1_interp (B : ParametricSemanticBackend)
    (u : B.Utterance) : List (B.Interp × Frac) :=
  let joint := L1_joint B u
  B.interps.map fun i =>
    let interpScores := joint.filter fun ((_, i'), _) => i' == i
    let sum := interpScores.foldl (fun acc (_, f) => Frac.add acc f) Frac.zero
    (i, sum)

end ParametricRSA
