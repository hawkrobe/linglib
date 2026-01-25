/-
# Linglib.Core.RSA

Core RSA (Rational Speech Acts) infrastructure.

Uses exact fraction arithmetic (Core/Frac.lean) for clean proofs.

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
-- Finite Semantic Backend
-- ============================================================================

/--
A semantic backend with finite, enumerable utterances and worlds.
-/
class FiniteSemanticBackend (S : Type) where
  Utterance : Type
  World : Type
  utterances : List Utterance
  worlds : List World
  meaning : Utterance → World → Bool
  [utteranceBEq : BEq Utterance]
  [worldBEq : BEq World]

attribute [instance] FiniteSemanticBackend.utteranceBEq
attribute [instance] FiniteSemanticBackend.worldBEq

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Look up score of an item in a distribution -/
def getScore {A : Type} [BEq A] (dist : List (A × Frac)) (x : A) : Frac :=
  match dist.find? λ (a, _) => a == x with
  | some (_, p) => p
  | none => Frac.zero

/-- Count worlds compatible with an utterance -/
def compatibleCount (S : Type) [inst : FiniteSemanticBackend S]
    (u : inst.Utterance) : Nat :=
  (inst.worlds.filter (inst.meaning u)).length

/-- Informativity of an utterance = 1 / (compatible worlds) -/
def informativity (S : Type) [inst : FiniteSemanticBackend S]
    (u : inst.Utterance) : Frac :=
  let n := compatibleCount S u
  if h : n > 0 then ⟨1, n, h⟩ else Frac.zero

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

/--
L0 scores: P(w | u) = 1/n if meaning(u, w), else 0
where n = number of compatible worlds.
-/
def L0_scores (S : Type) [inst : FiniteSemanticBackend S]
    (u : inst.Utterance) : List (inst.World × Frac) :=
  let n := compatibleCount S u
  let prob := if h : n > 0 then ⟨1, n, h⟩ else Frac.zero
  inst.worlds.map λ w => (w, if inst.meaning u w then prob else Frac.zero)

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/--
S1 scores: P(u | w) ∝ informativity(u) for true utterances

The speaker chooses among true utterances weighted by informativity.
More informative (less ambiguous) utterances are preferred.

To normalize: P(u | w) = inf(u) / Σ inf(u') for all true u'
-/
def S1_scores (S : Type) [inst : FiniteSemanticBackend S]
    (w : inst.World) : List (inst.Utterance × Frac) :=
  -- Get all true utterances
  let trueUtts := inst.utterances.filter (λ u => inst.meaning u w)
  -- Compute informativity for each: 1/n_i
  -- To sum fractions 1/n_1 + 1/n_2 + ..., use common denominator = n_1 * n_2 * ...
  let dens := trueUtts.map (λ u => compatibleCount S u)
  let commonDen := dens.foldl (· * ·) 1
  -- Sum = Σ (commonDen / n_i) with denominator commonDen
  let sumNum := dens.foldl (λ acc d => if d > 0 then acc + commonDen / d else acc) 0
  -- Now P(u | w) = (commonDen / n_u) / sumNum = (commonDen / n_u) / sumNum
  inst.utterances.map λ u =>
    if inst.meaning u w then
      let n := compatibleCount S u
      if h : n > 0 ∧ sumNum > 0 then
        -- Numerator = commonDen / n, Denominator = sumNum
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
def L1_scores (S : Type) [inst : FiniteSemanticBackend S]
    (u : inst.Utterance) : List (inst.World × Frac) :=
  inst.worlds.map λ w => (w, getScore (S1_scores S w) u)

end RSA

-- ============================================================================
-- Parametric Semantic Backend (for lifted-variable RSA)
-- ============================================================================

namespace ParametricRSA

open Frac

/--
A semantic backend with an interpretation parameter.

This supports "lifted-variable" RSA models where:
- **Interp** represents different ways to interpret an utterance
  (e.g., scope readings: surface vs inverse)
- **meaning** is parameterized by interpretation

Example: "Every horse didn't jump"
- Interp = {surface, inverse}
- meaning surface u w = ∀x.¬jump(x) in w
- meaning inverse u w = ¬∀x.jump(x) in w

Reference: Scontras & Pearl (2021)
-/
class ParametricSemanticBackend (S : Type) where
  Utterance : Type
  World : Type
  Interp : Type
  utterances : List Utterance
  worlds : List World
  interps : List Interp
  meaning : Interp → Utterance → World → Bool
  [utteranceBEq : BEq Utterance]
  [worldBEq : BEq World]
  [interpBEq : BEq Interp]

attribute [instance] ParametricSemanticBackend.utteranceBEq
attribute [instance] ParametricSemanticBackend.worldBEq
attribute [instance] ParametricSemanticBackend.interpBEq

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Look up score in a distribution -/
def getScore {A : Type} [BEq A] (dist : List (A × Frac)) (x : A) : Frac :=
  match dist.find? λ (a, _) => a == x with
  | some (_, p) => p
  | none => Frac.zero

/-- Count worlds compatible with an utterance under an interpretation -/
def compatibleCount (S : Type) [inst : ParametricSemanticBackend S]
    (i : inst.Interp) (u : inst.Utterance) : Nat :=
  (inst.worlds.filter (inst.meaning i u)).length

/-- Informativity: 1 / (compatible worlds) -/
def informativity (S : Type) [inst : ParametricSemanticBackend S]
    (i : inst.Interp) (u : inst.Utterance) : Frac :=
  let n := compatibleCount S i u
  if h : n > 0 then ⟨1, n, h⟩ else Frac.zero

-- ============================================================================
-- L0: Literal Listener (given interpretation)
-- ============================================================================

/--
L0 scores given a fixed interpretation:
P(w | u, i) = 1/n if meaning(i, u, w), else 0
-/
def L0_scores (S : Type) [inst : ParametricSemanticBackend S]
    (i : inst.Interp) (u : inst.Utterance) : List (inst.World × Frac) :=
  let n := compatibleCount S i u
  let prob := if h : n > 0 then ⟨1, n, h⟩ else Frac.zero
  inst.worlds.map λ w => (w, if inst.meaning i u w then prob else Frac.zero)

-- ============================================================================
-- S1: Pragmatic Speaker (given interpretation)
-- ============================================================================

/--
S1 scores given a fixed interpretation:
P(u | w, i) ∝ informativity(i, u) for true utterances
-/
def S1_scores (S : Type) [inst : ParametricSemanticBackend S]
    (i : inst.Interp) (w : inst.World) : List (inst.Utterance × Frac) :=
  let trueUtts := inst.utterances.filter (λ u => inst.meaning i u w)
  let dens := trueUtts.map (λ u => compatibleCount S i u)
  let commonDen := dens.foldl (· * ·) 1
  let sumNum := dens.foldl (λ acc d => if d > 0 then acc + commonDen / d else acc) 0
  inst.utterances.map λ u =>
    if inst.meaning i u w then
      let n := compatibleCount S i u
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
def L1_joint_scores (S : Type) [inst : ParametricSemanticBackend S]
    (u : inst.Utterance) : List ((inst.World × inst.Interp) × Frac) :=
  let pairs := (inst.worlds.map λ w =>
    inst.interps.map λ i => (w, i)).flatten
  pairs.map λ (w, i) => ((w, i), getScore (S1_scores S i w) u)

/--
L1 marginal scores over worlds: P(w | u) = Σ_i P(w, i | u)

This sums over all interpretations to get the marginal world distribution.
-/
def L1_world_scores (S : Type) [inst : ParametricSemanticBackend S]
    (u : inst.Utterance) : List (inst.World × Frac) :=
  let joint := L1_joint_scores S u
  inst.worlds.map λ w =>
    let worldScores := joint.filter λ ((w', _), _) => w' == w
    let sum := worldScores.foldl (λ acc (_, f) => Frac.add acc f) Frac.zero
    (w, sum)

/--
L1 marginal scores over interpretations: P(i | u) = Σ_w P(w, i | u)

This sums over all worlds to get the marginal interpretation distribution.
-/
def L1_interp_scores (S : Type) [inst : ParametricSemanticBackend S]
    (u : inst.Utterance) : List (inst.Interp × Frac) :=
  let joint := L1_joint_scores S u
  inst.interps.map λ i =>
    let interpScores := joint.filter λ ((_, i'), _) => i' == i
    let sum := interpScores.foldl (λ acc (_, f) => Frac.add acc f) Frac.zero
    (i, sum)

end ParametricRSA
