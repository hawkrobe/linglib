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
