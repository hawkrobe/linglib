import Linglib.Core.Logic.ConstraintEvaluation
import Linglib.Theories.Pragmatics.Bidirectional
import Linglib.Theories.Semantics.Presupposition.Accommodation

/-!
# @cite{blutner-2000} — Presupposition Projection via Bidirectional OT

@cite{blutner-2000} @cite{van-der-sandt-1992} @cite{geurts-1995}

Some Aspects of Optimality in Natural Language Interpretation.
Journal of Semantics 17(3): 189–216.

## Overview

Section 4 of @cite{blutner-2000} reconstructs @cite{van-der-sandt-1992}'s
and @cite{geurts-1995}'s presupposition projection mechanism within
bidirectional OT. The I-principle (interpretation optimality) selects the
preferred accommodation site; the Q-principle (production optimality)
blocks accommodation when a simpler expression alternative exists.

## Two Constraints

- **AvoidA** (Avoid Accommodation): counts the number of discourse markers
  that require accommodation. Binding (resolving against existing context)
  is preferred over accommodation. This captures @cite{van-der-sandt-1992}'s
  and @cite{geurts-1995}'s first preference (binding > accommodation).

- **BeStrong**: ranks interpretations by logical strength (entailment).
  Stronger (more informative) outcomes are preferred. This captures
  @cite{geurts-1995}'s second preference (higher accommodation site
  yields stronger interpretation, ceteris paribus).

Ranking: AvoidA >> BeStrong.

## Application

### Example (18): "If Peter has a dog, then his cat is gray"

Three projection sites for the presupposition "Peter has a cat":
- τ₁ (local): accommodate in consequent — requires accommodation
- τ₂ (intermediate): accommodate in antecedent — requires accommodation
- τ₃ (global): accommodate globally — requires accommodation

All three violate AvoidA. BeStrong is decisive: global accommodation
(τ₃) gives the strongest interpretation → selected.

### Example (19): "If Peter has a cat, then his cat is gray"

Three projection sites:
- τ₁ (local): requires accommodation (AvoidA violated)
- τ₂ (intermediate): allows binding/factoring (AvoidA satisfied)
- τ₃ (global): requires accommodation (AvoidA violated)

AvoidA selects τ₂ (intermediate) — the only site where the
presupposition is bound rather than accommodated.

### Accommodation blocking (Q-principle)

@cite{blutner-2000} §4, example (25): accommodation of "the car"
is blocked when a simpler expression "a car" achieves the same
context change without triggering presupposition. This is
Q-principle blocking: the presuppositional form is more complex
than the non-presuppositional alternative.
-/

set_option autoImplicit false

namespace Phenomena.Presupposition.Studies.Blutner2000

open Core.ConstraintEvaluation

-- ============================================================================
-- § 1: Projection Sites
-- ============================================================================

/-- Presupposition projection sites, following @cite{van-der-sandt-1992}. -/
inductive ProjectionSite where
  | local         -- accommodate in the most embedded position
  | intermediate  -- accommodate at an intermediate level (e.g., antecedent)
  | global        -- accommodate at the top-level discourse context
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Constraints
-- ============================================================================

/-- **AvoidA** (Avoid Accommodation): counts accommodated discourse markers.
    0 = bound (no accommodation needed), n = n markers accommodated.

    Captures @cite{van-der-sandt-1992}'s preference for binding over
    accommodation and @cite{geurts-1995}'s preference (i). -/
abbrev AvoidA := Nat

/-- **BeStrong**: ranks by logical strength of the resulting interpretation.
    Lower values = stronger interpretation.

    Captures @cite{geurts-1995}'s preference (ii): prefer higher
    accommodation sites (which yield stronger interpretations). -/
abbrev Strength := Nat

-- ============================================================================
-- § 3: Example (18) — "If Peter has a dog, then his cat is gray"
-- ============================================================================

/-! Presupposition: "Peter has a cat" (triggered by "his cat").
    Context: empty (∅). No antecedent provides a cat.
    All three sites require accommodation (no binding possible). -/

/-- The input form for example (18). Only one form (the presuppositional
    sentence). The competition is among interpretations (projection sites). -/
inductive Form18 where | sentence deriving DecidableEq, BEq, Repr

/-- Generator: one form, three projection sites. -/
def gen18 : List (Form18 × ProjectionSite) :=
  [(.sentence, .local), (.sentence, .intermediate), (.sentence, .global)]

/-- Constraint profile: [AvoidA, BeStrong].
    All three sites require accommodation (AvoidA = 1).
    Strength: global (0) > intermediate (1) > local (2). -/
def profile18 : Form18 × ProjectionSite → List Nat
  | (.sentence, .global)       => [1, 0]  -- accommodated, strongest
  | (.sentence, .intermediate) => [1, 1]  -- accommodated, medium
  | (.sentence, .local)        => [1, 2]  -- accommodated, weakest

/-- Example (18): AvoidA is tied (all sites accommodate), so BeStrong
    is decisive. Global accommodation wins (strongest interpretation). -/
theorem ex18_global_wins :
    superoptimal gen18 profile18 = [(.sentence, .global)] := by
  native_decide

-- ============================================================================
-- § 4: Example (19) — "If Peter has a cat, then his cat is gray"
-- ============================================================================

/-! Presupposition: "Peter has a cat" (triggered by "his cat").
    Context: empty (∅), but the antecedent introduces "Peter has a cat".
    At the intermediate site, the presupposition can be BOUND (factored)
    against the antecedent — no accommodation needed. -/

/-- Generator for example (19). -/
inductive Form19 where | sentence deriving DecidableEq, BEq, Repr

def gen19 : List (Form19 × ProjectionSite) :=
  [(.sentence, .local), (.sentence, .intermediate), (.sentence, .global)]

/-- Constraint profile for example (19): [AvoidA, BeStrong].
    Intermediate: binding possible → AvoidA = 0.
    Local and global: accommodation required → AvoidA = 1.
    Strength: global (0) > intermediate (1) > local (2). -/
def profile19 : Form19 × ProjectionSite → List Nat
  | (.sentence, .global)       => [1, 0]  -- accommodated, strongest
  | (.sentence, .intermediate) => [0, 1]  -- BOUND (factored), medium
  | (.sentence, .local)        => [1, 2]  -- accommodated, weakest

/-- Example (19): AvoidA is decisive — intermediate projection allows
    binding (0 violations) while local and global require accommodation.
    BeStrong is irrelevant since AvoidA already discriminates. -/
theorem ex19_intermediate_wins :
    superoptimal gen19 profile19 = [(.sentence, .intermediate)] := by
  native_decide

-- ============================================================================
-- § 5: Accommodation Blocking (Q-Principle)
-- ============================================================================

/-! @cite{blutner-2000} example (25): "He had an accident. ??The car hit him."
    vs "He had an accident. A car hit him."

    "The car" triggers the presupposition that there is a unique salient car.
    "A car" does not trigger this presupposition.

    Starting from a neutral context (no car introduced), both sentences
    achieve the same context change — but "the car" requires accommodation
    while "a car" does not. The Q-principle blocks accommodation of "the car"
    because the simpler alternative "a car" achieves the same effect. -/

/-- Two forms: the presuppositional definite and the indefinite. -/
inductive DefForm where
  | definite    -- "the car hit him" (triggers presupposition)
  | indefinite  -- "a car hit him" (no presupposition)
  deriving DecidableEq, BEq, Repr

/-- The shared meaning (same context change result). -/
inductive AccidentMeaning where
  | carHitHim  -- the resulting interpretation
  deriving DecidableEq, BEq, Repr

/-- Generator: both forms map to the same meaning. -/
def genAccident : List (DefForm × AccidentMeaning) :=
  [(.definite, .carHitHim), (.indefinite, .carHitHim)]

/-- Profile: [FormComplexity, AccommodationCost].
    The definite requires accommodation (more complex pragmatically);
    the indefinite does not. -/
def profileAccident : DefForm × AccidentMeaning → List Nat
  | (.definite,   .carHitHim) => [1, 0]  -- accommodation needed
  | (.indefinite, .carHitHim) => [0, 0]  -- no accommodation

/-- Q-principle blocks the definite: the indefinite achieves the same
    meaning with fewer violations. The definite form is blocked
    (pragmatically anomalous) in neutral contexts. -/
theorem accommodation_blocked :
    superoptimal genAccident profileAccident =
      [(.indefinite, .carHitHim)] := by
  native_decide

/-- This is a Q-principle effect: the definite is blocked because
    a competing form (indefinite) with the same meaning is better. -/
theorem accommodation_blocked_is_Q :
    Theories.Pragmatics.Bidirectional.satisfiesQ
      genAccident profileAccident (.definite, .carHitHim) = false := by
  native_decide

/-- The indefinite satisfies both Q and I. -/
theorem indefinite_satisfies_both :
    Theories.Pragmatics.Bidirectional.satisfiesQ
      genAccident profileAccident (.indefinite, .carHitHim) = true ∧
    Theories.Pragmatics.Bidirectional.satisfiesI
      genAccident profileAccident (.indefinite, .carHitHim) = true := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 6: Connection to Accommodation Infrastructure
-- ============================================================================

/-! @cite{blutner-2000}'s projection sites correspond to the accommodation
    levels in `Semantics.Presupposition.Accommodation`. The bridge makes
    explicit that Blutner's OT analysis operates over the same site taxonomy
    as the Heim/Lewis/van der Sandt tradition. -/

open Semantics.Presupposition.Accommodation (AccommodationLevel)

/-- Map projection sites to the standard accommodation levels. -/
def ProjectionSite.toAccommodationLevel : ProjectionSite → AccommodationLevel
  | .local        => .local
  | .intermediate => .intermediate 0  -- depth 0 = immediate superordinate DRS
  | .global       => .global

/-- Global projection corresponds to global accommodation. -/
theorem global_is_global_accommodation :
    ProjectionSite.global.toAccommodationLevel = AccommodationLevel.global := rfl

/-- Local projection corresponds to local accommodation. -/
theorem local_is_local_accommodation :
    ProjectionSite.local.toAccommodationLevel = AccommodationLevel.local := rfl

end Phenomena.Presupposition.Studies.Blutner2000
