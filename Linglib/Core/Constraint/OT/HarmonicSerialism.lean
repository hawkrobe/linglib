import Linglib.Core.Constraint.OT.Basic
import Linglib.Core.Constraint.OT.EvalMode
import Linglib.Core.Constraint.OT.Iteration

/-!
# Harmonic Serialism — The Combinator
@cite{mccarthy-2000} @cite{mccarthy-2010} @cite{pruitt-2023}
@cite{lamont-2022a} @cite{lamont-2022b}

Bundles a one-step `gen` function and a constraint ranking into an
`HSDerivation`. Reuses the iteration combinator from `Iteration.lean`
and the existing parallel `Tableau`/`mkTableau` machinery from
`Basic.lean` (Layered Grounding — does not duplicate parallel
optimization).

## NOTE on theoretical scope

Per @cite{pruitt-2023} (Table 1): HS does **not** solve counterfeeding
underapplication, and only patches counterbleeding overapplication with
extra GEN assumptions. This file's docstring deliberately does not claim
HS is "the serial OT solution to opacity" — that would misrepresent the
field's current understanding. HS is one constraint-based serial framework
with mixed empirical record; @cite{mcpherson-lamont-2026} is the
motivating positive case for the directional variant of HS
(@cite{lamont-2022b}). For counterfeeding cases linglib offers
`Theories/Phonology/Process/RuleBased/` (extrinsic ordering) and
`Theories/Phonology/OptimalityTheory/StratalOT.lean` (cyclic ranking) as
architecturally-distinct alternatives.

## Sibling architectures

OT has multiple "more than one EVAL call" specializations, all sharing
the parallel-OT primitives in `Basic.lean`:

| Theory                        | Ranking across calls | Candidate across calls |
|-------------------------------|----------------------|------------------------|
| Parallel OT (`Basic.lean`)    | n/a (single call)    | n/a                    |
| Stratal OT (`StratalOT.lean`) | varies per stratum   | chained via `bridge`   |
| HS (this file)                | **durable**          | iterated via `gen`     |
| Stratal HS (not yet)          | varies per stratum   | iterated within stratum |

HS and Stratal OT are **sister specializations**, not nested: HS holds
ranking constant and varies the candidate; Stratal OT varies the ranking
and chains the candidate. Stratal HS combines both axes and is
deferred (cf. @cite{pruitt-2023} §2.4).

## Sibling, not refactor

This module does **not** modify `NamedConstraint` or `Tableau`
(load-bearing for `Weighted.lean`/`MaxEnt.lean`/`NoisyHG.lean` and ~30
study files). The `stepOptimum` function builds an inner `Tableau` and
reuses `Tableau.optimal` directly. Future directional dispatch
(@cite{lamont-2022b}; @cite{eisner-2000}) will land as a sibling
`DirectionalTableau` consumer; deliberately not stubbed here, to avoid
silently routing directional callers to the parallel optimum.
-/

namespace Core.Constraint.OT

open Core.Constraint.Evaluation

-- ============================================================================
-- § 1: HSDerivation Specification
-- ============================================================================

/-- A Harmonic Serialism derivation specification.

    `gen` is the one-step candidate-generation function (per
    @cite{mccarthy-2008b}'s restricted GEN). `ranking` is a list of
    named constraints, indexed by rank position (head = highest). The
    inner `Tableau` width is inferred from `ranking.length`; no separate
    length parameter is exposed. -/
structure HSDerivation (C : Type*) [DecidableEq C] where
  gen : C → Finset C
  ranking : List (NamedConstraint C)

namespace HSDerivation

variable {C : Type*} [DecidableEq C]

-- ============================================================================
-- § 2: Inner Tableau and Optimal Set
-- ============================================================================

/-- Build a `Tableau` from an explicit candidate set, given `D.ranking`.
    Defined when the candidate set is non-empty. Reuses `mkProfile`
    (Layered Grounding — does not duplicate the `buildViolationProfile`
    body). -/
def tableauFor (D : HSDerivation C) (cands : Finset C) (h : cands.Nonempty) :
    Tableau C D.ranking.length :=
  { candidates := cands
    profile := mkProfile D.ranking
    nonempty := h }

/-- The inner tableau's profile is exactly `mkProfile D.ranking`. -/
@[simp] theorem tableauFor_profile (D : HSDerivation C) (cands : Finset C)
    (h : cands.Nonempty) : (D.tableauFor cands h).profile = mkProfile D.ranking :=
  rfl

/-- Filter a candidate set to its optimal subset under `D.ranking`.
    Returns `∅` on empty input. Routes through the existing parallel
    `Tableau.optimal` (Layered Grounding — does not duplicate parallel
    optimization). This is the `eval : Finset C → Finset C` consumed by
    `Iteration.iterateGen`. -/
def evalFilter (D : HSDerivation C) (cands : Finset C) : Finset C :=
  if h : cands.Nonempty then (D.tableauFor cands h).optimal else ∅

/-- Optimal set for one HS step: `evalFilter` applied to `gen c`.
    Equivalently, `Iteration.iterateStep D.gen D.evalFilter c`. -/
def stepOptimum (D : HSDerivation C) (c : C) : Finset C :=
  D.evalFilter (D.gen c)

@[simp] theorem stepOptimum_eq_iterateStep (D : HSDerivation C) (c : C) :
    D.stepOptimum c = iterateStep D.gen D.evalFilter c := rfl

/-- An empty `gen` output yields an empty optimal set. -/
@[simp] theorem stepOptimum_of_empty_gen (D : HSDerivation C) (c : C)
    (h : D.gen c = ∅) : D.stepOptimum c = ∅ := by
  simp [stepOptimum, evalFilter, h]

-- ============================================================================
-- § 3: Convergence
-- ============================================================================

/-- A form `c` has **converged** under `D` iff its optimal set is the
    singleton `{c}` — the faithful candidate is the unique optimum. This
    is the canonical HS halting condition (@cite{mccarthy-2010}).

    Equivalent to mathlib's `Function.IsFixedPt (hsStep D.gen D.evalFilter) {c}`
    via `hsStep_singleton`. -/
def Converged (D : HSDerivation C) (c : C) : Prop :=
  D.stepOptimum c = ({c} : Finset C)

instance (D : HSDerivation C) (c : C) : Decidable (D.Converged c) :=
  decEq (D.stepOptimum c) ({c} : Finset C)

/-- `Converged` is exactly mathlib's `Function.IsFixedPt` applied to the
    powerset-lifted step at the singleton input. The bridge direction is
    `IsFixedPt → Converged` (more complex → simpler), so the simp lemma
    is registered in that direction. -/
@[simp] theorem isFixedPt_hsStep_singleton_iff_converged (D : HSDerivation C) (c : C) :
    Function.IsFixedPt (hsStep D.gen D.evalFilter) ({c} : Finset C) ↔ D.Converged c := by
  simp [Converged, Function.IsFixedPt, hsStep_singleton]

/-- Convenience flip of `isFixedPt_hsStep_singleton_iff_converged`. Not
    a simp lemma in this direction — would rewrite the simpler `Converged`
    form to the more complex `IsFixedPt` form. -/
theorem converged_iff_isFixedPt (D : HSDerivation C) (c : C) :
    D.Converged c ↔ Function.IsFixedPt (hsStep D.gen D.evalFilter) ({c} : Finset C) :=
  (isFixedPt_hsStep_singleton_iff_converged D c).symm

/-- **Sufficient condition for convergence**: when `gen` produces only
    the faithful candidate, the form is converged. This is the structural
    soundness statement that GEN-restriction at a candidate forces the
    HS halting condition. -/
theorem converged_of_singleton_gen (D : HSDerivation C) (c : C)
    (h : D.gen c = ({c} : Finset C)) : D.Converged c := by
  show D.evalFilter (D.gen c) = ({c} : Finset C)
  rw [h]
  show (if h : ({c} : Finset C).Nonempty then (D.tableauFor {c} h).optimal else ∅) =
       ({c} : Finset C)
  rw [dif_pos (Finset.singleton_nonempty c)]
  -- Tableau with a singleton candidate set: optimal = {c}
  ext x
  simp only [Tableau.optimal, tableauFor, Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, ?_⟩⟩
  intro c' hc'; subst hc'; subst hx; rfl

-- ============================================================================
-- § 4: Smart Constructor for n-Step Derivation
-- ============================================================================

/-- n-step HS derivation. Wraps `iterateGen` with `D.gen` and
    `D.stepOptimum`. The caller supplies a `pick : Finset C → Option C`
    tie-breaker used when the optimal set isn't a singleton (which would
    indicate either (a) ties not yet broken by directional eval, or (b)
    a divergent tie in the @cite{pruitt-2009} sense). Returns `none` if
    `pick` ever fails. HS derivations are not in general guaranteed to
    converge — see @cite{lamont-2022b} for non-terminating cases. -/
def derive (D : HSDerivation C) (pick : Finset C → Option C) (c : C)
    (steps : Nat) : Option C :=
  iterateGen D.gen D.evalFilter pick c steps

end HSDerivation

/-- Canonical tie-breaker for `HSDerivation.derive` when `C` carries a
    `LinearOrder`: pick the order-minimal element of the optimal set.
    The ordering is typically incidental (a paper-grounded
    `LinearOrder.lift'` through a `toNat` injection) since vanilla HS
    doesn't specify how to break ties; directional HS replaces this with
    `EvalMode.directional` once the `DirectionalTableau` consumer
    arrives. Promoted out of the `HSDerivation` namespace because it
    operates on bare `Finset C` and is reusable wherever an HS-style
    iteration needs a canonical tie-breaker. -/
def pickByOrder {C : Type*} [LinearOrder C] (s : Finset C) : Option C :=
  if h : s.Nonempty then some (s.min' h) else none

namespace HSDerivation

variable {C : Type*} [DecidableEq C]

-- ============================================================================
-- § 5: Smoke Test
-- ============================================================================

section SmokeTest

/-- Two-character toy alphabet for the substrate's smoke test. -/
inductive Toy | a | b
  deriving DecidableEq, Repr

/-- Toy GEN: every form admits only itself. This makes every form a
    fixed point of every HSDerivation built over `Toy` (no harmonic
    improvement is possible). The smoke test exercises the convergence
    machinery on the trivial-GEN case. -/
def toyGen : Toy → Finset Toy := fun c => {c}

/-- Toy ranking: a single faithfulness constraint that is satisfied by
    every candidate (returns 0 always). Evaluation is then trivially
    parallel. -/
def toyRanking : List (NamedConstraint Toy) :=
  [{ name := "TOY-FAITH", family := .faithfulness, eval := fun _ => 0 }]

/-- The toy HSDerivation. -/
def toyDerivation : HSDerivation Toy :=
  { gen := toyGen, ranking := toyRanking }

/-- **Smoke test**: every form is converged under `toyDerivation`,
    because `toyGen c = {c}` (one-line proof via the substrate's
    `converged_of_singleton_gen` sufficient condition). -/
example (c : Toy) : toyDerivation.Converged c :=
  converged_of_singleton_gen toyDerivation c rfl

end SmokeTest

end HSDerivation

end Core.Constraint.OT
