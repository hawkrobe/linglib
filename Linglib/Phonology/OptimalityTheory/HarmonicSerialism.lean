import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.Constraints.Profile
import Linglib.Phonology.OptimalityTheory.Defs
import Linglib.Phonology.OptimalityTheory.DirectionalTableau
import Mathlib.Data.Finset.Union

/-!
# Harmonic Serialism — The Combinator
[mccarthy-2000] [mccarthy-2010] [pruitt-2023]
[lamont-2022a] [lamont-2022b]

Bundles a one-step `gen` function and a constraint ranking into an
`HSDerivation`. Owns the serial GEN/EVAL iteration combinator (§ 1 — a
bespoke fuel-bounded search; the generic fixed-point / well-founded-
termination theory it instantiates is mathlib's) and reuses the existing
parallel `Tableau`/`mkTableau` machinery from `Basic.lean` (Layered
Grounding — does not duplicate parallel optimization).

## NOTE on theoretical scope

Per [pruitt-2023] (Table 1): HS does **not** solve counterfeeding
underapplication, and only patches counterbleeding overapplication with
extra GEN assumptions. This file's docstring deliberately does not claim
HS is "the serial OT solution to opacity" — that would misrepresent the
field's current understanding. HS is one constraint-based serial framework
with mixed empirical record; [mcpherson-lamont-2026] is the
motivating positive case for the directional variant of HS
([lamont-2022b]). For counterfeeding cases linglib offers
`Phonology/Subregular/LocalRewrite.lean` (extrinsic ordering of
local rewrite rules; subregular-grounded per [chandlee-heinz-2018])
and `Phonology/OptimalityTheory/Stratal.lean` (cyclic ranking)
as architecturally-distinct alternatives.

## Sibling architectures

OT has multiple "more than one EVAL call" specializations, all sharing
the parallel-OT primitives in `Basic.lean`:

| Theory                        | Ranking across calls | Candidate across calls |
|-------------------------------|----------------------|------------------------|
| Parallel OT (`Basic.lean`)    | n/a (single call)    | n/a                    |
| Stratal OT (`Stratal.lean`) | varies per stratum   | chained via `bridge`   |
| HS (this file)                | **durable**          | iterated via `gen`     |
| Stratal HS (not yet)          | varies per stratum   | iterated within stratum |

HS and Stratal OT are **sister specializations**, not nested: HS holds
ranking constant and varies the candidate; Stratal OT varies the ranking
and chains the candidate. Stratal HS combines both axes and is
deferred (cf. [pruitt-2023] §2.4).

## Sibling, not refactor

This module does **not** modify `NamedConstraint` or `Tableau`
(load-bearing for `Weighted.lean`/`MaxEnt.lean`/`NoisyHG.lean` and ~30
study files). The `stepOptimum` function builds an inner `Tableau` and
reuses `Tableau.optimal` directly. Future directional dispatch
([lamont-2022b]; [eisner-2000]) will land as a sibling
`DirectionalTableau` consumer; deliberately not stubbed here, to avoid
silently routing directional callers to the parallel optimum.
-/

namespace OptimalityTheory
open Constraints


open Core.Optimization.Evaluation

-- ============================================================================
-- § 1: Serial GEN/EVAL Iteration Combinator
-- ============================================================================

/-! The bespoke part of Harmonic Serialism, which mathlib has no off-the-shelf
form of: a fuel-bounded search that iterates `eval ∘ gen` to a fixed point,
picking a representative of the optimal set at each step. The *general* theory
it instantiates is mathlib's — `Function.IsFixedPt`, `Order.FixedPoints`
(Knaster–Tarski), `WellFounded` descent; the `Nat` fuel and `pick` selector
here are what make a possibly-non-terminating, possibly-tied search total and
computable. -/

section Iteration

variable {C : Type*}

/-- One step of an HS derivation: `gen` produces the candidate set, `eval`
    selects the (possibly non-singleton) optimal subset. -/
def iterateStep (gen : C → Finset C) (eval : Finset C → Finset C) (c : C) : Finset C :=
  eval (gen c)

/-- Iterate `iterateStep` for at most `n` rounds, stopping early at HS
    convergence (`eval (gen c) = {c}`). Otherwise advance by `pick`ing some
    element of the optimal set (a canonical sort + `head?`, or a directional
    tie-breaker). Returns `none` if `pick` fails or the optimal set is empty
    along the way. The `Nat` bound makes the function total — HS need not
    converge ([lamont-2022b]). -/
def iterateGen [DecidableEq C] (gen : C → Finset C)
    (eval : Finset C → Finset C) (pick : Finset C → Option C) : C → Nat → Option C
  | c, 0     => some c
  | c, n + 1 =>
    let optima := iterateStep gen eval c
    if optima = ({c} : Finset C) then some c
    else
      match pick optima with
      | none    => none
      | some c' => iterateGen gen eval pick c' n

/-- Zero iterations is identity. -/
@[simp] theorem iterateGen_zero [DecidableEq C] (gen : C → Finset C)
    (eval : Finset C → Finset C) (pick : Finset C → Option C) (c : C) :
    iterateGen gen eval pick c 0 = some c := rfl

/-- One iteration from a converged form returns it unchanged. -/
theorem iterateGen_succ_of_converged [DecidableEq C] {gen : C → Finset C}
    {eval : Finset C → Finset C} (pick : Finset C → Option C) {c : C}
    (h : iterateStep gen eval c = ({c} : Finset C)) (n : Nat) :
    iterateGen gen eval pick c (n + 1) = some c := by
  unfold iterateGen; simp [h]

/-- One iteration from a non-converged form recurses with the picked
    successor at the smaller depth. -/
theorem iterateGen_succ_of_step [DecidableEq C] {gen : C → Finset C}
    {eval : Finset C → Finset C} {pick : Finset C → Option C} {c c' : C}
    (n : Nat) (hcv : iterateStep gen eval c ≠ ({c} : Finset C))
    (hpick : pick (iterateStep gen eval c) = some c') :
    iterateGen gen eval pick c (n + 1) = iterateGen gen eval pick c' n := by
  show (if iterateStep gen eval c = ({c} : Finset C) then some c
        else match pick (iterateStep gen eval c) with
             | none => none
             | some c' => iterateGen gen eval pick c' n)
       = iterateGen gen eval pick c' n
  rw [if_neg hcv, hpick]

/-- One iteration from a non-converged form where `pick` fails yields `none`. -/
theorem iterateGen_succ_of_pickFail [DecidableEq C] {gen : C → Finset C}
    {eval : Finset C → Finset C} {pick : Finset C → Option C} {c : C}
    (n : Nat) (hcv : iterateStep gen eval c ≠ ({c} : Finset C))
    (hpick : pick (iterateStep gen eval c) = none) :
    iterateGen gen eval pick c (n + 1) = none := by
  show (if iterateStep gen eval c = ({c} : Finset C) then some c
        else match pick (iterateStep gen eval c) with
             | none => none
             | some c' => iterateGen gen eval pick c' n)
       = none
  rw [if_neg hcv, hpick]

/-- Once at a fixed point, further iterations stay there — convergence is
    durable. The hypothesis is equivalent to `Function.IsFixedPt` of the
    powerset step at `{c}`. -/
theorem iterateGen_idempotent_at_fixedPoint [DecidableEq C]
    (gen : C → Finset C) (eval : Finset C → Finset C)
    (pick : Finset C → Option C) (c : C)
    (h : iterateStep gen eval c = ({c} : Finset C)) :
    ∀ n, iterateGen gen eval pick c n = some c
  | 0     => rfl
  | n + 1 => iterateGen_succ_of_converged (gen := gen) (eval := eval) pick h n

/-- **Harmonic improvement.** At each non-fixed-point step every newly chosen
    candidate is strictly better than the input under the supplied harmony
    order `lt`. The order is a parameter so this stays agnostic about the
    EVAL term order; soundness (`sound`) is witnessed by the caller. -/
theorem harmonicImprovement [DecidableEq C] (lt : C → C → Prop)
    (gen : C → Finset C) (eval : Finset C → Finset C)
    (sound : ∀ c c', c' ∈ eval (gen c) → c' ≠ c → lt c' c)
    (c c' : C) (hopt : c' ∈ iterateStep gen eval c) (hne : c' ≠ c) :
    lt c' c :=
  sound c c' hopt hne

/-- **HS terminates under a well-founded harmony order.** If `lt` is
    well-founded and every genuine step produces a strictly more harmonic
    candidate (`sound`), then `iterateGen` is **eventually constant**: some `N`
    past which further iterations don't change the result. This is the
    structural justification for HS as a search — derivations can't loop while
    each step makes measurable progress, so the explicit `Nat` bound is
    harmless. -/
theorem iterateGen_eventually_constant [DecidableEq C]
    (gen : C → Finset C) (eval : Finset C → Finset C)
    (pick : Finset C → Option C) {lt : C → C → Prop} (wf : WellFounded lt)
    (sound : ∀ c c', iterateStep gen eval c ≠ ({c} : Finset C) →
                     pick (iterateStep gen eval c) = some c' → c' ≠ c → lt c' c)
    (c : C) :
    ∃ N, ∀ m, N ≤ m → iterateGen gen eval pick c m = iterateGen gen eval pick c N := by
  induction c using wf.induction with
  | _ c IH =>
    by_cases hcv : iterateStep gen eval c = ({c} : Finset C)
    · refine ⟨0, fun m _ => ?_⟩
      rw [iterateGen_idempotent_at_fixedPoint gen eval pick c hcv m,
          iterateGen_idempotent_at_fixedPoint gen eval pick c hcv 0]
    · cases hp : pick (iterateStep gen eval c) with
      | none =>
        refine ⟨1, fun m hm => ?_⟩
        match m, hm with
        | 0, hm => omega
        | n + 1, _ =>
          rw [iterateGen_succ_of_pickFail _ hcv hp,
              iterateGen_succ_of_pickFail 0 hcv hp]
      | some c' =>
        by_cases hne : c' = c
        · have hp' : pick (iterateStep gen eval c) = some c := hne ▸ hp
          refine ⟨0, fun m _ => ?_⟩
          have h : ∀ m, iterateGen gen eval pick c m = some c := by
            intro m
            induction m with
            | zero => rfl
            | succ _ ih => rw [iterateGen_succ_of_step _ hcv hp']; exact ih
          rw [h m, h 0]
        · have hlt : lt c' c := sound c c' hcv hp hne
          obtain ⟨N', IH'⟩ := IH c' hlt
          refine ⟨N' + 1, fun m hm => ?_⟩
          match m, hm with
          | 0, hm => omega
          | n + 1, hn =>
            have hn' : N' ≤ n := Nat.le_of_succ_le_succ hn
            rw [iterateGen_succ_of_step _ hcv hp,
                iterateGen_succ_of_step _ hcv hp,
                IH' n hn']

end Iteration

-- ============================================================================
-- § 2: HSDerivation Specification
-- ============================================================================

/-- A Harmonic Serialism derivation specification.

    `gen` is the one-step candidate-generation function (per
    [mccarthy-2008b]'s restricted GEN). `ranking` is a list of
    named constraints, indexed by rank position (head = highest). The
    inner `Tableau` width is inferred from `ranking.length`; no separate
    length parameter is exposed. -/
structure HSDerivation (C : Type*) [DecidableEq C] where
  gen : C → Finset C
  ranking : List (NamedConstraint C)

namespace HSDerivation

variable {C : Type*} [DecidableEq C]

-- ============================================================================
-- § 3: Inner Tableau and Optimal Set
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
    `iterateGen`. -/
def evalFilter (D : HSDerivation C) (cands : Finset C) : Finset C :=
  if h : cands.Nonempty then (D.tableauFor cands h).optimal else ∅

/-- Optimal set for one HS step: `evalFilter` applied to `gen c`.
    Equivalently, `iterateStep D.gen D.evalFilter c`. -/
def stepOptimum (D : HSDerivation C) (c : C) : Finset C :=
  D.evalFilter (D.gen c)

@[simp] theorem stepOptimum_eq_iterateStep (D : HSDerivation C) (c : C) :
    D.stepOptimum c = iterateStep D.gen D.evalFilter c := rfl

/-- An empty `gen` output yields an empty optimal set. -/
@[simp] theorem stepOptimum_of_empty_gen (D : HSDerivation C) (c : C)
    (h : D.gen c = ∅) : D.stepOptimum c = ∅ := by
  simp [stepOptimum, evalFilter, h]

-- ============================================================================
-- § 4: Convergence
-- ============================================================================

/-- A form `c` has **converged** under `D` iff its optimal set is the
    singleton `{c}` — the faithful candidate is the unique optimum. This
    is the canonical HS halting condition ([mccarthy-2010]).

    Equivalent to `Function.IsFixedPt` of the powerset step at `{c}`
    (`isFixedPt_singleton_iff_converged`). -/
def Converged (D : HSDerivation C) (c : C) : Prop :=
  D.stepOptimum c = ({c} : Finset C)

instance (D : HSDerivation C) (c : C) : Decidable (D.Converged c) :=
  decEq (D.stepOptimum c) ({c} : Finset C)

/-- `Converged` is exactly mathlib's `Function.IsFixedPt` of the powerset step
    `s ↦ ⋃_{x ∈ s} evalFilter (gen x)` at the singleton `{c}` — by
    `Finset.singleton_biUnion`, with no intermediate combinator. Registered as
    a simp lemma in the `IsFixedPt → Converged` direction (complex → simpler). -/
@[simp] theorem isFixedPt_singleton_iff_converged (D : HSDerivation C) (c : C) :
    Function.IsFixedPt (fun s => s.biUnion fun x => D.evalFilter (D.gen x))
      ({c} : Finset C) ↔ D.Converged c := by
  simp [Converged, stepOptimum, Function.IsFixedPt, Finset.singleton_biUnion]

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
  simp only [LexMinProblem.lexMins, argMinSet, tableauFor, Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, ?_⟩⟩
  intro c' hc'; subst hc'; subst hx; rfl

-- ============================================================================
-- § 5: Smart Constructor for n-Step Derivation
-- ============================================================================

/-- n-step HS derivation. Wraps `iterateGen` with `D.gen` and
    `D.stepOptimum`. The caller supplies a `pick : Finset C → Option C`
    tie-breaker used when the optimal set isn't a singleton (which would
    indicate either (a) ties not yet broken by directional eval, or (b)
    a divergent tie in the [pruitt-2009] sense). Returns `none` if
    `pick` ever fails. HS derivations are not in general guaranteed to
    converge — see [lamont-2022b] for non-terminating cases. -/
def derive (D : HSDerivation C) (pick : Finset C → Option C) (c : C)
    (steps : Nat) : Option C :=
  iterateGen D.gen D.evalFilter pick c steps

end HSDerivation

namespace HSDerivation

variable {C : Type*} [DecidableEq C]

-- ============================================================================
-- § 6: Smoke Test
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

-- ============================================================================
-- § 7: Directional Harmonic Serialism
-- ============================================================================

/-! Directional HS ([lamont-2022b]): the constraint hierarchy is a list of
    `Constraint C`, each carrying its own `TermOrder` (counting constraints
    `.degree`, `*FLOAT^→` `.lex`, `*FLOAT^←` `.revLex`), evaluated via
    `DirectionalTableau`. Sibling to the parallel `HSDerivation` above; the two
    are not unified because their constraint types differ (`NamedConstraint C`
    carries a scalar `eval` for weighted aggregation; `Constraint C` carries a
    vector + term order, with which weighting is incoherent per Lamont 2022b).

    The motivating consumer is paper, fig. 3 (`/kāk^H + rī^H + dō^H/`):
    parallel HS produces a divergent tie among three deletion candidates;
    directional `*FLOAT^→` breaks the tie by requiring leftmost-first
    deletion. -/

structure DirectionalHSDerivation (C : Type*) [DecidableEq C] where
  gen : C → Finset C
  ranking : List (Constraint C)

namespace DirectionalHSDerivation

variable {C : Type*} [DecidableEq C]

/-- Build a `DirectionalTableau` from an explicit candidate set. -/
def tableauFor (D : DirectionalHSDerivation C) (cands : Finset C)
    (h : cands.Nonempty) : DirectionalTableau C :=
  { candidates := cands
    ranking := D.ranking
    nonempty := h }

/-- Filter a candidate set to its optimal subset under `D.ranking`. Routes
    through `DirectionalTableau.optima` (Layered Grounding). Returns `∅` on
    empty input. -/
def evalFilter (D : DirectionalHSDerivation C) (cands : Finset C) : Finset C :=
  if h : cands.Nonempty then (D.tableauFor cands h).optima else ∅

/-- Optimal set for one HS step under directional EVAL. -/
def stepOptimum (D : DirectionalHSDerivation C) (c : C) : Finset C :=
  D.evalFilter (D.gen c)

/-- A form `c` has **converged** under `D` iff its optimal set under
    directional EVAL is `{c}`. -/
def Converged (D : DirectionalHSDerivation C) (c : C) : Prop :=
  D.stepOptimum c = ({c} : Finset C)

instance (D : DirectionalHSDerivation C) (c : C) : Decidable (D.Converged c) :=
  decEq (D.stepOptimum c) ({c} : Finset C)

/-- N-step directional HS derivation. Wraps `iterateGen` with `D.gen`
    and `D.evalFilter`. The caller supplies a `pick : Finset C → Option C`
    tie-breaker; under directional EVAL ties should be rare or absent
    (that's the whole point of using directional), but `pick` is still
    needed for the fallback path — e.g. the order-minimal element when
    `C` carries a `LinearOrder`. -/
def derive (D : DirectionalHSDerivation C) (pick : Finset C → Option C)
    (c : C) (steps : Nat) : Option C :=
  iterateGen D.gen D.evalFilter pick c steps

end DirectionalHSDerivation

end OptimalityTheory
