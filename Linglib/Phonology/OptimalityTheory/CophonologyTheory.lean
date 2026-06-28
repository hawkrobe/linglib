import Linglib.Morphology.DM.VocabularyInsertion
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Basic

/-!
# Cophonology Theory
[inkelas-zoll-2007] [sande-jenks-2017] [rolle-2018]

Cophonology Theory (CPT) proposes that individual morphemes can trigger
morpheme-specific constraint rankings — **cophonologies** — that override
parts of the default phonological grammar. The resulting surface form is
the optimal candidate under the morpheme's cophonology rather than the
default ranking.

## Triggers: VIs, not constructions

In classic CPT ([inkelas-zoll-2007]), cophonologies are properties
of **constructions** (e.g., compounding, reduplication). [sande-jenks-2017]
and [rolle-2018] argue that the trigger should instead be the individual
**Vocabulary Item** inserted at a terminal node: the R component of a VI
specifies a constraint subranking that applies when that VI wins insertion.

This gives DM's Vocabulary Item a four-part structure:
1. **M** — morphosyntactic features (= `contextMatch` in `VocabItem`)
2. **F** — phonological content (= `exponent`)
3. **P** — prosodic subcategorization (not formalized here)
4. **R** — constraint subranking (= `subranking` below)

## Connection to linglib

`CophVocabItem` extends `VocabItem` with an R component. The
`cophonologicalEval` function merges the winning VI's subranking with
the default ranking and runs `Tableau.optimal`, connecting DM
vocabulary insertion (`Morphology.DM.VI`) to OT constraint evaluation
(`Constraint` / `Core.Optimization.Evaluation`).

## Phasal extension: see `CophonologyByPhrase.lean`

[sande-jenks-inkelas-2020] extend the trigger from individual
Vocabulary Items to spell-out *phases* — the cophonology can be
associated with a vP, CP, or DP phase head, activating over the entire
phase complement at spell-out. The substrate for that extension lives
in the sibling file `CophonologyByPhrase.lean`. Consumers handling
long-distance morphologically conditioned phonological effects (cross-
word) — e.g. `Studies/SandeClemDabkowski2026.lean`
— should reach for the phrasal version. Per-VI cophonology (this file)
remains the right substrate for morpheme-internal effects.
-/

namespace OptimalityTheory.CophonologyTheory

open Morphology.DM.VI (VocabItem)
open Constraints OptimalityTheory
open Constraints OptimalityTheory

-- ============================================================================
-- § 1: Cophonological Vocabulary Item
-- ============================================================================

/-- A Vocabulary Item enriched with a morpheme-specific constraint
    subranking (the **R component** of [rolle-2018] Ch 4).

    Extends `VocabItem` with all its fields (exponent, contextMatch,
    rootMatch, specificity) plus:
    - `C`: the candidate type for phonological evaluation
    - `subranking`: constraints promoted above the default ranking

    When this VI wins insertion, its `subranking` overrides the default
    constraint ranking: constraints named in `subranking` are promoted
    to the top of the ranking (in the order listed), and the remaining
    default constraints follow. -/
structure CophVocabItem (Ctx Root C : Type*) extends VocabItem Ctx Root where
  /-- Morpheme-specific constraint subranking (R component).
      Constraints listed here are promoted to the top of the effective
      ranking, overriding their default position. An empty subranking
      means this VI imposes no morpheme-specific phonology. -/
  subranking : List (String × Constraint C) := []

-- ============================================================================
-- § 2: Ranking Merge
-- ============================================================================

/-- Merge a morpheme-specific subranking with the default ranking.

    The effective ranking places the subranking constraints first (in
    the order given), then appends default constraints whose names do
    not appear in the subranking. This implements the intuition that
    the morpheme "promotes" certain constraints above the default
    ranking without disturbing the relative order of other constraints.

    When `sub` is empty, the result is exactly `default`. -/
def mergeRanking {C : Type*}
    (default sub : List (String × Constraint C)) : List (String × Constraint C) :=
  let subNames := sub.map (·.1)
  sub ++ default.filter (λ c => !subNames.contains c.1)

/-- An empty subranking produces the default ranking unchanged. -/
theorem mergeRanking_empty_sub {C : Type*}
    (default : List (String × Constraint C)) :
    mergeRanking default [] = default := by
  simp [mergeRanking]

-- ============================================================================
-- § 3: Cophonological Evaluation
-- ============================================================================

/-- Evaluate a candidate set under a cophonology: merge the winning VI's
    subranking with the default ranking, then return optimal candidates.

    This is the core of CPT: the same candidate set can yield different
    winners depending on which VI's subranking is active. A dominant GT
    trigger, for instance, has a subranking that promotes a faithfulness
    constraint (basemap correspondence) above default markedness
    constraints, forcing the output to match the basemap rather than
    preserving the target's underlying tones ([rolle-2018] Ch 5). -/
def cophonologicalEval {C : Type*} [DecidableEq C]
    (defaultRanking : List (String × Constraint C))
    (subranking : List (String × Constraint C))
    (candidates : List C)
    (h : candidates ≠ [] := by decide) : Finset C :=
  let effective := mergeRanking defaultRanking subranking
  (mkTableau candidates (effective.map (·.2)) h).optimal

/-- When the subranking is empty, cophonological evaluation reduces to
    standard OT evaluation. CPT is a proper generalization of OT. -/
theorem cophonologicalEval_empty_sub {C : Type*} [DecidableEq C]
    (defaultRanking : List (String × Constraint C))
    (candidates : List C) (h : candidates ≠ []) :
    cophonologicalEval defaultRanking [] candidates h =
    (mkTableau candidates (defaultRanking.map (·.2)) h).optimal := by
  show (mkTableau candidates ((mergeRanking defaultRanking []).map (·.2)) h).optimal = _
  rw [mergeRanking_empty_sub]

end OptimalityTheory.CophonologyTheory
