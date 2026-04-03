import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Core.Logic.OT

/-!
# Cophonology Theory
@cite{inkelas-zoll-2007} @cite{sande-jenks-2017} @cite{rolle-2018}

Cophonology Theory (CPT) proposes that individual morphemes can trigger
morpheme-specific constraint rankings — **cophonologies** — that override
parts of the default phonological grammar. The resulting surface form is
the optimal candidate under the morpheme's cophonology rather than the
default ranking.

## Triggers: VIs, not constructions

In classic CPT (@cite{inkelas-zoll-2007}), cophonologies are properties
of **constructions** (e.g., compounding, reduplication). @cite{sande-jenks-2017}
and @cite{rolle-2018} argue that the trigger should instead be the individual
**Vocabulary Item** inserted at a terminal node: the R component of a VI
specifies a constraint subranking that applies when that VI wins insertion.

This gives DM's Vocabulary Item a four-part structure:
1. **M** — morphosyntactic features (= `contextMatch` in `VocabItem`)
2. **F** — phonological content (= `exponent`)
3. **P** — prosodic subcategorization (not formalized here; see `RichExponent`)
4. **R** — constraint subranking (= `subranking` below)

## Connection to linglib

`CophVocabItem` extends `VocabItem` with an R component. The
`cophonologicalEval` function merges the winning VI's subranking with
the default ranking and runs `OTTableau.optimal`, connecting DM
vocabulary insertion (`Morphology.DM.VI`) to OT constraint evaluation
(`Core.OT` / `Core.ConstraintEvaluation`).
-/

namespace Theories.Phonology.CophonologyTheory

open Morphology.DM.VI (VocabItem)
open Core.OT (NamedConstraint buildTableau)
open Core.ConstraintEvaluation (OTTableau)

-- ============================================================================
-- § 1: Cophonological Vocabulary Item
-- ============================================================================

/-- A Vocabulary Item enriched with a morpheme-specific constraint
    subranking (the **R component** of @cite{rolle-2018} Ch 4).

    Extends `VocabItem` with all its fields (exponent, contextMatch,
    rootMatch, specificity) plus:
    - `C`: the candidate type for phonological evaluation
    - `subranking`: constraints promoted above the default ranking

    When this VI wins insertion, its `subranking` overrides the default
    constraint ranking: constraints named in `subranking` are promoted
    to the top of the ranking (in the order listed), and the remaining
    default constraints follow. -/
structure CophVocabItem (Ctx Root C : Type) extends VocabItem Ctx Root where
  /-- Morpheme-specific constraint subranking (R component).
      Constraints listed here are promoted to the top of the effective
      ranking, overriding their default position. An empty subranking
      means this VI imposes no morpheme-specific phonology. -/
  subranking : List (NamedConstraint C) := []

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
def mergeRanking {C : Type}
    (default sub : List (NamedConstraint C)) : List (NamedConstraint C) :=
  let subNames := sub.map (·.name)
  sub ++ default.filter (λ c => !subNames.contains c.name)

/-- An empty subranking produces the default ranking unchanged. -/
theorem mergeRanking_empty_sub {C : Type}
    (default : List (NamedConstraint C)) :
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
    preserving the target's underlying tones (@cite{rolle-2018} Ch 5). -/
def cophonologicalEval {C : Type}
    (defaultRanking : List (NamedConstraint C))
    (subranking : List (NamedConstraint C))
    (candidates : List C)
    (h : candidates ≠ []) : List C :=
  let effective := mergeRanking defaultRanking subranking
  (buildTableau candidates effective h).optimal

/-- When the subranking is empty, cophonological evaluation reduces to
    standard OT evaluation. CPT is a proper generalization of OT. -/
theorem cophonologicalEval_empty_sub {C : Type}
    (defaultRanking : List (NamedConstraint C))
    (candidates : List C) (h : candidates ≠ []) :
    cophonologicalEval defaultRanking [] candidates h =
    (buildTableau candidates defaultRanking h).optimal := by
  simp [cophonologicalEval, mergeRanking_empty_sub]

-- ============================================================================
-- § 4: Dominant vs Non-dominant Cophonology
-- ============================================================================

/-- A dominant cophonology is one whose subranking is non-empty: the VI
    imposes morpheme-specific constraint effects on the phonological
    evaluation.

    In @cite{rolle-2018}'s analysis of grammatical tone, dominant GT
    triggers have a subranking that promotes basemap faithfulness,
    while non-dominant triggers have an empty subranking (relying on
    the default ranking). -/
def CophVocabItem.isDominantCoph {Ctx Root C : Type}
    (cvi : CophVocabItem Ctx Root C) : Bool :=
  !cvi.subranking.isEmpty

/-- A non-dominant cophonology imposes no morpheme-specific constraints:
    the phonological evaluation proceeds under the default ranking. -/
def CophVocabItem.isNonDominantCoph {Ctx Root C : Type}
    (cvi : CophVocabItem Ctx Root C) : Bool :=
  cvi.subranking.isEmpty

/-- Dominant and non-dominant are complementary. -/
theorem coph_dominant_complement {Ctx Root C : Type}
    (cvi : CophVocabItem Ctx Root C) :
    cvi.isDominantCoph = !cvi.isNonDominantCoph := by
  simp [CophVocabItem.isDominantCoph, CophVocabItem.isNonDominantCoph]

end Theories.Phonology.CophonologyTheory
