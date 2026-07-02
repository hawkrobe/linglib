import Linglib.Morphology.DM.VocabularyInsertion
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Syntax.Minimalist.Phase.Basic

/-!
# Cophonology theory
[inkelas-zoll-2007] [sande-jenks-2017] [rolle-2018] [sande-jenks-inkelas-2020]

Cophonology Theory (CPT): individual triggers carry morpheme-specific constraint
rankings — **cophonologies** — that override parts of the default phonological grammar;
the surface form is the optimal candidate under the trigger's cophonology rather than
the default ranking. The constraint-merge mechanics are one apparatus
(`mergeRanking` / `cophonologicalEval`); what varies across the theory family is the
**trigger**:

* **Per Vocabulary Item** ([sande-jenks-2017]; [rolle-2018] Ch 4): the trigger is the
  individual VI inserted at a terminal — its **R component** specifies the subranking
  (`CophVocabItem`, extending DM's `VocabItem` with `subranking`). Classic CPT
  ([inkelas-zoll-2007]) attached cophonologies to *constructions*; the VI view sharpens
  the trigger to the inserted exponent.
* **Per ph(r)ase** ([sande-jenks-inkelas-2020]): the trigger is a *spell-out phase*
  (vP, CP, DP) — the cophonology activates over the entire phase complement at
  spell-out (`PhrasalCophonology`), handling **long-distance** morphologically
  conditioned effects (cross-word, within a phase). Syntactic reference stays
  *indirect*: syntax selects which cophonology fires, but the cophonology itself is a
  pure constraint subranking with no syntactic vocabulary — [newell-2008]-style cyclic
  phase phonology in CPT shape, without violating modularity.

[sande-clem-dabkowski-2026] ground Guébie discontinuous harmony in the phrasal version
(`Studies/SandeClemDabkowski2026.lean`); per-VI cophonology remains the right substrate
for morpheme-internal effects (`Studies/AkinboFwangwar2026.lean`). The substrate
implements neither bracket erasure ([kiparsky-1982]) nor DM PF discharge
([embick-noyer-2007]) — rival interface theories [sande-clem-dabkowski-2026] §6.2
argues against; it makes the CPT view expressible without forcing it on consumers.
-/

namespace OptimalityTheory.Cophonology

open Morphology.DM.VI (VocabItem)
open Constraints OptimalityTheory
open Minimalist (Phase SyntacticObject)
/-! ### Cophonological Vocabulary Item -/

/-- A Vocabulary Item enriched with a morpheme-specific constraint
    subranking (the **R component** of [rolle-2018] Ch 4).

    Extends `VocabItem` with all its fields (exponent, contextMatch,
    rootMatch, specificity) plus:
    - `C`: the candidate type for phonological evaluation
    - `subranking`: constraints promoted above the default ranking

    When this VI wins insertion, its `subranking` overrides the default
    constraint ranking: constraints labeled in `subranking` are promoted
    to the top of the ranking (in the order listed), and the remaining
    default constraints follow. -/
structure CophVocabItem (Ctx Root L C : Type*) extends VocabItem Ctx Root where
  /-- Morpheme-specific constraint subranking (R component).
      Constraints listed here are promoted to the top of the effective
      ranking, overriding their default position. An empty subranking
      means this VI imposes no morpheme-specific phonology. -/
  subranking : List (L × Constraint C) := []

/-! ### Ranking Merge -/

/-- Merge a morpheme-specific subranking with the default ranking.

    The effective ranking places the subranking constraints first (in
    the order given), then appends default constraints whose labels do
    not appear in the subranking. This implements the intuition that
    the morpheme "promotes" certain constraints above the default
    ranking without disturbing the relative order of other constraints.

    When `sub` is empty, the result is exactly `default`. -/
def mergeRanking {L C : Type*} [DecidableEq L]
    (default sub : List (L × Constraint C)) : List (L × Constraint C) :=
  let subLabels := sub.map (·.1)
  sub ++ default.filter (λ c => !subLabels.contains c.1)

/-- An empty subranking produces the default ranking unchanged. -/
theorem mergeRanking_empty_sub {L C : Type*} [DecidableEq L]
    (default : List (L × Constraint C)) :
    mergeRanking default [] = default := by
  simp [mergeRanking]

/-! ### Cophonological Evaluation -/

/-- Evaluate a candidate set under a cophonology: merge the winning VI's
    subranking with the default ranking, then return optimal candidates.

    This is the core of CPT: the same candidate set can yield different
    winners depending on which VI's subranking is active. A dominant GT
    trigger, for instance, has a subranking that promotes a faithfulness
    constraint (basemap correspondence) above default markedness
    constraints, forcing the output to match the basemap rather than
    preserving the target's underlying tones ([rolle-2018] Ch 5). -/
def cophonologicalEval {L C : Type*} [DecidableEq L] [DecidableEq C]
    (defaultRanking : List (L × Constraint C))
    (subranking : List (L × Constraint C))
    (candidates : List C)
    (h : candidates ≠ [] := by decide) : Finset C :=
  let effective := mergeRanking defaultRanking subranking
  (Tableau.ofRanking candidates (effective.map (·.2)) h).optimal

/-- When the subranking is empty, cophonological evaluation reduces to
    standard OT evaluation. CPT is a proper generalization of OT. -/
theorem cophonologicalEval_empty_sub {L C : Type*} [DecidableEq L] [DecidableEq C]
    (defaultRanking : List (L × Constraint C))
    (candidates : List C) (h : candidates ≠ []) :
    cophonologicalEval defaultRanking [] candidates h =
    (Tableau.ofRanking candidates (defaultRanking.map (·.2)) h).optimal := by
  show (Tableau.ofRanking candidates ((mergeRanking defaultRanking []).map (·.2)) h).optimal = _
  rw [mergeRanking_empty_sub]

/-! ### Phrasal Cophonology -/

/-- A cophonology triggered by spell-out of a particular kind of phase
    ([sande-jenks-inkelas-2020]). Bundles a phase-head predicate
    with a constraint subranking promoted within the matched phase.

    Examples (per [sande-clem-dabkowski-2026]):
    - vP phase carries the ATR-harmony cophonology — `phaseSelector`
      matches v heads, `subranking` lists ATRHARM ≫ IDENT-IO(ATR).
    - DP phase carries definite-marker phonology — `phaseSelector`
      matches D heads of definite category. -/
structure PhrasalCophonology (L C : Type*) where
  /-- Predicate selecting which phase heads activate this cophonology. -/
  phaseSelector : SyntacticObject → Bool
  /-- Constraint subranking promoted within the matched phase. -/
  subranking    : List (L × Constraint C)

/-- A phrasal cophonology activates on a phase iff its `phaseSelector`
    matches the phase head (the head leaf `ph.head`, as a leaf SO). -/
def PhrasalCophonology.appliesTo {L C : Type*}
    (pc : PhrasalCophonology L C) (ph : Phase) : Bool :=
  pc.phaseSelector (Minimalist.SO.lexLeaf ph.head)

/-! ### Phrasal Cophonological Evaluation -/

/-- Run a matched phrasal cophonology on a candidate set: merge its
    subranking with the default ranking, return optimal candidates.

    Delegates to `cophonologicalEval` from the per-VI sections above;
    the difference relative to per-VI cophonology is the *trigger*
    (phase head match), not the constraint-merge mechanics. -/
def phrasalCophonologicalEval {L C : Type*} [DecidableEq L] [DecidableEq C]
    (defaultRanking : List (L × Constraint C))
    (pc : PhrasalCophonology L C)
    (candidates : List C)
    (h : candidates ≠ []) : Finset C :=
  cophonologicalEval defaultRanking pc.subranking candidates h

/-- A phrasal cophonology with empty subranking reduces to default OT.
    Lifts `cophonologicalEval_empty_sub`. -/
theorem phrasalCophonologicalEval_empty_sub {L C : Type*} [DecidableEq L] [DecidableEq C]
    (defaultRanking : List (L × Constraint C))
    (pc : PhrasalCophonology L C)
    (candidates : List C) (h : candidates ≠ [])
    (hsub : pc.subranking = []) :
    phrasalCophonologicalEval defaultRanking pc candidates h
      = (OptimalityTheory.Tableau.ofRanking candidates (defaultRanking.map (·.2)) h).optimal := by
  unfold phrasalCophonologicalEval
  rw [hsub]
  exact cophonologicalEval_empty_sub defaultRanking candidates h

/-! ### Phase-Bounded Cophonology Selection -/

/-- Given a list of registered phrasal cophonologies and a specific
    phase, return the *first* cophonology whose `phaseSelector` matches
    the phase head. The "first" convention encodes lexicographic
    precedence — earlier-listed cophonologies win, mimicking the
    English-style elsewhere ordering of [sande-jenks-inkelas-2020].

    Returns `none` if no registered cophonology matches; in that case
    callers should fall back to the default ranking. -/
def selectCophonology {L C : Type*}
    (registry : List (PhrasalCophonology L C)) (ph : Phase)
    : Option (PhrasalCophonology L C) :=
  registry.find? (·.appliesTo ph)

/-- The selected cophonology, when present, applies to the phase. -/
theorem selectCophonology_applies {L C : Type*}
    {registry : List (PhrasalCophonology L C)} {ph : Phase}
    {pc : PhrasalCophonology L C}
    (h : selectCophonology registry ph = some pc) :
    pc.appliesTo ph = true := by
  unfold selectCophonology at h
  have := List.find?_some h
  simpa using this

/-! ### Phrasal Cophonology with Empty Registry -/

/-- An empty registry selects no cophonology. -/
theorem selectCophonology_empty {L C : Type*} (ph : Phase) :
    selectCophonology ([] : List (PhrasalCophonology L C)) ph = none := rfl

end OptimalityTheory.Cophonology
