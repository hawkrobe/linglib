import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Syntax.Minimalist.Phase.Basic

/-!
# Cophonology theory

A *cophonology* is a morpheme-specific constraint ranking: in Cophonology Theory
([inkelas-zoll-2007]), individual triggers override parts of the default phonological
grammar, and the surface form is the optimal candidate under the trigger's ranking
rather than the default one. The constraint-merge mechanics are a single apparatus;
what varies across the theory family is the *trigger*:

* *per Vocabulary Item* ([sande-jenks-2017]; [rolle-2018] Ch 4): the trigger is the VI
  inserted at a terminal, whose R component specifies the subranking — carried here as
  the `subranking` argument to `cophonologicalEval`. Classic CPT attached cophonologies
  to constructions; the VI view sharpens the trigger to the inserted exponent.
* *per ph(r)ase* ([sande-jenks-inkelas-2020]): the trigger is a spell-out phase
  (vP, CP, DP), whose cophonology activates over the entire phase complement —
  deriving long-distance morphologically conditioned effects (cross-word, within a
  phase). Syntactic reference stays indirect: syntax selects which cophonology fires,
  but the cophonology itself is a pure constraint subranking with no syntactic
  vocabulary, giving [newell-2008]-style cyclic phase phonology a CPT shape without
  violating modularity.

## Main definitions

* `mergeRanking`: place a subranking's constraints above the default ranking,
  preserving the relative order of the rest.
* `cophonologicalEval`: OT evaluation under the merged ranking. With an empty
  subranking it is standard OT evaluation (`cophonologicalEval_empty_sub`): CPT
  properly generalizes OT.
* `PhrasalCophonology`: the phasal trigger — a phase-head predicate bundled with its
  subranking; `selectCophonology` picks the first match from a registry, the elsewhere
  ordering of [sande-jenks-inkelas-2020].

## Implementation notes

The substrate implements neither bracket erasure ([kiparsky-1982]) nor DM PF discharge
([embick-noyer-2007]) — rival theories of the syntax–phonology interface that
[sande-clem-dabkowski-2026] §6.2 argues against; it makes the CPT view expressible
without forcing it on consumers. Consuming studies: `Studies/AkinboFwangwar2026.lean`
(per-VI, dominant grammatical tone) and `Studies/SandeClemDabkowski2026.lean` (phasal,
Guébie discontinuous harmony).
-/

namespace OptimalityTheory.Cophonology

open Constraints OptimalityTheory
open Minimalist (Phase SyntacticObject)

variable {L C : Type*}

/-! ### Ranking merge -/

/-- Merge a morpheme-specific subranking with the default ranking: the subranking's
constraints first (in the order given), then the default constraints whose labels do
not appear in it — the trigger promotes its constraints without disturbing the
relative order of the rest. -/
def mergeRanking [DecidableEq L] (default sub : List (L × Constraint C)) :
    List (L × Constraint C) :=
  let subLabels := sub.map (·.1)
  sub ++ default.filter (λ c => !subLabels.contains c.1)

/-- An empty subranking produces the default ranking unchanged. -/
theorem mergeRanking_empty_sub [DecidableEq L] (default : List (L × Constraint C)) :
    mergeRanking default [] = default := by
  simp [mergeRanking]

/-! ### Cophonological evaluation -/

/-- Evaluate a candidate set under a cophonology: merge the trigger's subranking with
the default ranking, then take the optimal candidates. The core of CPT — the same
candidate set can yield different winners depending on which subranking is active. A
dominant grammatical-tone trigger, for instance, promotes a basemap-faithfulness
constraint above the default markedness constraints, forcing the output to match the
basemap rather than preserve the target's underlying tones ([rolle-2018] Ch 5). -/
def cophonologicalEval [DecidableEq L] [DecidableEq C]
    (defaultRanking subranking : List (L × Constraint C)) (candidates : List C)
    (h : candidates ≠ [] := by decide) : Finset C :=
  (Tableau.ofRanking candidates ((mergeRanking defaultRanking subranking).map (·.2)) h).optimal

/-- With an empty subranking, cophonological evaluation reduces to standard OT
evaluation: CPT is a proper generalization of OT. -/
theorem cophonologicalEval_empty_sub [DecidableEq L] [DecidableEq C]
    (defaultRanking : List (L × Constraint C)) (candidates : List C) (h : candidates ≠ []) :
    cophonologicalEval defaultRanking [] candidates h
      = (Tableau.ofRanking candidates (defaultRanking.map (·.2)) h).optimal := by
  show (Tableau.ofRanking candidates ((mergeRanking defaultRanking []).map (·.2)) h).optimal = _
  rw [mergeRanking_empty_sub]

/-! ### Cophonologies by ph(r)ase -/

/-- A cophonology triggered by spell-out of a particular kind of phase
([sande-jenks-inkelas-2020]): a phase-head predicate bundled with the constraint
subranking promoted within the matched phase. Per [sande-clem-dabkowski-2026], the vP
phase carries the ATR-harmony cophonology (`phaseSelector` matches v heads) and the DP
phase the definite-marker phonology (`phaseSelector` matches definite D heads). -/
structure PhrasalCophonology (L C : Type*) where
  /-- Predicate selecting which phase heads activate this cophonology. -/
  phaseSelector : SyntacticObject → Bool
  /-- Constraint subranking promoted within the matched phase. -/
  subranking : List (L × Constraint C)

/-- A phrasal cophonology activates on a phase iff its `phaseSelector` matches the
phase head (the head leaf `ph.head`, as a leaf SO). -/
def PhrasalCophonology.appliesTo (pc : PhrasalCophonology L C) (ph : Phase) : Bool :=
  pc.phaseSelector (Minimalist.SO.lexLeaf ph.head)

/-- The *first* registered cophonology whose `phaseSelector` matches the phase head —
first-match encodes lexicographic precedence, the elsewhere ordering of
[sande-jenks-inkelas-2020]. `none` when no cophonology matches; callers then fall back
to the default ranking. -/
def selectCophonology (registry : List (PhrasalCophonology L C)) (ph : Phase) :
    Option (PhrasalCophonology L C) :=
  registry.find? (·.appliesTo ph)

/-- The selected cophonology, when present, applies to the phase. -/
theorem selectCophonology_applies {registry : List (PhrasalCophonology L C)} {ph : Phase}
    {pc : PhrasalCophonology L C} (h : selectCophonology registry ph = some pc) :
    pc.appliesTo ph = true := by
  unfold selectCophonology at h
  simpa using List.find?_some h

end OptimalityTheory.Cophonology
