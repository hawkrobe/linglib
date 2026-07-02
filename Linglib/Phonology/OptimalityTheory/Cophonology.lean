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
  individual VI inserted at a terminal — its **R component** specifies the subranking,
  carried here as the `subranking` argument to `cophonologicalEval`. Classic CPT
  ([inkelas-zoll-2007]) attached cophonologies to *constructions*; the VI view sharpens
  the trigger to the inserted exponent.
* **Per ph(r)ase** ([sande-jenks-inkelas-2020]): the trigger is a *spell-out phase*
  (vP, CP, DP) — the cophonology activates over the entire phase complement at
  spell-out (`PhrasalCophonology`), handling **long-distance** morphologically
  conditioned effects (cross-word, within a phase). Syntactic reference stays
  *indirect*: syntax selects which cophonology fires (`selectCophonology`), but the
  cophonology itself is a pure constraint subranking with no syntactic vocabulary —
  [newell-2008]-style cyclic phase phonology in CPT shape, without violating
  modularity.

[sande-clem-dabkowski-2026] ground Guébie discontinuous harmony in the phrasal version
(`Studies/SandeClemDabkowski2026.lean`); per-VI cophonology remains the right substrate
for morpheme-internal effects (`Studies/AkinboFwangwar2026.lean`). The substrate
implements neither bracket erasure ([kiparsky-1982]) nor DM PF discharge
([embick-noyer-2007]) — rival interface theories [sande-clem-dabkowski-2026] §6.2
argues against; it makes the CPT view expressible without forcing it on consumers.
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
