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

* *per Vocabulary Item* ([sande-jenks-2017]; [rolle-2018] Ch 4): the inserted VI's
  R component is the subranking — the `subranking` argument to `cophonologicalEval`;
* *per ph(r)ase* ([sande-jenks-inkelas-2020]): a spell-out phase (vP, CP, DP) carries
  the subranking (`PhrasalCophonology`) and activates it over its whole complement at
  spell-out, deriving cross-word morphologically conditioned effects.

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

Syntactic reference stays indirect: syntax selects which cophonology fires, but the
cophonology itself contains no syntactic vocabulary — [newell-2008]-style cyclic phase
phonology without violating modularity.

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

section Eval

variable [DecidableEq L]

/-! ### Ranking merge -/

/-- Merge a morpheme-specific subranking with the default ranking: the subranking's
constraints first (in the order given), then the default constraints whose labels do
not appear in it — the trigger promotes its constraints without disturbing the
relative order of the rest. -/
def mergeRanking (default sub : List (L × Constraint C)) :
    List (L × Constraint C) :=
  let subLabels := sub.map (·.1)
  sub ++ default.filter (λ c => !subLabels.contains c.1)

/-- An empty subranking produces the default ranking unchanged. -/
theorem mergeRanking_empty_sub (default : List (L × Constraint C)) :
    mergeRanking default [] = default := by
  simp [mergeRanking]

/-! ### Cophonological evaluation -/

variable [DecidableEq C]

/-- Evaluate a candidate set under a cophonology: merge the trigger's subranking with
the default ranking, then take the optimal candidates. The core of CPT — the same
candidate set can yield different winners depending on which subranking is active. A
dominant grammatical-tone trigger, for instance, promotes a basemap-faithfulness
constraint above the default markedness constraints, forcing the output to match the
basemap rather than preserve the target's underlying tones ([rolle-2018] Ch 5). -/
def cophonologicalEval
    (defaultRanking subranking : List (L × Constraint C)) (candidates : List C)
    (h : candidates ≠ [] := by decide) : Finset C :=
  (Tableau.ofRanking candidates ((mergeRanking defaultRanking subranking).map (·.2)) h).optimal

/-- With an empty subranking, cophonological evaluation reduces to standard OT
evaluation: CPT is a proper generalization of OT. -/
theorem cophonologicalEval_empty_sub
    (defaultRanking : List (L × Constraint C)) (candidates : List C) (h : candidates ≠ []) :
    cophonologicalEval defaultRanking [] candidates h
      = (Tableau.ofRanking candidates (defaultRanking.map (·.2)) h).optimal := by
  show (Tableau.ofRanking candidates ((mergeRanking defaultRanking []).map (·.2)) h).optimal = _
  rw [mergeRanking_empty_sub]

end Eval

/-! ### Cophonologies by ph(r)ase -/

/-- A cophonology triggered by spell-out of a particular kind of phase
([sande-jenks-inkelas-2020]): a `Minimalist.Phase.Trigger` whose payload is the
constraint subranking promoted within the matched phase. Per
[sande-clem-dabkowski-2026], the vP phase carries the ATR-harmony cophonology (the
selector matches v heads) and the DP phase the definite-marker phonology (the selector
matches definite D heads). Selection from a registry is `Minimalist.Phase.selectTrigger`
(first-match, the elsewhere ordering). -/
abbrev PhrasalCophonology (L C : Type*) := Minimalist.Phase.Trigger (List (L × Constraint C))

end OptimalityTheory.Cophonology
