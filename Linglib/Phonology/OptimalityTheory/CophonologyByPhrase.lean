import Linglib.Phonology.OptimalityTheory.CophonologyTheory
import Linglib.Syntax.Minimalist.Phase.Basic

/-!
# Cophonologies by Ph(r)ase
[sande-jenks-inkelas-2020]

[sande-jenks-2017] (formalized in `CophonologyTheory.lean`)
proposed that the cophonology trigger is the individual **Vocabulary
Item** inserted at a terminal node — the **R** component of a VI lists
constraints promoted above the default ranking when that VI wins
insertion.

[sande-jenks-inkelas-2020] extends this to handle **long-distance
morphologically conditioned phonological effects** — phonological
processes in one word affected by morphemes in another word, within
the same syntactic phase. Two architectural moves:

1. **Phasal triggers**: cophonologies can be associated with
   *cyclically generated syntactic units* (phases — vP, CP, DP), not
   just individual VIs. The cophonology activates over the entire
   phase complement when that phase is spelled out, rewriting the
   constraint ranking for the duration of the phase-internal
   phonological evaluation.

2. **Indirect syntactic reference**: phonology never directly mentions
   syntactic structure. The cophonology mechanism is the indirect
   pathway: syntax determines which cophonology fires (via the phase
   selector), but the cophonology itself is a pure constraint
   subranking with no syntactic vocabulary.

This gives [newell-2008]-style cyclic phase phonology a CPT shape
without violating the modularity assumption that phonology operates on
phonological strings, not on syntactic trees.

## Why this substrate is needed

[sande-clem-dabkowski-2026] ground their analysis of Guébie
discontinuous harmony in this framework: the vP phase carries the
ATR-harmony cophonology (the *ATRHARM(ONY)* constraint, formulated
under [hansson-2014]'s Agreement-by-Projection), so that when V
and the particle are both spelled out within vP, harmony applies; in
SVO clauses where V has moved out of vP to T, only the particle is
in the vP-spell-out and harmony does not apply. The substrate change
relative to `CophonologyTheory.lean` is the trigger type — phase head
predicate vs. individual Vocabulary Item.

## Design

`PhrasalCophonology` is the analogue of `CophVocabItem` for phases:
both bundle a "what activates this cophonology?" predicate with a
constraint subranking. The activation predicate is just a
`SyntacticObject → Bool` so it can match phases by category, by
specifier content, by feature, or by anything else the analyst can
decide. `phrasalCophonologicalEval` delegates to
`OptimalityTheory.CophonologyTheory.cophonologicalEval` once the matched
cophonology has been selected — there is no parallel ranking-merge
machinery, just a different trigger.

## What this substrate does NOT do

It does not implement bracket erasure (Lexical Phonology /
[kiparsky-1982]) nor PF discharge / rewrite (Distributed
Morphology / [harley-noyer-1999], [embick-noyer-2007]). Both
are competing theories of the syntax-phonology interface;
[sande-clem-dabkowski-2026] §6.2 explicitly argues against them.
The substrate's neutral position is to make the SBJ 2020 / SCD 2026
view expressible without forcing it on consumers.
-/

namespace OptimalityTheory.CophonologyByPhrase

open OptimalityTheory.CophonologyTheory (cophonologicalEval mergeRanking
  mergeRanking_empty_sub cophonologicalEval_empty_sub)
open Constraint OptimalityTheory
open Minimalist (Phase SyntacticObject)

-- ============================================================================
-- § 1: Phrasal Cophonology
-- ============================================================================

/-- A cophonology triggered by spell-out of a particular kind of phase
    ([sande-jenks-inkelas-2020]). Bundles a phase-head predicate
    with a constraint subranking promoted within the matched phase.

    Examples (per [sande-clem-dabkowski-2026]):
    - vP phase carries the ATR-harmony cophonology — `phaseSelector`
      matches v heads, `subranking` lists ATRHARM ≫ IDENT-IO(ATR).
    - DP phase carries definite-marker phonology — `phaseSelector`
      matches D heads of definite category. -/
structure PhrasalCophonology (C : Type) where
  /-- Predicate selecting which phase heads activate this cophonology. -/
  phaseSelector : SyntacticObject → Bool
  /-- Constraint subranking promoted within the matched phase. -/
  subranking    : List (NamedConstraint C)
  /-- Optional human-readable name for diagnostics. -/
  name          : String := ""

/-- A phrasal cophonology activates on a phase iff its `phaseSelector`
    matches the phase head (the head leaf `ph.head`, as a leaf SO). -/
def PhrasalCophonology.appliesTo {C : Type}
    (pc : PhrasalCophonology C) (ph : Phase) : Bool :=
  pc.phaseSelector (Minimalist.SO.lexLeaf ph.head)

-- ============================================================================
-- § 2: Phrasal Cophonological Evaluation
-- ============================================================================

/-- Run a matched phrasal cophonology on a candidate set: merge its
    subranking with the default ranking, return optimal candidates.

    Delegates to `cophonologicalEval` from `CophonologyTheory.lean`;
    the difference relative to per-VI cophonology is the *trigger*
    (phase head match), not the constraint-merge mechanics. -/
def phrasalCophonologicalEval {C : Type} [DecidableEq C]
    (defaultRanking : List (NamedConstraint C))
    (pc : PhrasalCophonology C)
    (candidates : List C)
    (h : candidates ≠ []) : Finset C :=
  cophonologicalEval defaultRanking pc.subranking candidates h

/-- A phrasal cophonology with empty subranking reduces to default OT.
    Lifts `cophonologicalEval_empty_sub`. -/
theorem phrasalCophonologicalEval_empty_sub {C : Type} [DecidableEq C]
    (defaultRanking : List (NamedConstraint C))
    (pc : PhrasalCophonology C)
    (candidates : List C) (h : candidates ≠ [])
    (hsub : pc.subranking = []) :
    phrasalCophonologicalEval defaultRanking pc candidates h
      = (OptimalityTheory.mkTableau candidates defaultRanking h).optimal := by
  unfold phrasalCophonologicalEval
  rw [hsub]
  exact cophonologicalEval_empty_sub defaultRanking candidates h

-- ============================================================================
-- § 3: Phase-Bounded Cophonology Selection
-- ============================================================================

/-- Given a list of registered phrasal cophonologies and a specific
    phase, return the *first* cophonology whose `phaseSelector` matches
    the phase head. The "first" convention encodes lexicographic
    precedence — earlier-listed cophonologies win, mimicking the
    English-style elsewhere ordering of [sande-jenks-inkelas-2020].

    Returns `none` if no registered cophonology matches; in that case
    callers should fall back to the default ranking. -/
def selectCophonology {C : Type}
    (registry : List (PhrasalCophonology C)) (ph : Phase)
    : Option (PhrasalCophonology C) :=
  registry.find? (·.appliesTo ph)

/-- The selected cophonology, when present, applies to the phase. -/
theorem selectCophonology_applies {C : Type}
    {registry : List (PhrasalCophonology C)} {ph : Phase}
    {pc : PhrasalCophonology C}
    (h : selectCophonology registry ph = some pc) :
    pc.appliesTo ph = true := by
  unfold selectCophonology at h
  have := List.find?_some h
  simpa using this

-- ============================================================================
-- § 4: Phrasal Cophonology with Empty Registry
-- ============================================================================

/-- An empty registry selects no cophonology. -/
theorem selectCophonology_empty {C : Type} (ph : Phase) :
    selectCophonology ([] : List (PhrasalCophonology C)) ph = none := rfl

end OptimalityTheory.CophonologyByPhrase
