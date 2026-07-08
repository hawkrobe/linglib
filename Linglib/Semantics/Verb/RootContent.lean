import Linglib.Semantics.Verb.Basic
import Linglib.Morphology.RootTypology

/-!
# Verb ↔ root content accessors

The integration seam (P-HUB) between a `Verb` and the (total) root it carries
(`Verb.root : Verb.Root`): a verb's [bhadra-2024] outcome cardinality and
change-entailment type are read off its own root. The coarse Levin-class view
of the kind signature (`Verb.classKinds`) is kept as a *separate, named*
provenance — the realization label's prediction, not the source of truth
(`Verb.kinds`); the two agree only by theorem, never by construction.

`RootType` and `Verb.Root.changeType` live in `Morphology/RootTypology.lean`, so
these accessors (which mention them) live here rather than in `Verb/Basic.lean`.

## Main definitions

* `Verb.classKinds` — the class-derived kind signature (the coarse Levin view)
* `Verb.outcomes` — the verb's outcome-set cardinality
* `Verb.changeType` — the verb's change-entailment type (derived from its root)

## Main results

* `Verb.classKinds_wellFormed` — the class view, when present, is a well-formed
  signature (grounded in `rootEntailments_wellFormed`)

(`Verb.kinds`, the root-sourced source-of-truth signature, lives in
`Verb/Basic.lean`.)
-/

open Verb
open ArgumentStructure

/-- The kind signature [levin-1993] attributes to the verb *via its class*
    (`LevinClass.rootEntailments`) — the coarse REALIZATION-layer view, distinct
    from the root's own `kinds`. They are independent provenances; a
    `classKinds = kinds` agreement is a theorem, not a default. -/
def Verb.classKinds (v : Verb) : Option Verb.Root.Kinds :=
  v.levinClass.map LevinClass.rootEntailments

/-- The class-derived signature, when present, is well-formed (collocationally
    closed) — `classKinds`'s grounding, inherited from `rootEntailments_wellFormed`.
    The stronger `classKinds ⊆ Verb.kinds` is deliberately *not* a theorem:
    `classKinds` (the Levin label's prediction) and `Verb.kinds` (the verb's own
    root) are independent provenances, so they coincide only for a faithfully
    classified verb — a per-verb hypothesis the type does not enforce. -/
theorem Verb.classKinds_wellFormed (v : Verb) :
    ∀ s ∈ v.classKinds, s.WellFormed := by
  intro s hs
  simp only [Verb.classKinds] at hs
  obtain ⟨c, -, rfl⟩ := Option.mem_map.1 hs
  exact ArgumentStructure.rootEntailments_wellFormed c

/-- The verb's outcome-set cardinality ([bhadra-2024]), read off its `root`
    (`none` where the root is not annotated for outcomes). -/
def Verb.outcomes (v : Verb) : Option Verb.OutcomeCardinality :=
  v.root.outcomes

/-- The verb's change-entailment type ([beavers-etal-2021]), derived from its
    root's kind signature. -/
def Verb.changeType (v : Verb) : RootType :=
  v.root.changeType

/-- A verb's `changeType` is blind to its root's outcome axis (it factors through
    `Verb.Root.changeType`): verbs whose roots share entailments share a
    `changeType` whatever their outcomes — why outcome cardinality is an
    independent dimension. -/
theorem Verb.changeType_ignores_outcomes {v v' : Verb}
    (h : v.root.entailments = v'.root.entailments) : v.changeType = v'.changeType :=
  Verb.Root.changeType_ignores_outcomes h

/-- End-to-end (P-HUB): for any verb, its `changeType` off two same-entailment
    roots that differ only in outcome cardinality agree — only the outcome axis
    distinguishes them. -/
example (v : Verb) :
    ({ v with root := { entailments := ∅, outcomes := some .multi } }).changeType
      = ({ v with root := { entailments := ∅, outcomes := some .singleton } }).changeType :=
  Verb.changeType_ignores_outcomes rfl
