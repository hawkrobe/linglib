import Linglib.Semantics.Verb.Basic
import Linglib.Semantics.Verb.Root.Classification

/-!
# Verb ↔ root content accessors

The integration seam (P-HUB) between a `Verb` and the (total) root it carries
(`Verb.root : Verb.Root`): a verb's [bhadra-2024] outcome cardinality and
change-entailment type are read off its own root. The coarse Levin-class view
of the kind signature (`Verb.classKinds`) is kept as a *separate, named*
provenance — the realization label's prediction, not the source of truth
(`Verb.kinds`); the two agree only by theorem, never by construction.

`Verb.Root.ChangeType` lives in `Verb/Root/Classification.lean`; the
`Verb.Root.changeType` projection off a root's kind signature lives here,
alongside the verb-level accessors that read it.

## Main definitions

* `Verb.Root.changeType` — a root's change-entailment type, derived from its
  kind signature (blind to the [bhadra-2024] outcome axis)
* `Verb.classKinds` — the class-derived kind signature (the coarse Levin view)
* `Verb.outcomes` — the verb's outcome-set cardinality
* `Verb.changeType` — the verb's change-entailment type (derived from its root)

## Main results

* `Verb.Root.changeType_ignores_outcomes` — same entailments ⇒ same
  `changeType`, whatever the outcomes
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

/-! ### Root change type, and its blindness to the outcome axis

`ChangeType` is a *projection* of a root's entailment signature, derived not
stored. Crucially it is blind to the [bhadra-2024] outcome axis
(`Root.outcomes`, the orthogonal dimension `Root` carries): two roots with the
same entailments share a `changeType` whatever their outcomes — which is
precisely why outcome cardinality is a genuinely independent dimension of root
content, the one that drives reversative *un-* where the manner/result typology
cannot. -/

/-- The change-entailment type of a root, derived from its kind signature: a
    root entails change iff its signature carries `result` ([beavers-etal-2021]). -/
def Verb.Root.changeType (r : Verb.Root) : Verb.Root.ChangeType :=
  if LexKind.result ∈ r.kinds then .result else .propertyConcept

theorem Verb.Root.changeType_eq_result_iff (r : Verb.Root) :
    r.changeType = .result ↔ r.HasResult := by
  unfold Verb.Root.changeType Verb.Root.HasResult
  by_cases h : LexKind.result ∈ r.kinds <;> simp [h]

/-- `changeType` is blind to outcomes: same entailments ⇒ same `changeType`,
    whatever the `outcomes`. The formal statement of why [bhadra-2024]'s outcome
    cardinality is an independent axis the manner/result signature cannot see. -/
theorem Verb.Root.changeType_ignores_outcomes {r r' : Verb.Root}
    (h : r.entailments = r'.entailments) : r.changeType = r'.changeType := by
  have hsig : r.kinds = r'.kinds := by
    unfold Verb.Root.kinds; rw [h]
  unfold Verb.Root.changeType; rw [hsig]

/-- A *bend*-like and a *break*-like root with the same entailments but different
    outcome cardinality share a `changeType` — only the outcome axis tells them
    apart ([bhadra-2024]). -/
example :
    ({ entailments := {.becomesState "s", .hasCause}, outcomes := some .multi } : Root).changeType
      = ({ entailments := {.becomesState "s", .hasCause}, outcomes := some .singleton } : Root).changeType :=
  Root.changeType_ignores_outcomes rfl

/-- The verb's change-entailment type ([beavers-etal-2021]), derived from its
    root's kind signature. -/
def Verb.changeType (v : Verb) : Verb.Root.ChangeType :=
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
