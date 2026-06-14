import Linglib.Semantics.Verb.Basic
import Linglib.Morphology.RootTypology

/-!
# Verb ↔ root content accessors

The integration seam (P-HUB) between a `Verb` and the root it carries
(`Verb.root : Option Verb.Root`): a verb's B&KG kind signature, [bhadra-2024]
outcome cardinality, and change-entailment type are read off *its own root* when
present, falling back to its Levin class only for the signature (the per-class
outcome assignment is a Study-level claim, so there is no Levin fallback for
outcomes).

`RootType` and `Verb.Root.changeType` live in `Morphology/RootTypology.lean`, so
these accessors (which mention them) live here rather than in `Verb/Basic.lean`.

## Main definitions

* `Verb.classKinds` — the class-derived kind signature (the coarse Levin view)
* `Verb.outcomes` — the verb's outcome-set cardinality (root only)
* `Verb.changeType` — the verb's change-entailment type (derived from its root)

(`Verb.kinds`, the root-sourced signature, lives in `Verb/Basic.lean`.)
-/

open Verb
open Semantics.Lexical

/-- The kind signature [levin-1993] attributes to the verb *via its class*
    (`LevinClass.rootEntailments`) — the coarse REALIZATION-layer view, distinct
    from the root's own `kinds`. They are independent provenances; a
    `classKinds = kinds` agreement is a theorem, not a default. -/
def Verb.classKinds (v : Verb) : Option Verb.Root.Kinds :=
  v.levinClass.map LevinClass.rootEntailments

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
