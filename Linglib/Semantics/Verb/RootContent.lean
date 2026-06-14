import Linglib.Semantics.Verb.Basic
import Linglib.Morphology.RootTypology

/-!
# Verb ↔ root content accessors

The integration seam (P-HUB) between a `Verb` and the root it carries
(`Verb.root : Option Verb.Root`): a verb's B&KG feature signature, [bhadra-2024]
outcome cardinality, and change-entailment type are read off *its own root* when
present, falling back to its Levin class only for the signature (the per-class
outcome assignment is a Study-level claim, so there is no Levin fallback for
outcomes).

`RootType` and `Verb.Root.changeType` live in `Morphology/RootTypology.lean`, so
these accessors (which mention them) live here rather than in `Verb/Basic.lean`.

## Main definitions

* `Verb.featureSignature` — the verb's entailment-kind signature (root, else Levin)
* `Verb.outcomes` — the verb's outcome-set cardinality (root only)
* `Verb.changeType` — the verb's change-entailment type (derived from its root)
-/

open Verb
open Semantics.Lexical

/-- The verb's B&KG feature signature: from its annotated `root` if present, else
    its Levin class's signature ([levin-1993] fallback, via `rootEntailments`). -/
def Verb.featureSignature (v : Verb) : Option Verb.Root.FeatureSignature :=
  v.root.map (·.featureSignature) <|> v.levinClass.map LevinClass.rootEntailments

/-- The verb's outcome-set cardinality ([bhadra-2024]), read off its `root`. No
    Levin fallback: the per-class outcome assignment is a Study-level claim. -/
def Verb.outcomes (v : Verb) : Option Verb.OutcomeCardinality :=
  v.root.bind (·.outcomes)

/-- The verb's change-entailment type ([beavers-etal-2021]), derived from its
    root's feature signature. -/
def Verb.changeType (v : Verb) : Option RootType :=
  v.root.map Verb.Root.changeType

/-- A verb's `changeType` is blind to its root's outcome axis (it factors through
    `Verb.Root.changeType`): verbs whose roots share entailments share a
    `changeType` whatever their outcomes — the verb-level lift of the root
    orthogonality, and why outcome cardinality is an independent dimension. -/
theorem Verb.changeType_ignores_outcomes {v v' : Verb} {r r' : Verb.Root}
    (hr : v.root = some r) (hr' : v'.root = some r')
    (h : r.entailments = r'.entailments) : v.changeType = v'.changeType := by
  unfold Verb.changeType
  rw [hr, hr']
  exact congrArg some (Verb.Root.changeType_ignores_outcomes h)

/-- The verb's outcome cardinality is exactly its root's, when annotated. -/
@[simp] theorem Verb.outcomes_root {v : Verb} {r : Verb.Root} (hr : v.root = some r) :
    v.outcomes = r.outcomes := by
  unfold Verb.outcomes; rw [hr]; rfl

/-- End-to-end (P-HUB): for any verb, reading its `changeType` off a root and off
    the same-entailment root with a different outcome cardinality agree — only the
    outcome axis distinguishes them. -/
example (v : Verb) :
    ({ v with root := some ⟨"r", ∅, some .multi⟩ }).changeType
      = ({ v with root := some ⟨"r", ∅, some .singleton⟩ }).changeType :=
  Verb.changeType_ignores_outcomes rfl rfl rfl
