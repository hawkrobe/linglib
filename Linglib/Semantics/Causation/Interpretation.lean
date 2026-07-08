import Linglib.Features.Aktionsart
import Linglib.Features.Attitudes
import Linglib.Features.Causation
import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Semantics.ArgumentStructure.MeaningComponents
import Linglib.Semantics.Causation.CCSelection
import Linglib.Semantics.Causation.Sufficiency
import Linglib.Semantics.Causation.Necessity
import Linglib.Semantics.Causation.Prevention

/-!
# Causative Interpretation (force-dynamic dispatch)
[nadathur-lauer-2020] [talmy-1988] [wolff-2003]

Maps `Causative` verb classifications to their compositional semantics
under the **force-dynamic** view ([talmy-1988], [wolff-2003]),
which collapses `enable`/`force`/`make` into a single sufficiency
predicate (`causallySufficient`) distinguished post-hoc by `isCoercive`/`isPermissive`.

| Causative | Mechanism | English verbs | N&L property (derived) |
|-----------|-----------|---------------|----------------------|
| cause | Counterfactual dependence | cause | necessity |
| make | Direct sufficient guarantee | make, have, get | sufficiency |
| force | Coercive (overcome resistance) | force | sufficiency + coercion |
| enable | Barrier removal (permissive) | let, enable | sufficiency |
| prevent | Barrier addition (blocking) | prevent | preventSem |

## Theoretical commitment

This file commits to the force-dynamic mapping. The competing
**causal-model-theoretic** view ([sloman-barbey-hotaling-2009])
distinguishes `enable` from `make`/`cause` *structurally*: enable
asserts `B := A ∧ X` (accessory variable required), while cause asserts
`B := A`. Under that view, the present `Causative.toSemantics`
mis-classifies enable. The Sloman alternative dispatch — and a
divergence theorem witnessing the disagreement on `enable` — lives
in `Studies/SlomanBarbeyHotaling2009.lean`.

This is intentional. linglib does not pretend a single canonical
mapping exists; both dispatches coexist as named functions and the
disagreement is theorem-provable.
-/

-- ════════════════════════════════════════════════════
-- § Methods on `Features.Causative`
-- ════════════════════════════════════════════════════

/-! Methods on `Features.Causative` that depend on heavy semantic
machinery (`Causation.SEM`, `CausalGraph`, the `Necessity`/
`Sufficiency`/`Prevention` modules) live here rather than in
`Features/Causation.lean`, which is kept import-free per the
"Features/ stays lightweight" convention. The `namespace
Features.Causative` block below is the standard mathlib pattern for
distributing methods on a type across files based on import weight. -/

namespace Features.Causative

open Causation.CCSelection
open Causation (SEM CausalGraph Valuation DecidableValuation)

/-- The CC-selection mode associated with each variant.

    - `.cause` selects any necessary condition → `memberOfSufficientSet`
    - `.make`/`.force`/`.enable` select the completing condition →
      `completionOfSufficientSet`
    - `.prevent` selects the condition that blocks the effect →
      `completionOfSufficientSet` (the preventer completes the blocking set) -/
def selectionMode : Causative → CCSelectionMode
  | .cause => .memberOfSufficientSet
  | .make | .force | .enable | .prevent => .completionOfSufficientSet

/-- Force-dynamic dispatch: map a causative classification to its V2
    polymorphic semantic function. -/
noncomputable def toSemantics {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M] :
    Causative → Valuation α → ∀ c : V, α c → ∀ e : V, α e → Prop
  | .cause => Causation.Necessity.causeSem M
  | .make => Causation.Sufficiency.makeSem M
  | .force => Causation.Sufficiency.makeSem M
  | .enable => Causation.Sufficiency.makeSem M
  | .prevent => Causation.Prevention.preventSem M

end Features.Causative

-- ════════════════════════════════════════════════════
-- § Derivation theorems (substrate-independent)
-- ════════════════════════════════════════════════════

namespace Causation.Interpretation

open ArgumentStructure
open Features

/-- `make` and `force` are distinguished by coercion despite sharing truth conditions. -/
theorem make_force_distinguished_by_coercion :
    Causative.make.isCoercive = false ∧
    Causative.force.isCoercive = true := ⟨rfl, rfl⟩

/-- `make` and `enable` are distinguished by permissivity despite sharing truth conditions. -/
theorem make_enable_distinguished_by_permissivity :
    Causative.make.isPermissive = false ∧
    Causative.enable.isPermissive = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Bridge to CC-Selection
-- ════════════════════════════════════════════════════

/-! `Causative` encodes force-dynamic mechanisms; `CCSelectionMode`
([baglini-bar-asher-siegal-2025]) encodes which element of a causal
model the construction can select as "the cause." These are orthogonal
but connected: each variant has a canonical selection mode. -/

/-- Sufficiency variants have completion selection mode. -/
theorem sufficiency_selects_completion (b : Causative)
    (h : b.assertsSufficiency = true) :
    b.selectionMode = .completionOfSufficientSet := by
  cases b <;> simp_all [Causative.assertsSufficiency, Causative.selectionMode]

/-- Necessity variant has member selection mode. -/
theorem necessity_selects_member :
    Causative.cause.selectionMode = .memberOfSufficientSet := rfl

end Causation.Interpretation
