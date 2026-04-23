import Linglib.Core.Lexical.VerbClass
import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.Prevention

/-!
# Causative Interpretation (force-dynamic dispatch)
@cite{nadathur-lauer-2020} @cite{talmy-1988} @cite{wolff-2003}

Maps `Causative` verb classifications to their compositional semantics
under the **force-dynamic** view (@cite{talmy-1988}, @cite{wolff-2003}),
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
**causal-model-theoretic** view (@cite{sloman-barbey-hotaling-2009})
distinguishes `enable` from `make`/`cause` *structurally*: enable
asserts `B := A ∧ X` (accessory variable required), while cause asserts
`B := A`. Under that view, the present `Causative.toSemantics`
mis-classifies enable. The Sloman alternative dispatch — and a
divergence theorem witnessing the disagreement on `enable` — lives
in `Phenomena/Causation/Studies/SlomanBarbeyHotaling2009.lean`.

This is intentional. linglib does not pretend a single canonical
mapping exists; both dispatches coexist as named functions and the
disagreement is theorem-provable.
-/

-- ════════════════════════════════════════════════════
-- § Semantic interpretation
-- ════════════════════════════════════════════════════

namespace Core.Verbs

open Semantics.Causation.CCSelection

/-- The CC-selection mode associated with each variant.

    - `.cause` selects any necessary condition → `memberOfSufficientSet`
    - `.make`/`.force`/`.enable` select the completing condition →
      `completionOfSufficientSet`
    - `.prevent` selects the condition that blocks the effect →
      `completionOfSufficientSet` (the preventer completes the blocking set) -/
def Causative.selectionMode : Causative → CCSelectionMode
  | .cause => .memberOfSufficientSet
  | .make | .force | .enable | .prevent => .completionOfSufficientSet

end Core.Verbs

-- ════════════════════════════════════════════════════
-- § Derivation theorems (substrate-independent)
-- ════════════════════════════════════════════════════

namespace Semantics.Causation.Interpretation

open Core.Verbs

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
(@cite{baglini-bar-asher-siegal-2025}) encodes which element of a causal
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

end Semantics.Causation.Interpretation

/-! ### Causative semantic dispatch

`Causative.toSemantics` is the canonical force-dynamic dispatch:
maps a `Causative` variant to its polymorphic V2 semantic function.
All variants share arity `(bg, cause, xC, effect, xE)` — Bool models
pass `xC = xE = true`, multi-valued models supply genuine values.

The previous Bool-implicit `CausalDynamics`-based dispatch (Phase D-A
and earlier) was deleted in Phase D-G2 in favor of this polymorphic
form. The V2 sub-namespace `Core.Verbs.Causative.V2.toSemantics` was
the staging area; it's now the canonical name. -/

namespace Core.Verbs

namespace Causative

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

/-- Force-dynamic dispatch: map a causative classification to its V2
    polymorphic semantic function. -/
noncomputable def toSemantics {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M] :
    Causative → Valuation α → ∀ c : V, α c → ∀ e : V, α e → Prop
  | .cause => Semantics.Causation.Necessity.causeSem M
  | .make => Semantics.Causation.Sufficiency.makeSem M
  | .force => Semantics.Causation.Sufficiency.makeSem M
  | .enable => Semantics.Causation.Sufficiency.makeSem M
  | .prevent => Semantics.Causation.Prevention.preventSem M

end Causative

end Core.Verbs
