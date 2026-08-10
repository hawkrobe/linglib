import Linglib.Features.Aktionsart
import Linglib.Features.Attitudes
import Linglib.Semantics.Causation.VerbClass
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
predicate (`makeSem`); the three remain distinct lexical classifications.

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

/-! ### Methods on `Causative` -/

/-! Methods on `Causative` that depend on heavy semantic
machinery (`Causation.SEM`, `CausalGraph`, the `Necessity`/
`Sufficiency`/`Prevention` modules) live here rather than in
`Semantics/Causation/VerbClass.lean`, which is kept import-free. -/

namespace Causative

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

/-- Sufficiency-asserting variants share `makeSem` truth conditions: the
`AssertsSufficiency` classification tracks the force-dynamic dispatch. -/
theorem AssertsSufficiency.toSemantics_eq {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    {b : Causative} (h : b.AssertsSufficiency) :
    b.toSemantics M = Causation.Sufficiency.makeSem M := by
  rcases h with rfl | rfl | rfl <;> rfl

end Causative

/-! ### Derivation theorems (substrate-independent) -/

namespace Causation.Interpretation

open ArgumentStructure
open Features

/-! ### Bridge to CC-Selection -/

/-! `Causative` encodes force-dynamic mechanisms; `CCSelectionMode`
([baglini-bar-asher-siegal-2025]) encodes which element of a causal
model the construction can select as "the cause." These are orthogonal
but connected: each variant has a canonical selection mode. -/

/-- Sufficiency variants have completion selection mode. -/
theorem sufficiency_selects_completion (b : Causative)
    (h : b.AssertsSufficiency) :
    b.selectionMode = .completionOfSufficientSet := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- Necessity variant has member selection mode. -/
theorem necessity_selects_member :
    Causative.cause.selectionMode = .memberOfSufficientSet := rfl

end Causation.Interpretation
