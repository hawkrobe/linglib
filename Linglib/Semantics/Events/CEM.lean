import Linglib.Semantics.Mereology
import Linglib.Semantics.Events.Basic

/-!
# Event mereology

Event-specific mereological infrastructure built on the generic `Mereology`
definitions. `EventCEM` makes the event domain a **classical extensional
mereology** in the sense of [hovda-2009] — parthood is a partial order closed
under unrestricted type-2 fusion (`Fusion2E`) with weak supplementation
(`WeakSup`) — and additionally requires the temporal trace τ to be a sum
homomorphism ([champollion-2017]; [bach-1986] for the underlying event algebra).

Because a classical mereology has *unique* type-2 fusions, the binary sum `⊔`
on events is the fusion of a pair rather than a stipulated operation: the
join-semilattice structure consumers use is *derived* from the fusion axioms.

## Main definitions

* `EventCEM` — events as a classical extensional mereology with τ a sum hom.
* `instSemilatticeSupEvent` — the derived binary-sum (`⊔`) structure on events.
* `EventCEM.sup_isLUB` — the event sum is the mereological fusion (a least
  upper bound), not a free operation.
* `instIsSumHomRuntime` — τ (runtime) as a `Mereology.IsSumHom`.

Generic mereological vocabulary (`CUM`, `QUA`, `IsSumHom`, `Overlap`, `IsFusion`,
`ClassicalMereology`, …) lives in `Mereology`; consumers `open Mereology`.
-/

namespace Semantics.Events.CEM

open _root_.Mereology

/-! ### Events as a classical extensional mereology -/

/-- The binary sum `⊔` on events, derived from the classical-mereology fusion
    axioms: `e₁ ⊔ e₂` is the unique type-2 fusion of `{e₁, e₂}`. Noncomputable
    because the fusion is extracted by choice from `Fusion2E`. -/
noncomputable instance instSemilatticeSupEvent (Time : Type*) [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)] :
    SemilatticeSup (Event Time) :=
  ClassicalMereology.toSemilatticeSup

/-- The event domain is a **classical extensional mereology** ([hovda-2009]):
    parthood (`Event.Mereology`) is a partial order closed under unrestricted
    type-2 fusion with weak supplementation, and the temporal trace τ is a sum
    homomorphism — the runtime of a sum is the (convex-hull) sum of the
    runtimes ([champollion-2017]). -/
class EventCEM (Time : Type*) [LinearOrder Time] extends
    Event.Mereology Time, ClassicalMereology (Event Time) where
  /-- τ is a sum homomorphism: τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂). -/
  τ_hom : ∀ e₁ e₂ : Event Time,
    (e₁ ⊔ e₂).runtime = e₁.runtime ⊔ e₂.runtime

/-- The derived binary-sum structure on events, named so that `EventCEM`-typed
    code can refer to it explicitly (`cem.evSemilatticeSup`). -/
@[reducible] noncomputable def EventCEM.evSemilatticeSup {Time : Type*}
    [LinearOrder Time] (cem : EventCEM Time) : SemilatticeSup (Event Time) :=
  instSemilatticeSupEvent Time

/-- The event sum `e₁ ⊔ e₂` is the least upper bound of `{e₁, e₂}` under
    parthood — i.e. the mereological fusion, not a stipulated operation. -/
theorem EventCEM.sup_isLUB {Time : Type*} [LinearOrder Time] [EventCEM Time]
    (e₁ e₂ : Event Time) : IsLUB {e₁, e₂} (e₁ ⊔ e₂) :=
  Classical.choose_spec (ClassicalMereology.exists_isLUB_pair e₁ e₂)

/-! ### Lexical cumulativity

A verb predicate is lexically cumulative iff it is closed under event sum —
exactly `Mereology.CUM` over `Event Time`. [champollion-2017] takes lexical
cumulativity (of verbs, events, and roles) as a working hypothesis, *universal*
over verbal predicates (telic ones included); it is `CUM` and is used directly,
with no event-specific re-spelling. -/

/-! ### Trace functions as sum-homomorphisms ([champollion-2017])

[champollion-2017] calls τ (and the spatial trace σ, and the thematic-role
extractors) *trace functions*. Their shared structural property is
**sum-homomorphism**: the trace of a sum is the sum of the traces. Linglib uses
`Mereology.IsSumHom` as the unifying abstraction, so dimension-polymorphic
theorems (`StratifiedReference.lean`) instantiate uniformly across the traces.
τ's instance is below; σ's is `instIsSumHomσ` in `Trace.lean`. -/

/-- τ (runtime extraction) as a `Mereology.IsSumHom`, from `EventCEM.τ_hom`.
    Lets `cum_pullback` fire for τ without threading the homomorphism proof. -/
noncomputable instance instIsSumHomRuntime (Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] : IsSumHom (fun e : Event Time => e.runtime) :=
  ⟨fun e₁ e₂ => cem.τ_hom e₁ e₂⟩

end Semantics.Events.CEM
