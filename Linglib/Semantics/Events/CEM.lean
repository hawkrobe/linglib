import Linglib.Semantics.Mereology
import Linglib.Semantics.Events.Basic

/-!
# Event mereology

The event domain as a **classical extensional mereology** ([hovda-2009]). Events
carry a parthood partial order (`Event.Mereology`); when that order is a
`Mereology.ClassicalMereology` — closed under unrestricted type-2 fusion with
weak supplementation — the binary event sum `⊔` is the *unique fusion* of a pair
(`instSemilatticeSupEvent`, `sup_isLUB`) rather than a stipulated operation.

## Implementation notes

There is deliberately no single bundled event-mereology class. An event theory's
two assumptions — that events form a classical mereology, and (separately) that a
trace function such as the temporal trace `Event.runtime` is a
`Mereology.IsSumHom` — are logically independent, so callers state the standard
mixins directly:
`[ClassicalMereology (Event Time)]` and, where τ-pullback is needed,
`[IsSumHom (fun e => e.runtime)]` ([champollion-2017] §2.5; [bach-1986] for the
underlying event algebra).

Lexical cumulativity of a verb predicate is just `Mereology.CUM` over
`Event Time` — [champollion-2017] takes it as a working hypothesis, *universal*
over verbal predicates (telic ones included) — so it is used directly with no
event-specific re-spelling.

## Main definitions

* `instSemilatticeSupEvent` — the derived binary-sum (`⊔`) structure on events,
  from the classical-mereology fusion axioms.
* `sup_isLUB` — the event sum is the mereological fusion (a least upper bound).

Generic mereological vocabulary (`CUM`, `QUA`, `IsSumHom`, `Overlap`, `IsFusion`,
`ClassicalMereology`, …) lives in `Mereology`; consumers `open Mereology`.
-/

namespace Semantics.Events.CEM

open _root_.Mereology

/-- The binary sum `⊔` on events, derived from the classical-mereology fusion
    axioms: `e₁ ⊔ e₂` is the unique type-2 fusion of `{e₁, e₂}`. Noncomputable
    because the fusion is extracted by choice from `Fusion2E`. -/
noncomputable instance instSemilatticeSupEvent (Time : Type*) [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)] :
    SemilatticeSup (Event Time) :=
  ClassicalMereology.toSemilatticeSup

/-- The event sum `e₁ ⊔ e₂` is the least upper bound of `{e₁, e₂}` under
    parthood — i.e. the mereological fusion, not a stipulated operation. -/
theorem sup_isLUB {Time : Type*} [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)]
    (e₁ e₂ : Event Time) : IsLUB {e₁, e₂} (e₁ ⊔ e₂) :=
  Classical.choose_spec (ClassicalMereology.exists_isLUB_pair e₁ e₂)

end Semantics.Events.CEM
