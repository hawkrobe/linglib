import Linglib.Semantics.Truthmaker.Basic
import Linglib.Core.Order.UpperLower.Closure

/-! # Closure Conditions on Truthmaker Propositions [jago-2026]

Jago Def 4: A truthmaker proposition (a set of states `P : Set S`) may
satisfy three closure conditions:

- **Closed (`P^⊔`)**: closed under nonempty fusion — if `Q ⊆ P` is
  nonempty, then `⊔Q ∈ P`.
- **Convex (`P^∼`)**: convex under parthood — if `s, u ∈ P` and
  `s ≤ t ≤ u`, then `t ∈ P`.
- **Regular (`P^*`)**: both closed and convex.

Closures are not redefined here — they are imported from
`Semantics/Mereology.lean`:

- `Mereology.AlgClosure P` is `P^⊔` (Jago: closed under fusion).
- `Mereology.setOf_algClosure` identifies it with mathlib's `supClosure`.
- `ordConnectedHull P` is `P^∼` (Jago: convex under parthood).
- `ordConnectedHull : ClosureOperator (Set α)` bundles it.
- `Set.OrdConnected` is the convex predicate (via `ordConnectedHull`).
- The regular closure `P^*` is `ordConnectedHull (AlgClosure P)`.

This file provides the **truthmaker-flavored vocabulary** (`IsClosed`,
`IsRegular`, `regularClose`) and the bridges to mathlib's
`ClosureOperator.IsClosed` API.

CAVEAT: `IsClosed` here is the *finitary* version (closed under binary
fusion via `AlgClosure`'s inductive definition). Jago's encyclopedia
text is "closed under nonempty fusion" of arbitrary subsets. Over a
`SemilatticeSup` with no infinitary `sSup`, these coincide on finite
witnesses; for infinitary closure use `LowerSet`-style packaging.

-/

namespace Semantics.Truthmaker

open _root_.Mereology

-- ════════════════════════════════════════════════════
-- § 1. Closed propositions (Jago's `P^⊔`)
-- ════════════════════════════════════════════════════

section Closed
variable {S : Type*} [SemilatticeSup S]

/-- A proposition is **closed** under (finite, nonempty) fusion iff it
    is fixed by `AlgClosure` — equivalently `CUM`. Truthmaker-flavored
    alias for `Mereology.CUM`. -/
abbrev IsClosed (p : TMProp S) : Prop := CUM p

/-- The closed closure `p^⊔ = AlgClosure p` is itself closed.
    Re-export of `Mereology.algClosure_cum`. -/
theorem isClosed_algClosure (p : TMProp S) : IsClosed (AlgClosure p) :=
  algClosure_cum

end Closed

-- ════════════════════════════════════════════════════
-- § 2. Convex propositions (Jago's `P^∼`)
-- ════════════════════════════════════════════════════

section Convex
variable {S : Type*} [PartialOrder S]

/-- A proposition is **convex** iff it lies between any two of its
    members in the partial order — mathlib's `Set.OrdConnected`, in
    Jago's vocabulary. -/
abbrev IsConvex (p : TMProp S) : Prop := Set.OrdConnected p

/-- Convex closure of a `TMProp` — the order-convex hull `ordConnectedHull`
    (recall `Set α = α → Prop = TMProp α` definitionally). -/
abbrev convexClose (p : TMProp S) : TMProp S := ordConnectedHull p

/-- The convex closure of `p` is convex (`ordConnected_ordConnectedHull`). -/
theorem isConvex_convexClose (p : TMProp S) : IsConvex (convexClose p) :=
  ordConnected_ordConnectedHull p

end Convex

-- ════════════════════════════════════════════════════
-- § 3. Regular propositions (Jago's `P^*`)
-- ════════════════════════════════════════════════════

section Regular
variable {S : Type*} [SemilatticeSup S]

/-- A proposition is **regular** iff both closed (under fusion) and
    convex (under parthood) — [jago-2026] Def 4.
    `Prop`-shape via `∧` for mathlib uniformity. -/
def IsRegular (p : TMProp S) : Prop := IsClosed p ∧ IsConvex p

/-- Regular closure: convexify the algebraic closure.
    `regularClose p = (p^⊔)^∼` — composition of the two closure
    operators of `Semantics/Mereology.lean`. -/
def regularClose (p : TMProp S) : TMProp S :=
  convexClose (AlgClosure p)

/-- `p ⊆ p^*`: regular closure extends the original. -/
theorem subset_regularClose (p : TMProp S) {s : S} (h : p s) :
    regularClose p s :=
  mem_ordConnectedHull.mpr ⟨s, AlgClosure.base h, s, AlgClosure.base h, le_refl s, le_refl s⟩

/-- The regular closure is convex. -/
theorem isConvex_regularClose (p : TMProp S) :
    IsConvex (regularClose p) :=
  isConvex_convexClose _

end Regular

end Semantics.Truthmaker
