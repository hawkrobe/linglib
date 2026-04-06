import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Lattice
import Linglib.Core.Mereology

/-!
# Mereotopology
@cite{casati-varzi-1999} @cite{grimm-2012} @cite{krifka-2021}

Mereotopological infrastructure grounded in Mathlib's `TopologicalSpace`,
`IsConnected`, and `closure`. Extends `Core/Mereology.lean` (algebraic
parthood, overlap, CUM/DIV/QUA) with topological structure (connection,
self-connection, touch).

## Grounding in Mathlib

Casati & Varzi (1999) take Connection C as a mereotopological *primitive*.
We derive it instead from two independent Mathlib structures:

1. **`SemilatticeSup`** — algebraic mereology (parthood ≤, sum ⊔, overlap)
2. **`TopologicalSpace`** — spatial structure (open sets, closure, connectivity)

The topology is *not* derived from the order (contra `OrderTopology`).
This respects the philosophical position of @cite{casati-varzi-1999} that
spatial arrangement is irreducible to parthood: two entities may share
parts (overlap) without being spatially adjacent, and may touch without
sharing parts. Adding topology as independent structure captures this.

## Key Correspondences

| Mereotopology | Mathlib definition |
|---|---|
| Self-connection SC(x) | `IsConnected (Set.Iic x)` |
| Touch ∞(x,y) | `¬Overlap ∧ (closure (Iic x) ∩ closure (Iic y)).Nonempty` |
| Connection C(x,y) | `Overlap ∨ Touch` |
| Connected Liquid | `IsConnected (Iic x) ∧ ∀ y ≤ x, phase y = .liquid` |

## Compatibility

The `ContinuousSup` typeclass ensures mereological sum (⊔) is
topologically continuous, so joining connected parts preserves
connectivity under appropriate conditions.
-/

namespace Mereotopology

open Set Mereology

-- ════════════════════════════════════════════════════
-- § 1. Self-Connection
-- ════════════════════════════════════════════════════

/-- The principal downset (parts of x), viewed as a set.
    This is the topological representative of entity x:
    the region of space x occupies. -/
abbrev parts {α : Type*} [Preorder α] (x : α) : Set α := Set.Iic x

/-- Self-connected: the set of parts of x is topologically connected.

    @cite{casati-varzi-1999} def 20b:
      SC(x) := ∀y,z [∀w (O(w,x) ↔ O(w,y) ∨ O(w,z)) → C(y,z)]

    Grounded via Mathlib's `IsConnected`: a set is connected iff it is
    nonempty and cannot be partitioned into two disjoint nonempty
    open subsets. The set in question is `Set.Iic x = {y | y ≤ x}`,
    the principal downset — all parts of x.

    An atomic entity (e.g., a point particle) is trivially self-connected
    since `{x}` is connected. A scattered aggregate (e.g., separate
    shots of tequila and lime juice at a bar) is NOT self-connected. -/
def SelfConnected {α : Type*} [Preorder α] [TopologicalSpace α]
    (x : α) : Prop :=
  IsConnected (parts x)

-- ════════════════════════════════════════════════════
-- § 2. Touch (External Connection)
-- ════════════════════════════════════════════════════

/-- Touch: external connection without overlap.

    @cite{casati-varzi-1999}: two entities touch when their closures
    share a point but they have no common part. Grounded via Mathlib's
    `closure`: the smallest closed set containing a given set.

    Intuitively: the wine and the bottle touch (their closures share
    boundary points) but do not overlap (no part is both wine and bottle).

    @cite{krifka-2021} def 21 gives an order-theoretic characterization:
      x ∞ y := ¬O(x,y) ∧ ∃z,z'[z ≤ x ∧ z' ≤ y ∧ ¬∃z''[z < z'' < z']]
    Under the standard spatial model (regular open subsets of ℝⁿ), the
    order-theoretic and closure-based definitions coincide. -/
def Touch {α : Type*} [PartialOrder α] [TopologicalSpace α]
    (x y : α) : Prop :=
  ¬ Overlap x y ∧ (closure (parts x) ∩ closure (parts y)).Nonempty

/-- Touch is symmetric. -/
theorem Touch.symm {α : Type*} [PartialOrder α] [TopologicalSpace α]
    {x y : α} (h : Touch x y) : Touch y x :=
  ⟨fun ho => h.1 ho.symm, by rw [Set.inter_comm]; exact h.2⟩

-- ════════════════════════════════════════════════════
-- § 3. Connection (Derived)
-- ════════════════════════════════════════════════════

/-- Connection: two entities are connected if they overlap or touch.

    @cite{casati-varzi-1999} take C as primitive. We derive it.
    C(x,y) := O(x,y) ∨ Touch(x,y).

    Connection is reflexive (via overlap) and symmetric. -/
def Connected {α : Type*} [PartialOrder α] [TopologicalSpace α]
    (x y : α) : Prop :=
  Overlap x y ∨ Touch x y

theorem Connected.refl {α : Type*} [PartialOrder α] [TopologicalSpace α]
    (x : α) : Connected x x :=
  .inl (Overlap.refl x)

theorem Connected.symm {α : Type*} [PartialOrder α] [TopologicalSpace α]
    {x y : α} (h : Connected x y) : Connected y x := by
  rcases h with ho | ht
  · exact .inl ho.symm
  · exact .inr ht.symm

theorem overlap_connected {α : Type*} [PartialOrder α] [TopologicalSpace α]
    {x y : α} (h : Overlap x y) : Connected x y :=
  .inl h

-- ════════════════════════════════════════════════════
-- § 4. Matter Phase (@cite{krifka-2021})
-- ════════════════════════════════════════════════════

/-- Phase of matter, following @cite{krifka-2021}'s trichotomy.

    - **solid**: retains shape, parts don't move relative to each other
    - **granular**: aggregate of discrete solid pieces (rice, sand)
    - **liquid**: parts in constant internal motion, self-connected
      at any time interval

    This distinction drives the count/mass behavior of substance nouns:
    solids and granulars can be individuated by shape/grain boundaries;
    liquids lack internal boundaries (pure substances) or have them
    only via ingredient structure (mixed drinks, @cite{moon-2026}). -/
inductive Phase where
  | solid
  | granular
  | liquid
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 5. Connected Liquid
-- ════════════════════════════════════════════════════

/-- Connected liquid: an entity that is self-connected and whose parts
    are all in liquid phase.

    @cite{moon-2026} def 23 (following @cite{krifka-2021}):
      CONNECTED LIQUID(x) := ∀t ∈ i ∀x'[x' ≤ x →
        ¬solid(x',t) ∧ ¬granular(x',t) ∧ SC(x,t)]

    We omit the temporal parameter for now (static mereotopology). -/
def ConnectedLiquid {α : Type*} [PartialOrder α] [TopologicalSpace α]
    (phase : α → Phase) (x : α) : Prop :=
  SelfConnected x ∧ ∀ y ∈ parts x, phase y = .liquid

-- ════════════════════════════════════════════════════
-- § 6. Basic Theorems
-- ════════════════════════════════════════════════════

/-- Every entity is in its own parts. -/
theorem mem_parts_self {α : Type*} [Preorder α] (x : α) : x ∈ parts x :=
  le_refl x

/-- Self-connection implies nonemptiness (from `IsConnected`). -/
theorem SelfConnected.nonempty {α : Type*} [Preorder α] [TopologicalSpace α]
    {x : α} (h : SelfConnected x) : (parts x).Nonempty :=
  h.1

/-- Atoms are self-connected when singletons are connected.
    In any T1 space (where singletons are closed), `{x}` is connected
    since it's a singleton — and if x is an atom, `parts x = {x}`. -/
theorem selfConnected_of_atom {α : Type*} [PartialOrder α] [TopologicalSpace α]
    {x : α} (_hAtom : Atom x) (hParts : parts x = {x}) :
    SelfConnected x := by
  rw [SelfConnected, hParts]
  exact isConnected_singleton

/-- Connected liquid implies self-connected. -/
theorem ConnectedLiquid.selfConnected {α : Type*} [PartialOrder α] [TopologicalSpace α]
    {phase : α → Phase} {x : α} (h : ConnectedLiquid phase x) :
    SelfConnected x :=
  h.1

-- ════════════════════════════════════════════════════
-- § 7. Topological Non-Cumulativity
-- ════════════════════════════════════════════════════

/-! ### The CUM/QUA incompleteness of pure mereology

In pure mereology (`SemilatticeSup` alone), the CUM/QUA classification
is nearly exhaustive for non-trivial predicates:

- CUM and QUA are incompatible (`qua_cum_incompatible`)
- For non-singleton predicates, ¬CUM typically comes from QUA

Adding `TopologicalSpace` as **independent** structure (not
`OrderTopology`) creates a third category: **¬CUM ∧ ¬QUA**.

The mechanism is the fundamental asymmetry of topological connectivity
with respect to lattice operations:

- **Join can disconnect**: `IsConnected(↓x) ∧ IsConnected(↓y)` does
  NOT imply `IsConnected(↓(x ⊔ y))`. Two connected sets placed apart
  form a disconnected union.
- **Restriction can preserve**: `y ≤ x ∧ IsConnected(↓x)` is
  consistent with `IsConnected(↓y)`. A connected subset of a
  connected set can remain connected.

This asymmetry means:
1. Connectivity constraints **block CUM** — join of connected things
   can be disconnected, so the predicate is not closed under ⊔.
2. Connectivity constraints **don't imply QUA** — proper parts can
   remain connected, so proper-part witnesses can satisfy the predicate.

The result: ¬CUM ∧ ¬QUA predicates exist in mereotopological spaces
but not in pure semilattices. Natural language exploits this gap for
mixed drink nouns (@cite{moon-2026}), where individuation comes from
topological connectivity rather than mereological atomicity.

Compare the two independent sources of non-cumulativity:

| Source | Mechanism | Result |
|---|---|---|
| Algebraic (atomicity) | `Atom x → ¬∃ y, y < x` | QUA (no proper parts) |
| Topological (connectivity) | `¬IsConnected(↓(x ⊔ y))` | ¬CUM (join fails predicate) |

The algebraic source (QUA) implies ¬CUM for non-singletons
(`qua_cum_incompatible`). The topological source (connectivity)
gives ¬CUM independently, without implying QUA.
-/

section TopologicalNonCumulativity

variable {α : Type*} [SemilatticeSup α] [TopologicalSpace α]

/-- Any predicate entailing self-connectivity fails CUM when two
    instances have a disconnected join.

    This is the **topological** source of non-cumulativity. Compare
    with the **algebraic** source: QUA implies ¬CUM for non-singletons
    (`qua_cum_incompatible`). The two sources are orthogonal.

    Proof: if CUM held, `P(x) ∧ P(y) → P(x ⊔ y)`, and then
    `hConn` would give `SelfConnected(x ⊔ y)`, contradicting `hDisc`. -/
theorem connectivity_breaks_cum
    {P : α → Prop}
    (hConn : ∀ x, P x → SelfConnected x)
    {x y : α} (hx : P x) (hy : P y)
    (hDisc : ¬ SelfConnected (x ⊔ y)) :
    ¬ CUM P := by
  intro hCum
  exact hDisc (hConn _ (hCum x y hx hy))

/-- ¬CUM ∧ ¬QUA from connectivity: the **middle ground** between mass
    and standard count that is invisible to pure mereology.

    Given a predicate P that entails self-connectivity:
    - Two instances with a disconnected join witness ¬CUM (topological)
    - An instance with a proper part also satisfying P witnesses ¬QUA

    In pure mereology, ¬CUM for non-singletons comes from QUA
    (`qua_cum_incompatible`), so ¬CUM ∧ ¬QUA is impossible.
    With independent topology, the two conditions decouple.

    The linguistic instantiation: mixed drink nouns (@cite{moon-2026})
    are ¬CUM (disconnected margaritas aren't a margarita) and ¬QUA
    (half a margarita with preserved ratios is still a margarita). -/
theorem connectivity_middle_ground
    {P : α → Prop}
    (hConn : ∀ x, P x → SelfConnected x)
    -- CUM failure witnesses: two P-instances whose join is disconnected
    {a b : α} (ha : P a) (hb : P b)
    (hDisc : ¬ SelfConnected (a ⊔ b))
    -- QUA failure witnesses: a P-instance with a proper part also in P
    {x y : α} (hx : P x) (hy : P y) (hlt : y < x) :
    ¬ CUM P ∧ ¬ QUA P :=
  ⟨connectivity_breaks_cum hConn ha hb hDisc,
   fun hQ => hQ x y hx hlt hy⟩

end TopologicalNonCumulativity

end Mereotopology
