import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.EventAdjacency
import Linglib.Theories.Semantics.Events.InitialFinalParts
import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Theories.Semantics.Spatial.Path

/-!
# Movement Relations and Path-Event Correspondence
@cite{krifka-1998} @cite{zwarts-2005} @cite{talmy-2000} @cite{gawron-2009}

Substrate for the propositional theory of movement events: predicates
that classify thematic relations θ between paths/objects and events
according to whether they preserve adjacency, precedence, and the
correspondence between sub-events and sub-paths.

Topic-named (not paper-named): defines the deep substrate that
`@cite{krifka-1998}` §4 (*Telicity by Precedence and Adjacency*),
`@cite{zwarts-2005}` (path-PP semantics), and `@cite{gawron-2009}`
(spatial events) all use. Specific paper replications import this
file and instantiate the predicates on paper-specific data.

## Sections

1. **Event adjacency and precedence** — `Ev.adjacent` and `Ev.precedes`,
   defined on `Ev Time` via runtime intervals.
2. **Initial/final parts** — `IsInitialPart`/`IsFinalPart`, generic
   over a partial order and a precedence relation. K98 eq. 36.
3. **Expansion (EXP)** — K98 eq. 63: temporally-following sub-events
   correspond to non-overlapping sub-objects.
4. **Strictly Expansive Incremental (SEINC)** — K98 eq. 65: EXP + MO.
5. **Adjacency property (ADJ)** — K98 eq. 68: temporal adjacency on
   sub-events iff spatial adjacency on sub-paths.
6. **Strict Movement Relations (SMR)** — K98 eq. 69: ADJ + MO +
   path-only range.
7. **Movement Closure and General Movement (MR)** — K98 eq. 71:
   smallest relation containing some SMR θ' and closed under
   precedence-respecting sums. Parallel to `IncClosure`/`INC` in
   `Krifka1998.lean` §8.
8. **Source and Goal (SOURCE / GOAL)** — K98 eq. 73: directional
   adverbial-modifier predicates relating path endpoints to event
   initial/final parts.
9. **Derived movement-event measure (KM')** — K98 eq. 72:
   `km' KM = KM ∘ σ`, the event measure derived from a path measure
   via the spatial trace.
10. **Bridge to existing telicity infrastructure** — labels
    `SpatialTrace.bounded_path_telic` as the K98 §4 movement-relation
    telicity result; the heavy lifting is already done by the σ-pullback
    machinery in `Theories/Semantics/Events/SpatialTrace.lean`.

## Deferred (out of scope for this round)

- **TANG_H tangentiality** (K98 eq. 17) on directed paths — needed for
  the full MR closure axiom that excludes "telekinetic" movements
  (sums of non-tangential paths). The `MovementClosure` here uses a
  weaker precedence-only condition that admits stop-and-go, Alcatraz,
  and Echternach movements (K98 §4.3).
- **Full ADJ axioms** for adjacency on a part-mereology (K98 §2.3
  eq. 14.b: adjacency-doesn't-overlap and adjacency-propagates-under-
  part). The concrete `Path.adjacent` and `Ev.adjacent` defined here
  satisfy these but the propositional theorems are not added.
- **Cross-dimensional movements** (K98 §4.6: heat, bake, whip in
  directed temperature/done-ness paths) — requires a `DirectedPath`
  generalization of `Path Loc`.

-/

namespace Semantics.Events

open Mereology
open Semantics.Events.ThematicRoleProperties (MO)
open Semantics.Spatial.Path (Path)

-- Event adjacency (`Ev.adjacent`/`Ev.precedes`) and initial/final
-- parts (`IsInitialPart`/`IsFinalPart`) are now in their own focused
-- files (`EventAdjacency.lean` and `InitialFinalParts.lean`); imported
-- above. Movement-relation-specific content begins here.

namespace MovementRelations

open Semantics.Events.InitialFinalParts (IsInitialPart IsFinalPart)

-- ════════════════════════════════════════════════════
-- § 1. Expansion (EXP) — K98 §4.1 eq. 63
-- ════════════════════════════════════════════════════

/-- K98 §4.1 eq. 63 EXP: expansion property. If x is θ-related to e
    and y to a temporally-following e', then x and y do not overlap.
    Captures the dynamic intuition that temporally-distinct sub-events
    of a movement event correspond to non-overlapping sub-objects:
    walking from a to b and then from b to c covers non-overlapping
    spatial regions because the two events are temporally distinct. -/
def EXP {α β : Type*} [SemilatticeSup α]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e e' : β),
    θ x e → θ y e' → precedes e e' → ¬ Overlap x y

-- ════════════════════════════════════════════════════
-- § 4. Strictly Expansive Incremental (SEINC) — K98 eq. 65
-- ════════════════════════════════════════════════════

/-- K98 §4.1 eq. 65 SEINC: strictly expansive incremental. EXP
    (temporal-distinctness implies object-non-overlap) plus MO
    (mapping to objects: every event-part has a corresponding
    object-part). MO is from `Krifka1998.lean` §1. SEINC is K98's
    generalization of strict incrementality (SINC) to cases where
    the part-event correspondence is precedence-driven rather than
    bijective. -/
def SEINC {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  EXP precedes θ ∧ MO θ

-- ════════════════════════════════════════════════════
-- § 5. Adjacency Property (ADJ) — K98 §4.2 eq. 68
-- ════════════════════════════════════════════════════

/-- K98 §4.2 eq. 68 ADJ: adjacency property. Whenever two sub-events
    of a movement event are temporally adjacent, then their paths are
    spatially adjacent, and vice versa. The biconditional makes ADJ
    distinctive for movement: not all incremental relations satisfy
    it (e.g., consumption of an apple has spatial-adjacency-of-bites
    but not temporal-adjacency in a single event). -/
def ADJ {α β : Type*} [PartialOrder α] [PartialOrder β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop)
    (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y z : α) (e' e'' : β),
    θ x e → e' ≤ e → e'' ≤ e → y ≤ x → z ≤ x →
    θ y e' → θ z e'' → (adjβ e' e'' ↔ adjα y z)

-- ════════════════════════════════════════════════════
-- § 6. Strict Movement Relations (SMR) — K98 §4.2 eq. 69
-- ════════════════════════════════════════════════════

/-- K98 §4.2 eq. 69 SMR: θ is a strict movement relation iff (i) it
    has the adjacency property (ADJ), (ii) it satisfies mapping to
    objects (MO), and (iii) its first argument is constrained to
    paths (the K98 paper's `x ∈ U_H` condition; here parameterized
    by a path-membership predicate `isPath`). For `Path Loc`, take
    `isPath := fun _ => True`. -/
def SMR {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop)
    (isPath : α → Prop) (θ : α → β → Prop) : Prop :=
  ADJ adjα adjβ θ ∧ MO θ ∧ ∀ x e, θ x e → isPath x

-- ════════════════════════════════════════════════════
-- § 7. Movement Closure and MR — K98 §4.3 eq. 71
-- ════════════════════════════════════════════════════

/-- K98 §4.3 eq. 71 closure operation: smallest relation containing a
    base SMR θ' and closed under precedence-respecting sums. Each
    sum operation requires that the events being summed are in
    precedence order (preventing telekinetic concatenations of
    unrelated movements). Parallel to `IncClosure` (K98 §3.6 eq. 59
    in `Krifka1998.lean:386`).

    K98 eq. 71's full version additionally requires that the
    final-of-e parts and initial-of-e' parts have spatially
    tangential paths (TANG_H, eq. 17). This weaker version omits
    TANG_H — admits "stop-and-go" (e.g., (70.b)), "Alcatraz"
    (circular returning, (70.e)), and "Echternach" (with backups,
    (70.d)) movements that the full version also admits, but ALSO
    admits non-meeting telekinetic concatenations that K98 would
    rule out. Full TANG_H is deferred. -/
inductive MovementClosure {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ' : α → β → Prop) : α → β → Prop where
  /-- Base: anything in the strict movement relation θ' is in MR. -/
  | base {x : α} {e : β} : θ' x e → MovementClosure precedes θ' x e
  /-- Sum: precedence-ordered MR-pairs combine to a new MR-pair. -/
  | sum {x1 x2 : α} {e1 e2 : β} :
      MovementClosure precedes θ' x1 e1 →
      MovementClosure precedes θ' x2 e2 →
      precedes e1 e2 →
      MovementClosure precedes θ' (x1 ⊔ x2) (e1 ⊔ e2)

/-- K98 §4.3 eq. 71 MR: θ is a (general) movement relation iff there
    exists a strict movement relation θ' such that θ is the
    `MovementClosure` of θ'. -/
def MR {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop) (precedes : β → β → Prop)
    (isPath : α → Prop) (θ : α → β → Prop) : Prop :=
  ∃ θ' : α → β → Prop,
    SMR adjα adjβ isPath θ' ∧
    ∀ x e, θ x e ↔ MovementClosure precedes θ' x e

/-- Every SMR is itself an MR — a strict movement relation is its own
    movement closure (the base case of `MovementClosure`). -/
theorem mr_of_smr {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    {adjα : α → α → Prop} {adjβ : β → β → Prop} {precedes : β → β → Prop}
    {isPath : α → Prop} {θ : α → β → Prop}
    (h : SMR adjα adjβ isPath θ)
    (hClosed : ∀ x1 x2 e1 e2, θ x1 e1 → θ x2 e2 → precedes e1 e2 →
               θ (x1 ⊔ x2) (e1 ⊔ e2)) :
    MR adjα adjβ precedes isPath θ := by
  refine ⟨θ, h, fun x e => ⟨MovementClosure.base, ?_⟩⟩
  intro hcl
  induction hcl with
  | base h => exact h
  | sum _ _ hprec ih1 ih2 => exact hClosed _ _ _ _ ih1 ih2 hprec

-- ════════════════════════════════════════════════════
-- § 8. Source and Goal (SOURCE / GOAL) — K98 §4.5 eq. 73
-- ════════════════════════════════════════════════════

/-- K98 §4.5 eq. 73a SOURCE: y is the source of path x for event e
    iff path-parts adjacent to y correspond exactly to initial parts
    of e. The biconditional in K98 is split into two implications:
    initial-event-parts have y-adjacent path-parts AND non-initial
    event-parts have non-y-adjacent path-parts. -/
def SOURCE {α β : Type*} [PartialOrder α] [PartialOrder β]
    (adjα : α → α → Prop) (precedes : β → β → Prop)
    (x y : α) (e : β) : Prop :=
  ∀ (e' : β) (x' : α), e' ≤ e → x' ≤ x →
    (IsInitialPart precedes e' e → adjα x' y) ∧
    (¬ IsInitialPart precedes e' e → ¬ adjα x' y)

/-- K98 §4.5 eq. 73b GOAL: y is the goal of path x for event e iff
    path-parts adjacent to y correspond exactly to final parts of e. -/
def GOAL {α β : Type*} [PartialOrder α] [PartialOrder β]
    (adjα : α → α → Prop) (precedes : β → β → Prop)
    (x y : α) (e : β) : Prop :=
  ∀ (e' : β) (x' : α), e' ≤ e → x' ≤ x →
    (IsFinalPart precedes e' e → adjα x' y) ∧
    (¬ IsFinalPart precedes e' e → ¬ adjα x' y)

-- ════════════════════════════════════════════════════
-- § 9. Derived Movement-Event Measure (KM') — K98 §4.4 eq. 72
-- ════════════════════════════════════════════════════

/-- K98 §4.4 eq. 72 KM': derived measure for movement events. Given a
    path measure KM and a spatial trace σ, the event measure is the
    composition: each event measures via the path it covers. The
    resulting measure inherits extensivity from KM under the additional
    condition that the σ trace function is injective (so that distinct
    events with the same path don't double-count). -/
def km' {Loc Time α : Type*} [LinearOrder Time]
    [_cem : EventCEM Time] [_psup : SemilatticeSup (Path Loc)]
    [st : SpatialTrace Loc Time]
    (KM : Path Loc → α) : Ev Time → α :=
  fun e => KM (st.σ e)

-- ════════════════════════════════════════════════════
-- § 10. Bridge to existing SpatialTrace telicity infrastructure
-- ════════════════════════════════════════════════════

/-- The K98 §4 SMR + bounded-path → telic chain is realized by the
    existing spatial-trace pullback infrastructure: when σ is
    injective and the path predicate P is QUA (bounded), the pulled-
    back event predicate (P ∘ σ) is QUA on events (telic). This
    theorem labels `SpatialTrace.bounded_path_telic` as the K98 §4
    movement-relation telicity result; no new proof needed since
    SpatialTrace already does the σ-pullback work via `MereoDim`.

    K98 §4.5 (eq. 74, *Mary walked from the university to the
    capitol*): a SOURCE+GOAL-bounded path predicate is QUA, so the
    VP is telic. The σ-trace pullback lifts this to events. -/
theorem k98_movement_telic_via_spatial_trace
    {Loc Time : Type*} [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
    [st : SpatialTrace Loc Time]
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ st.σ) :=
  SpatialTrace.bounded_path_telic hinj hP

/-- K98 §4.5 (eq. 75, *Mary walked towards the capitol*): a SOURCE-but-
    no-GOAL path predicate is CUM (unbounded direction), so the VP
    is atelic. The σ-trace pullback lifts this to events. Direct
    delegate to `SpatialTrace.unbounded_path_atelic`. -/
theorem k98_unbounded_movement_atelic_via_spatial_trace
    {Loc Time : Type*} [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
    [st : SpatialTrace Loc Time]
    {P : Path Loc → Prop} (hP : CUM P) :
    @CUM _ cem.evSemilatticeSup (P ∘ st.σ) :=
  SpatialTrace.unbounded_path_atelic hP

end MovementRelations

end Semantics.Events
