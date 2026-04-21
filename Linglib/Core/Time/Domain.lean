import Linglib.Core.Time.Allen
import Linglib.Core.Time.Orientation

/-!
# Temporal Domains
@cite{declerck-2006} @cite{reichenbach-1947}

A **temporal domain**: a central **time of orientation** (TO) — the
binding TO of the domain — together with related sub-TOs. The same
shape covers @cite{reichenbach-1947}'s S/P/R/E and Declerck's
binding-TO + sub-TOs; a `Domain` is what they share.

## Concepts

- **TO** (`Time of orientation`): a temporal anchor. Realized as
  `Interval Time`; degenerate intervals (`start = finish`) model point
  times like Reichenbach's S/P/R/E, while non-degenerate intervals
  model extended times-of-situation (Declerck's T-sit).
- **NamedTO**: a TO together with a typed `Role` label. The `Role` is
  abstract (any `DecidableEq` type), so role-based access stays
  type-safe across frameworks: `Orientation` (the canonical
  universal vocabulary) instantiates `Role` for both Reichenbach and
  Declerck, but a domain-specific framework could use its own enum.
- **Domain**: a central NamedTO + list of sub-NamedTOs. Pairwise Allen
  relations are *computed* from the underlying linear order on `Time`
  via `Interval.allenRel`; the domain does not store a relation table.

## What's not here

This file is foundational: it does **not** add tense semantics, aspect,
or sector classification. `Domain` is the substrate; the
domain-shaped theories build on top.
-/

namespace Core.Time

-- ════════════════════════════════════════════════════
-- § Times of Orientation
-- ════════════════════════════════════════════════════

/-- A **time of orientation** (TO, @cite{declerck-2006}): a temporal
    anchor used by tense/aspect frameworks. Realized as
    `Interval Time` so the same type covers both point times
    (degenerate intervals via `Interval.point`) and extended
    times-of-situation (general intervals).

    Allen relations between TOs are unique on **non-degenerate** pairs
    (`AllenRelation.holds_unique`), so Domain APIs that depend on
    uniqueness add a non-degeneracy hypothesis where needed. For
    point-time TOs (Reichenbach), the Allen algebra collapses to
    `{precedes, equal, precededBy}`. -/
abbrev TO (Time : Type*) [LinearOrder Time] := Interval Time

/-- Construct a point TO from a single time (degenerate interval). -/
abbrev TO.point {Time : Type*} [LinearOrder Time] (t : Time) : TO Time :=
  Interval.point t

/-- A TO with an identifying typed role label. The `Role` parameter is
    abstract: framework-specific role types (`Orientation` for
    Reichenbach/Declerck; framework-private enums elsewhere) all
    instantiate it. Using a typed role rather than a `String` makes
    role mismatches a compile-time error. -/
structure NamedTO (Time : Type*) (Role : Type*) [LinearOrder Time] where
  /-- The role label (e.g. `Orientation.perspective`, `.topic`). -/
  name : Role
  /-- The TO itself. -/
  span : TO Time

namespace NamedTO

variable {Time : Type*} {Role : Type*} [LinearOrder Time]

/-- The starting time of a NamedTO. -/
abbrev start (n : NamedTO Time Role) : Time := n.span.start

/-- The ending time of a NamedTO. -/
abbrev finish (n : NamedTO Time Role) : Time := n.span.finish

/-- Build a point NamedTO from a label and a single time. -/
def ofPoint (name : Role) (t : Time) : NamedTO Time Role where
  name := name
  span := TO.point t

end NamedTO

-- ════════════════════════════════════════════════════
-- § Domain
-- ════════════════════════════════════════════════════

/-- A **temporal domain** (@cite{declerck-2006}): a central time of
    orientation (the *binding TO* of the domain) together with a list
    of related sub-TOs. The Allen relations between any pair of TOs
    are computed on-demand from the underlying linear order on `Time`
    via `Interval.allenRel`; no relation table is stored.

    Two design choices worth noting:

    1. **No relation storage.** TOs are intervals on a `LinearOrder`,
       so their Allen relation is determined by the order. Storing
       relations would either be redundant (when consistent with the
       order) or contradictory (when inconsistent). We compute on
       demand.

    2. **NamedTO list, not record.** Different domain-shaped theories
       use different role-sets: Reichenbach has 4 roles (S/P/R/E),
       Declerck has a variable count (T₀ + sectors + sub-TOs). A
       label-keyed list lets `Domain` cover both without tying the
       structure to one role-set; downstream wrappers
       (`ReichenbachFrame`, `DeclercianSchema`) commit to a fixed
       role-set on top.

    `ReichenbachFrame` is recast as a `Domain` with central = S (point)
    and sub-TOs = [P, R, E] (each a point); `DeclercianSchema` is recast
    as a `Domain` plus a `Zone`-classifier function. -/
structure Domain (Time : Type*) (Role : Type*) [LinearOrder Time] where
  /-- The central TO — the binding TO of the domain. For matrix
      clauses this is typically speech time (S); under attitude
      embedding it shifts to the matrix event time. -/
  central : NamedTO Time Role
  /-- The other TOs in the domain (reference times, event times,
      sub-TOs, secondary anchors, …). -/
  subTOs : List (NamedTO Time Role)

namespace Domain

variable {Time : Type*} {Role : Type*} [LinearOrder Time]

/-- All TOs in the domain (central first, then sub-TOs). -/
def all (d : Domain Time Role) : List (NamedTO Time Role) :=
  d.central :: d.subTOs

@[simp] theorem all_central (d : Domain Time Role) :
    d.central ∈ d.all := List.mem_cons_self

@[simp] theorem all_sub (d : Domain Time Role) (t : NamedTO Time Role)
    (h : t ∈ d.subTOs) : t ∈ d.all := List.mem_cons_of_mem _ h

/-- Look up a TO by its role label. Returns `none` if no TO has that
    role; `some` of the *first* matching TO otherwise. (Roles are not
    required to be unique at the type level — a wrapper like
    `ReichenbachFrame` can prove uniqueness as a separate invariant.) -/
def find? [DecidableEq Role] (d : Domain Time Role) (r : Role) : Option (TO Time) :=
  ((d.all).find? (·.name == r)).map (·.span)

/-- The role label of every TO in the domain — useful for stating
    role-set invariants. -/
def labels (d : Domain Time Role) : List Role :=
  d.all.map (·.name)

/-- "TO `i` is related to TO `j` by some atom in the named set `S`."
    Lifts `AllenRelation.holdsIn` to the domain level. -/
def relatedBy (S : List AllenRelation) (i j : TO Time) : Prop :=
  AllenRelation.holdsIn S i j

/-- Lookup-and-relate: do the two role-labelled TOs both exist in the
    domain and stand in some atom of `S`? Used to phrase tense
    predicates like "topic precedes perspective" against a domain by
    role. -/
def relatedByName [DecidableEq Role] (d : Domain Time Role)
    (S : List AllenRelation) (rI rJ : Role) : Prop :=
  ∃ (i j : TO Time), d.find? rI = some i ∧ d.find? rJ = some j ∧
    relatedBy S i j

end Domain

-- ════════════════════════════════════════════════════
-- § Builders for the Common Reichenbach Role-Set
-- ════════════════════════════════════════════════════

/-! Convenience constructors for the canonical Reichenbach role-set,
    using `Orientation` as the universal `Role` type:
    `utterance` = S, `perspective` = P, `topic` = R, `situation` = E. -/

namespace Domain

variable {Time : Type*} [LinearOrder Time]

/-- The four canonical Reichenbach role labels (extended with
    @cite{kiparsky-2002}'s perspective time P) as `Orientation`
    values: utterance (S), perspective (P), topic (R), situation (E). -/
def reichenbachLabels : List Orientation :=
  [.utterance, .perspective, .topic, .situation]

/-- Build a domain from four point times in the Reichenbach convention.
    `S`/`P`/`R`/`E` map to `.utterance`/`.perspective`/`.topic`/`.situation`. -/
def ofReichenbachPoints (S P R E : Time) : Domain Time Orientation where
  central := NamedTO.ofPoint .utterance S
  subTOs := [NamedTO.ofPoint .perspective P,
             NamedTO.ofPoint .topic R,
             NamedTO.ofPoint .situation E]

@[simp] theorem ofReichenbachPoints_labels (S P R E : Time) :
    (ofReichenbachPoints S P R E).labels = reichenbachLabels := rfl

@[simp] theorem ofReichenbachPoints_findUtterance (S P R E : Time) :
    (ofReichenbachPoints S P R E).find? .utterance = some (TO.point S) := rfl

@[simp] theorem ofReichenbachPoints_findPerspective (S P R E : Time) :
    (ofReichenbachPoints S P R E).find? .perspective = some (TO.point P) := rfl

@[simp] theorem ofReichenbachPoints_findTopic (S P R E : Time) :
    (ofReichenbachPoints S P R E).find? .topic = some (TO.point R) := rfl

@[simp] theorem ofReichenbachPoints_findSituation (S P R E : Time) :
    (ofReichenbachPoints S P R E).find? .situation = some (TO.point E) := rfl

end Domain

end Core.Time
