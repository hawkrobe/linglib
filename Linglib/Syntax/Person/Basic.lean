module

public import Mathlib.Tactic.DeriveFintype

/-!
# Person — the canonical inventory
[cysouw-2003] [harbour-2016] [siewierska-2004]

The root-namespace `Person` type is the canonical, analytical person
inventory: the values languages' person systems distinguish, with
clusivity folded in as person values. [harbour-2016]'s quadripartition
(first exclusive / first inclusive / second / third) and the plain
tripartition (first / second / third) coexist as inventory values —
plain `first` is the tripartition cell (English *we*), related to the
clusivity-marked cells by `coarsen`, exactly as `Number.dual` relates to
`Number.plural` under coarsening. `zero` is the impersonal person (UD
`Person=0`; Finnish-type impersonals).

The Universal Dependencies tags corpora annotate have no clusivity, so realization
collapses the quadripartition cells to the first person (`Morphology/Word/UD.lean`).

This mirrors the `Number` API (`Syntax/Number/Basic.lean`): canonical
analytical inventory at root namespace, unified resolution (`Syntax/Person/Resolve.lean`),
the referential categories (`Syntax/Person/Category.lean`), the feature decomposition
(`Syntax/Person/Features.lean`) and the marking types of the first
person complex (`Syntax/Person/Clusivity.lean`).

`Person.prominence` is the graded prominence scale over this
inventory, consumed by person-hierarchy and scenario-split accounts.
-/

@[expose] public section

/-- Grammatical person — the canonical analytical inventory. Clusivity
    is a person-value distinction ([cysouw-2003]; [harbour-2016]'s
    quadripartition), not an orthogonal feature: `firstInclusive` and
    `firstExclusive` sit alongside the tripartition cell `first`. -/
inductive Person where
  /-- First person, clusivity-unmarked: the tripartition cell
      (English *we*). -/
  | first
  /-- First person inclusive: includes the addressee (Indonesian
      *kita*). -/
  | firstInclusive
  /-- First person exclusive: excludes the addressee (Indonesian
      *kami*). -/
  | firstExclusive
  /-- Second person: addressee, not speaker. -/
  | second
  /-- Third person: neither speaker nor addressee. -/
  | third
  /-- Impersonal/generic person (UD `Person=0`; Finnish-type
      impersonals). -/
  | zero
  deriving DecidableEq, Repr, Fintype

namespace Person

/-! ### Predicates -/

/-- The referent includes the speaker. -/
def IncludesSpeaker : Person → Prop
  | .first | .firstInclusive | .firstExclusive => True
  | _ => False

instance : DecidablePred IncludesSpeaker := fun p =>
  match p with
  | .first | .firstInclusive | .firstExclusive => isTrue trivial
  | .second | .third | .zero => isFalse fun h => h

/-- The value marks clusivity (a quadripartition cell). -/
def MarksClusivity : Person → Prop
  | .firstInclusive | .firstExclusive => True
  | _ => False

instance : DecidablePred MarksClusivity := fun p =>
  match p with
  | .firstInclusive | .firstExclusive => isTrue trivial
  | .first | .second | .third | .zero => isFalse fun h => h

/-- Speech-act participant: speaker or addressee included. `zero` is
    not a participant value. -/
def IsSAP : Person → Prop
  | .third | .zero => False
  | _ => True

instance : DecidablePred IsSAP := fun p =>
  match p with
  | .first | .firstInclusive | .firstExclusive | .second => isTrue trivial
  | .third | .zero => isFalse fun h => h

/-! ### Coarsening

The quadripartition cells coarsen to the tripartition cell, as
`Number.dual` coarsens to `Number.plural`: a clusivity-less system
realizes both inclusive and exclusive referents as plain `first`. -/

/-- Collapse clusivity: the tripartition image of each value. -/
def coarsen : Person → Person
  | .firstInclusive | .firstExclusive => .first
  | p => p

@[simp] theorem coarsen_idempotent (p : Person) :
    p.coarsen.coarsen = p.coarsen := by cases p <;> rfl

/-- Coarsening erases exactly the clusivity marking. -/
theorem coarsen_eq_self_iff (p : Person) :
    p.coarsen = p ↔ ¬MarksClusivity p := by
  cases p <;> simp [coarsen, MarksClusivity]

/-- The person hierarchy 1 < 2 < 3 ([zwicky-1977b]; resolution in
    coordination, [corbett-2006]). Clusivity-marked firsts share rank 0
    with `first`; `zero` sits outside the hierarchy (sentinel rank 3). -/
def hierarchyRank : Person → Nat
  | .first | .firstInclusive | .firstExclusive => 0
  | .second => 1
  | .third => 2
  | .zero => 3

/-! ### Person systems -/

/-- A language's person system: the analytical values its paradigms
    distinguish ([cysouw-2003]; the paradigm-level marking typology is
    `Person.Clusivity`, his Table 3.2). -/
structure System where
  /-- The person values the system distinguishes. -/
  values : List Person
  deriving DecidableEq, Repr

/-- Graded person prominence: 1st (2) > 2nd (1) > 3rd (0). The
    load-bearing cut is locuphoric (1st/2nd) > aliophoric (3rd) —
    [haspelmath-2021]'s person scale (8a); the ranking of 1st over 2nd
    within the locuphoric zone follows the person-hierarchy tradition and
    varies across languages. Clusivity-marked firsts rank with `first`;
    the impersonal `zero` is `[−participant]` and ranks with third. -/
def prominence : Person → Nat
  | .first | .firstInclusive | .firstExclusive => 2
  | .second => 1
  | .third | .zero => 0

namespace System

/-- The system marks clusivity. -/
def HasClusivity (ns : System) : Prop :=
  .firstInclusive ∈ ns.values ∨ .firstExclusive ∈ ns.values

instance : DecidablePred HasClusivity := fun ns => by
  unfold HasClusivity; infer_instance

/-- The English-type tripartition. -/
def tripartition : System := ⟨[.first, .second, .third]⟩

/-- The Indonesian/Tagalog-type quadripartition ([harbour-2016]). -/
def quadripartition : System :=
  ⟨[.firstInclusive, .firstExclusive, .second, .third]⟩

theorem tripartition_no_clusivity : ¬tripartition.HasClusivity := by
  decide

theorem quadripartition_clusivity : quadripartition.HasClusivity := by
  decide

end System

end Person
