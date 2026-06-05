import Linglib.Data.UD.Basic

/-!
# Person — the canonical inventory
[cysouw-2009] [harbour-2016] [siewierska-2004]

The root-namespace `Person` type is the canonical, analytical person
inventory: the values languages' person systems distinguish, with
clusivity folded in as person values. [harbour-2016]'s quadripartition
(first exclusive / first inclusive / second / third) and the plain
tripartition (first / second / third) coexist as inventory values —
plain `first` is the tripartition cell (English *we*), related to the
clusivity-marked cells by `coarsen`, exactly as `Number.dual` relates to
`Number.plural` under coarsening. `zero` is the impersonal person (UD
`Person=0`; Finnish-type impersonals).

`UD.Person` (`Data/UD/Basic.lean`) is the *realization* vocabulary —
what corpora annotate — reachable by `toUD`/`fromUD`. UD has no
clusivity, so `toUD` collapses the quadripartition cells to `.first`
(`ud_conflates_clusivity`); the analytical values are not recoverable
from UD alone.

This mirrors the `Number` API (`Features/Number/Basic.lean`): canonical
analytical inventory at root namespace, UD demoted to realization,
capability mixin (`Features/Person/Capabilities.lean`), unified
resolution (`Features/Person/Resolve.lean`), feature decomposition and
the Cysouw categories (`Features/Person/Decomposition.lean`).

The prominence scale over this inventory (`Person.prominence`, the
dissolved `Person`'s role) lives in `Features/Prominence.lean`.
-/

set_option autoImplicit false

/-- Grammatical person — the canonical analytical inventory. Clusivity
    is a person-value distinction ([cysouw-2009]; [harbour-2016]'s
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

/-! ### UD realization vocabulary -/

/-- Realize as UD annotation: clusivity collapses to `Person=1`. -/
def toUD : Person → UD.Person
  | .first | .firstInclusive | .firstExclusive => .first
  | .second => .second
  | .third => .third
  | .zero => .zero

/-- Analytical value of a UD annotation. Total: UD's vocabulary is a
    coarsening of the analytical inventory. -/
def fromUD : UD.Person → Person
  | .first => .first
  | .second => .second
  | .third => .third
  | .zero => .zero

/-- UD round-trips on its own image. -/
@[simp] theorem toUD_fromUD (u : UD.Person) : (fromUD u).toUD = u := by
  cases u <;> rfl

/-- The analytical inventory does not round-trip through UD: clusivity
    has no UD image. `fromUD ∘ toUD` is `coarsen`. -/
theorem fromUD_toUD (p : Person) : fromUD p.toUD = p.coarsen := by
  cases p <;> rfl

/-- UD conflates the clusivity values under `Person=1`. -/
theorem ud_conflates_clusivity :
    Person.firstInclusive.toUD = Person.firstExclusive.toUD := rfl

/-- The person hierarchy 1 < 2 < 3 ([zwicky-1977]; resolution in
    coordination, [corbett-2006]). Clusivity-marked firsts share rank 0
    with `first`; `zero` sits outside the hierarchy (sentinel rank 3). -/
def hierarchyRank : Person → Nat
  | .first | .firstInclusive | .firstExclusive => 0
  | .second => 1
  | .third => 2
  | .zero => 3

/-! ### Person systems -/

/-- A language's person system: the analytical values its paradigms
    distinguish ([cysouw-2009]; the paradigm-level marking typology is
    `Features.Clusivity.System`, his Table 3.2). -/
structure System where
  /-- The person values the system distinguishes. -/
  values : List Person
  deriving DecidableEq, Repr

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

/-- **Addressee inclusion implication I** at the value level
    ([cysouw-2009] (3.23), Fig 3.8): a distinguished exclusive requires a
    distinguished inclusive. The converse fails — only-inclusive systems
    (his (Pc), Maká) have an inclusive value whose exclusive is covered
    by the singular morpheme. (Over the common paradigm types; the rare
    Binandere pattern, his (3.22)/(Pj), is the noted incidental
    exception.) -/
def ExclusiveImpliesInclusive (ns : System) : Prop :=
  .firstExclusive ∈ ns.values → .firstInclusive ∈ ns.values

instance : DecidablePred ExclusiveImpliesInclusive := fun ns => by
  unfold ExclusiveImpliesInclusive; infer_instance

theorem tripartition_exclImpliesIncl :
    tripartition.ExclusiveImpliesInclusive := by decide

theorem quadripartition_exclImpliesIncl :
    quadripartition.ExclusiveImpliesInclusive := by decide

end System

end Person
