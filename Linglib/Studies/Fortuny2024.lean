import Linglib.Syntax.Tree.Cat
import Linglib.Syntax.Category.Coordinator

/-!
# [fortuny-2024] — Deducing the Coordinand Constraint

Fortuny, Jordi. 2024. Deducing the Coordinand Constraint. *Linguistic Inquiry*
55(2). 219–253.

Grosu (1973) decomposes Ross's (1967) Coordinate Structure Constraint into the
**Coordinand Constraint** (CC: *no coordinand may be moved*) and the Element
Constraint. Fortuny gives a **categorematic** definition of the coordinator —
`Coord : (X/X)/X` in Categorial Grammar, requiring the two coordinands and the
coordinate structure to be *categorially identical* (the Parallelism Requirement /
Law of Coordination of Likes) — and *deduces* the CC from it.

Relation to the `Coordinator` API. The CC and the semantic `Coordinator.op` are two
*sibling realizations* of the **categorematic schema** `Coord : (X/X)/X` (combine two
same-`X` constituents into `X`): `op : α → α → α` realizes it over Boolean-algebra
*types*, this file realizes it over syntactic *categorial features* — they share the
schema, not a Lean object (`op` lives over `[BooleanAlgebra α]`; categories are not a
Boolean algebra, and the criterial `[wh]`/`[focus]`/`[topic]` features that drive the
CC have no semantic-`op` counterpart). The genuine API tie-in is Fortuny's own point
that **the CC is uniform across coordinator types** (his (3a–f): *and*/*or*/*but* all
obey it): `cc_uniform` quantifies over `Coordinator.Role`, and its proof ignores the
role — the precise content of "the CC is structural, not meaning-based."

## Main definitions

* `CatFeature` / `Category` — generalized categorial features (Fortuny (12), (18)–(20)).
* `Coordinable` — the Coordinability Condition (Fortuny (21)/(22)): categorial identity.
* `MovesFor` — a coordinand bears a criterial feature that triggers A-bar movement
  (Remark (23): the feature triggering internal Merge is categorial).

## Main results

* `cc_case1` — **Case 1** (§2.2.1): a single coordinand cannot be extracted. Moving one
  coordinand for a criterial feature the other lacks makes them categorially distinct,
  so they are not coordinable. Derived from the categorematic coordinator alone.
* `coordinand_extraction_illformed` — the CC stated over a coordinate structure.
-/

namespace Fortuny2024

open Syntax (Cat)

/-! ### Generalized categorial features (Fortuny (12), (18)–(20)) -/

/-- A **generalized categorial feature** (Fortuny (12)): a feature that determines a
    constituent's syntactic distribution. Beyond the base categories, the criterial
    A-bar features [wh]/[focus]/[topic] (Rizzi's cartography) are categorial features —
    they have distinctive syntactic distributions and trigger movement (Remark (23)). -/
inductive CatFeature where
  /-- A base categorial feature [D], [V], [C], … (Fortuny (14)). -/
  | base : Cat → CatFeature
  /-- The criterial [wh] feature (Wh-Criterion → Spec,ForceP). -/
  | wh
  /-- The criterial [focus] feature (Focus Criterion → Spec,FocP). -/
  | focus
  /-- The criterial [topic] feature (Topic Criterion → Spec,TopP). -/
  | topic
  deriving DecidableEq, Repr

/-- A constituent's **category** = its set of generalized categorial features
    (Fortuny (18)–(20): a category is a feature matrix). -/
abbrev Category := Finset CatFeature

/-- A criterial (A-bar movement-triggering) feature: [wh]/[focus]/[topic]. Base
    categories are not criterial. -/
def CatFeature.isCriterial : CatFeature → Bool
  | .wh | .focus | .topic => true
  | .base _ => false

/-! ### The Coordinability Condition (Fortuny (21)/(22)) -/

/-- **Coordinability Condition** (Fortuny (22), from the categorematic `Coord : (X/X)/X`
    (10) + categorial identity (21)): two constituents can be coordinated iff they are
    categorially identical. This is the Parallelism Requirement / Law of Coordination of
    Likes at the level of categorial features — the syntactic counterpart of the
    same-type requirement `op : α → α → α` encodes in its type signature. -/
def Coordinable (a b : Category) : Prop := a = b

instance (a b : Category) : Decidable (Coordinable a b) := decEq a b

/-- **Remark (23)**: the grammatical feature that triggers internal Merge (movement) is
    a categorial feature. So a coordinand that moves to satisfy a criterion bears that
    criterial feature *in its category*. -/
def MovesFor (a : Category) (f : CatFeature) : Prop := f ∈ a ∧ f.isCriterial

/-! ### Deriving the Coordinand Constraint, Case 1 (§2.2.1) -/

/-- **Coordinand Constraint, Case 1** (Fortuny §2.2.1, his (24)): a single coordinand
    cannot be syntactically extracted. If coordinand `a` moves for a criterial feature
    `f` (e.g. [wh]) that the other coordinand `b` lacks, then `a` and `b` carry different
    categorial features, hence are *not* coordinable. The ill-formedness follows from the
    categorematic coordinator (Coordinability) — no construction-specific island
    stipulation is needed. -/
theorem cc_case1 {a b : Category} {f : CatFeature}
    (hmove : MovesFor a f) (hb : f ∉ b) : ¬ Coordinable a b := by
  intro h
  exact hb (h ▸ hmove.1)

/-- A coordinate structure of two coordinands is well-formed only if they are
    coordinable (the categorematic `Coord` projects a single category `X`). -/
def WellFormedCoordination (a b : Category) : Prop := Coordinable a b

/-- The CC over a coordinate structure: extracting a single coordinand (moving `a` for a
    criterial feature the in-situ coordinand `b` lacks) makes the coordination
    ill-formed. -/
theorem coordinand_extraction_illformed {a b : Category} {f : CatFeature}
    (hmove : MovesFor a f) (hb : f ∉ b) : ¬ WellFormedCoordination a b :=
  cc_case1 hmove hb

/-- A coordinate structure: a coordinator with its role (`Coordinator.Role` from the
    API — conjunctive `.j`, disjunctive `.disj`, adversative `.advers`) combining two
    coordinands. -/
structure CoordStructure where
  role : Coordinator.Role
  left : Category
  right : Category

/-- The structure is well-formed only if the coordinands are coordinable (the
    categorematic `Coord` projects a single category `X`). -/
def CoordStructure.WellFormed (cs : CoordStructure) : Prop := Coordinable cs.left cs.right

/-- **The Coordinand Constraint is uniform across coordinator types** (Fortuny (3a–f):
    *How was Emma [how and/or/but sleepy]?* — *and*, *or*, and *but* all obey the CC).
    Extracting a single coordinand is ill-formed *regardless* of the coordinator's
    `Coordinator.Role`: the proof discharges the goal without inspecting `r`, which is
    exactly the claim that the CC falls out of the categorematic coordinator's
    parallelism, not the role's denotation. -/
theorem cc_uniform (r : Coordinator.Role) {a b : Category} {f : CatFeature}
    (hmove : MovesFor a f) (hb : f ∉ b) :
    ¬ CoordStructure.WellFormed ⟨r, a, b⟩ :=
  cc_case1 hmove hb

/-! ### Illustrations (§2.2.1.1–§2.2.1.2) -/

/-- (25) *Who did John kiss [who] and/or [a girl]? — the wh-moved coordinand `who` is
    `[+wh]`, the in-situ `a girl` is `[−wh]`; categorially distinct, so not coordinable. -/
example :
    ¬ Coordinable {.base (.proj .NOUN), .wh} {.base (.proj .NOUN)} :=
  cc_case1 (a := {.base (.proj .NOUN), .wh}) (f := .wh) ⟨by decide, by decide⟩ (by decide)

/-- (26)/(28) Focalization of a single coordinand (Catalan *LES PASTANAGUES, sembra i/o
    les mongetes*): the `[+focus]` coordinand and the `[−focus]` one are not coordinable.
    The same derivation covers conjunctive, disjunctive, and adversative coordination —
    the CC is uniform because it falls out of the categorematic coordinator, not of any
    one coordinator's meaning. -/
example :
    ¬ Coordinable {.base (.proj .NOUN), .focus} {.base (.proj .NOUN)} :=
  cc_case1 (f := .focus) ⟨by decide, by decide⟩ (by decide)

/-- The well-formed control: coordinating two categorially-identical (here `[−wh]`)
    coordinands *is* coordinable — nothing is extracted, so the parallelism holds. -/
example : Coordinable {.base (.proj .NOUN)} {.base (.proj .NOUN)} := rfl

/-! ### Case 2 and the Least Effort deduction (§2.2.2–§2.3) — TODO

Fortuny's full account adds two further factors for **Case 2** (why *both* coordinands
cannot move) and the ultimate deduction: an economy condition on movement (the Integrity
Condition on Coordinate Structures (50)) and an interface condition (the Prohibition
against Self-Coordination (71)), all derived from Chomsky's (1991) Least Effort
Principle. Case 1 above — the robust, crosslinguistically pervasive core of the CC —
follows from the categorematic coordinator alone; the Least Effort deduction of Cases 1+2
is the larger formalization, deferred. -/

end Fortuny2024
