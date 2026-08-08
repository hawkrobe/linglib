import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Basic

/-!
# Discourse Representation Structures (faithful, model-theoretic core)

A faithful Lean model of the canonical DRS data type, built on mathlib's
`FirstOrder.Language` so its semantics can be given model-theoretically (via
`FirstOrder.Language.Structure` / `Realize`), exactly as [kamp-reyle-1993]
define it (verifying embeddings into a model, Def. 1.4.4–1.4.5).

A DRS is a pair `⟨referents, conditions⟩` (Def. 1.4.1): `referents` is the
*universe* `U` — a finite set of discourse referents — and `conditions` a
collection of DRS-conditions. Conditions are **atomic** (`rel`, `eq`) or
**complex**; sub-DRSs occur *only* inside complex conditions. Def. 1.4.1's only
complex condition is `neg`; `imp` and `dis` are its Chapter 2 extension
(conditionals and disjunction). Relation symbols come arity-indexed from a
`FirstOrder.Language`.

"Box" and "DRS" name the same object in the literature — the two-compartment
diagram, [muskens-1996]'s linear `[u₁ … uₙ | γ₁ … γₘ]` — in diagrammatic vs.
official register. Here `Box` is the generic shell that DRT variants
re-instantiate at their condition types (Layered DRT's LDRSs), and `DRS` its
instantiation at `Condition L V`.

## Main declarations

* `Box`, `Condition L V`, `DRS L V` — the data type over a language `L`
  (relation signature) and discourse-referent type `V`: a DRS is a `Box` of
  `Condition`s.
* `DRS.merge` — the `⊕` operation (set-union referents, concatenate
  conditions); [muskens-1996]'s compositional operation.
* `DirectlySubordinate`, `Subordinate`, `WeakSubordinate` — immediate
  subordination (Def. 1.4.10(i), extended to `⇒`/`∨` in Ch. 2) and its
  `Relation.TransGen` / `ReflTransGen` closures (Def. 1.4.10(ii)). Accessibility
  (Def. 1.4.11) is host-relative and lives in `DRS/Basic.lean` (`accessibleFrom`).

## Implementation notes

* `referents` is the textbook "universe `U`"; named for its contents because
  `universe` is a Lean keyword and `univ` collides with `Finset.univ`.
* No mutual block: `Box` is a parameterized container structure the condition
  syntax nests through, and `DRS` its instantiation at `Condition L V` — the
  simultaneous Def. 1.4.1 rendered as nesting, with the structure API
  (projections, `ext`, eta) for free.
* The recursive `conditions` field is a `List`: Lean forbids nesting an inductive
  through `Finset`/`Multiset`. Set semantics are imposed by the interpretation
  (`Embedding.verifies_perm`, `DRS/Verification.lean`).
* `DRT` is the owning namespace (mathlib's `FirstOrder.Language` pattern):
  `DRS`, `Condition`, and `Ctx` are DRT's objects, keeping generic names
  owner-relative rather than claiming them at the root.
-/

open FirstOrder

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w}

/-- A DRT *box*, generic over the condition type `C`; `DRS` instantiates `C`
at `Condition L V`. -/
@[ext] structure Box (V : Type w) (C : Type x) where
  /-- The universe `U`: the discourse referents the box introduces. -/
  referents : Finset V
  /-- The box's conditions. -/
  conditions : List C

/-- A DRS-condition: atomic (`rel`, `eq`) or complex — `neg` per Def. 1.4.1,
`imp`/`dis` per its Chapter 2 extension. Sub-DRSs occur only inside complex
conditions. -/
inductive Condition (L : Language.{u, v}) (V : Type w) where
  /-- Atomic condition: `n`-ary relation symbol `R` applied to referents `args`. -/
  | rel {n : ℕ} (R : L.Relations n) (args : Fin n → V)
  /-- Atomic equality condition `u = v`. -/
  | eq (u v : V)
  /-- Complex condition `¬K`. -/
  | neg (K : Box V (Condition L V))
  /-- Complex condition `K₁ ⇒ K₂` (antecedent ⇒ consequent). -/
  | imp (ante cons : Box V (Condition L V))
  /-- Complex condition `K₁ ∨ K₂`. -/
  | dis (left right : Box V (Condition L V))

/-- A discourse representation structure consists of two parts: a universe of
discourse referents, which represent the objects under discussion, and the
DRS-conditions, which encode the information that has accumulated on them
(Def. 1.4.1). -/
abbrev DRS (L : Language.{u, v}) (V : Type w) := Box V (Condition L V)

namespace DRS

@[simp] theorem referents_mk (u : Finset V) (c : List (Condition L V)) :
    (Box.mk u c).referents = u := rfl

@[simp] theorem conditions_mk (u : Finset V) (c : List (Condition L V)) :
    (Box.mk u c).conditions = c := rfl

/-- A condition of a DRS is smaller than the DRS — the recursion measure for
definitions descending through the nested `List (Condition L V)`. -/
theorem sizeOf_lt_of_mem_conditions {K : DRS L V} {c : Condition L V}
    (h : c ∈ K.conditions) : sizeOf c < sizeOf K := by
  obtain ⟨U, conds⟩ := K
  have : sizeOf c < sizeOf conds := List.sizeOf_lt_of_mem h
  simp only [Box.mk.sizeOf_spec]
  omega

-- Registers the `Box`-through-`List` nesting step with the default termination
-- tactic: recursions descending into a box's conditions need no `decreasing_by`.
macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| have := DRS.sizeOf_lt_of_mem_conditions (by assumption); omega)

/-- The empty DRS `⟨∅, []⟩`. -/
def empty : DRS L V := .mk ∅ []

instance : Inhabited (DRS L V) := ⟨empty⟩

/-- Merge `⊕`: set-union the referents, concatenate the conditions. The binary
DRS merge is Muskens's compositional operation — Kamp & Reyle themselves
combine DRSs incrementally via the construction algorithm, not a symmetric
binary `⊕`. An operation, not a syntactic constructor. -/
def merge [DecidableEq V] (K₁ K₂ : DRS L V) : DRS L V :=
  .mk (K₁.referents ∪ K₂.referents) (K₁.conditions ++ K₂.conditions)

@[simp] theorem referents_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    (K₁.merge K₂).referents = K₁.referents ∪ K₂.referents := rfl

@[simp] theorem conditions_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    (K₁.merge K₂).conditions = K₁.conditions ++ K₂.conditions := rfl

end DRS

/-- Induction on conditions, descending into sub-boxes: to prove `motive c` for
every condition, handle each constructor given the motive for every condition
of its sub-boxes. -/
@[induction_eliminator] theorem Condition.induction {motive : Condition L V → Prop}
    (rel : ∀ {n : ℕ} (R : L.Relations n) (args : Fin n → V), motive (.rel R args))
    (eq : ∀ u v, motive (.eq u v))
    (neg : ∀ K, (∀ c ∈ K.conditions, motive c) → motive (.neg K))
    (imp : ∀ a c, (∀ d ∈ a.conditions, motive d) → (∀ d ∈ c.conditions, motive d) →
      motive (.imp a c))
    (dis : ∀ l r, (∀ d ∈ l.conditions, motive d) → (∀ d ∈ r.conditions, motive d) →
      motive (.dis l r)) : ∀ c, motive c
  | .rel R args => rel R args
  | .eq u v => eq u v
  | .neg K => neg K fun c _ => Condition.induction rel eq neg imp dis c
  | .imp a c => imp a c (fun d _ => Condition.induction rel eq neg imp dis d)
      (fun d _ => Condition.induction rel eq neg imp dis d)
  | .dis l r => dis l r (fun d _ => Condition.induction rel eq neg imp dis d)
      (fun d _ => Condition.induction rel eq neg imp dis d)

/-! ### Subordination -/

/-- One-step subordination: `DirectlySubordinate K' K` says `K'` is *directly
subordinate* to `K` — the `neg` case per Def. 1.4.10(i), the `⇒`/`∨` cases per
its Chapter 2 extension. A relation on DRS values, where the textbook's is on
box occurrences: on a degenerate `imp a a` the consequent edge makes `a`
subordinate to itself. -/
inductive DirectlySubordinate : DRS L V → DRS L V → Prop where
  /-- The body of a `¬` is directly subordinate to the containing DRS. -/
  | neg {D K : DRS L V} : Condition.neg K ∈ D.conditions → DirectlySubordinate K D
  /-- The antecedent of a `⇒` is directly subordinate to the containing DRS. -/
  | impAnte {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate a D
  /-- The consequent of a `⇒` is directly subordinate to its *antecedent* — the
  asymmetry that makes antecedent referents accessible in the consequent. -/
  | impCons {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate c a
  /-- The left disjunct of a `∨` is directly subordinate to the containing DRS. -/
  | disL {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate l D
  /-- The right disjunct of a `∨` is directly subordinate to the containing DRS. -/
  | disR {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate r D

/-- The `<` of Def. 1.4.10(ii): the transitive closure of `DirectlySubordinate`.
Accessibility (`accessibleFrom`, `DRS/Basic.lean`) is host-relative and does
not build on this closure. -/
abbrev Subordinate : DRS L V → DRS L V → Prop :=
  Relation.TransGen DirectlySubordinate

/-- The `≤` of Def. 1.4.10(ii): the reflexive-transitive closure of
`DirectlySubordinate`. -/
abbrev WeakSubordinate : DRS L V → DRS L V → Prop :=
  Relation.ReflTransGen DirectlySubordinate

end DRT
