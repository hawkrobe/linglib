import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation

/-!
# Discourse Representation Structures (faithful core)
@cite{kamp-reyle-1993}

A faithful Lean model of the canonical DRS data type. Following Kamp & Reyle, a
DRS is a pair `⟨referents, conditions⟩`: `referents` is the *universe* `U` — a
finite set of discourse referents — and `conditions` a collection of
DRS-conditions. Conditions are **atomic** (`rel`, `eq`) or **complex** (`neg`,
`imp`, `dis`), and — crucially — sub-DRSs occur *only* inside complex conditions.
Merge is an *operation*, not a constructor, and accessibility is the declarative
"left and up" relation.

This replaces the legacy flat encoding (`Boxes/Syntax.lean`), in which atoms were
themselves DRSs, `box`/`seq` were constructors, and accessibility was a
first-match `List` walk.

## Main declarations

* `DRS R V`, `Condition R V` — the mutual data type (drefs `V`, relations `R`).
* `DRS.merge` — the `⊕` operation (set-union referents, concatenate conditions).
* `DirectlySubordinate`, `Subordinate`, `WeakSubordinate` — the one-step
  subordination relation and its `Relation.TransGen` / `ReflTransGen` closures.
* `Accessible` — a dref is accessible at a sub-DRS iff it lies in the referents of
  some weakly-superordinate DRS.

## Implementation notes

* `referents` is the textbook "universe `U`"; named for its contents because
  `universe` is a Lean keyword and `univ` collides with `Finset.univ` (the
  complete set of a `Fintype` — the opposite of a DRS universe, which is a finite
  *subset* of an arbitrary referent type, needing no `Fintype`).
* The recursive `conditions` field is a `List`: Lean forbids nesting an inductive
  through `Finset`/`Multiset`. Set semantics (order and duplication irrelevance)
  are the responsibility of the interpretation, not the syntax.
* The namespace is transitional `DRT` while the legacy `_root_.DRS`
  (`Boxes/Syntax.lean`) is migrated out; it promotes to the root namespace once
  the legacy type is retired.
-/

namespace DRT

universe u v

mutual
/-- A discourse representation structure: the pair `⟨referents, conditions⟩`
(@cite{kamp-reyle-1993}). `referents` is the universe `U` (a finite set of
discourse referents); `conditions` the DRS-conditions. -/
inductive DRS (R : Type u) (V : Type v) where
  | mk (referents : Finset V) (conditions : List (Condition R V))
/-- A DRS-condition: atomic (`rel`, `eq`) or complex (`neg`, `imp`, `dis`).
Sub-DRSs occur only inside complex conditions. -/
inductive Condition (R : Type u) (V : Type v) where
  /-- Atomic condition: relation symbol `r` applied to `args`. -/
  | rel (r : R) (args : List V)
  /-- Atomic equality condition `u = v`. -/
  | eq (u v : V)
  /-- Complex condition `¬K`. -/
  | neg (K : DRS R V)
  /-- Complex condition `K₁ ⇒ K₂` (antecedent ⇒ consequent). -/
  | imp (ante cons : DRS R V)
  /-- Complex condition `K₁ ∨ K₂`. -/
  | dis (left right : DRS R V)
end

namespace DRS

variable {R : Type u} {V : Type v}

/-- The referents (universe `U`) of a DRS — the discourse referents it introduces. -/
def referents : DRS R V → Finset V
  | .mk u _ => u

/-- The conditions of a DRS. -/
def conditions : DRS R V → List (Condition R V)
  | .mk _ c => c

@[simp] theorem referents_mk (u : Finset V) (c : List (Condition R V)) :
    (DRS.mk u c).referents = u := rfl

@[simp] theorem conditions_mk (u : Finset V) (c : List (Condition R V)) :
    (DRS.mk u c).conditions = c := rfl

/-- The empty DRS `⟨∅, []⟩`. -/
def empty : DRS R V := .mk ∅ []

/-- Merge (Kamp & Reyle's `⊕`): set-union the referents, concatenate the
conditions. An *operation*, not a syntactic constructor. -/
def merge [DecidableEq V] (K₁ K₂ : DRS R V) : DRS R V :=
  .mk (K₁.referents ∪ K₂.referents) (K₁.conditions ++ K₂.conditions)

@[simp] theorem merge_referents [DecidableEq V] (K₁ K₂ : DRS R V) :
    (K₁.merge K₂).referents = K₁.referents ∪ K₂.referents := rfl

@[simp] theorem merge_conditions [DecidableEq V] (K₁ K₂ : DRS R V) :
    (K₁.merge K₂).conditions = K₁.conditions ++ K₂.conditions := rfl

end DRS

/-! ### Subordination and accessibility -/

/-- One-step subordination ("`K'` is *directly subordinate* to `K`"), with
exactly the canonical edges (@cite{kamp-reyle-1993}, Def. 2.1.2):

* the body of a `¬` is subordinate to the containing DRS;
* the antecedent of a `⇒` is subordinate to the containing DRS;
* the consequent of a `⇒` is subordinate to its *antecedent* (the ⇒ asymmetry:
  antecedent drefs are accessible in the consequent, not conversely);
* each disjunct of a `∨` is subordinate to the containing DRS. -/
inductive DirectlySubordinate {R : Type u} {V : Type v} : DRS R V → DRS R V → Prop where
  | neg {D K : DRS R V} : Condition.neg K ∈ D.conditions → DirectlySubordinate K D
  | impAnte {D a c : DRS R V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate a D
  | impCons {D a c : DRS R V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate c a
  | disL {D l r : DRS R V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate l D
  | disR {D l r : DRS R V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate r D

/-- `K₁ < K₂`: `K₁` is subordinate to `K₂` — the transitive closure of
`DirectlySubordinate`. -/
abbrev Subordinate {R : Type u} {V : Type v} : DRS R V → DRS R V → Prop :=
  Relation.TransGen DirectlySubordinate

/-- `K₁ ≤ K₂`: `K₁` is weakly subordinate to `K₂` — the reflexive-transitive
closure of `DirectlySubordinate`. -/
abbrev WeakSubordinate {R : Type u} {V : Type v} : DRS R V → DRS R V → Prop :=
  Relation.ReflTransGen DirectlySubordinate

/-- A discourse referent `u` is *accessible* at a sub-DRS `K` iff it lies in the
referents of `K` itself or of some DRS weakly-superordinate to `K` — the "left
and up" geometry. -/
def Accessible {R : Type u} {V : Type v} (u : V) (K : DRS R V) : Prop :=
  ∃ D, WeakSubordinate K D ∧ u ∈ D.referents

end DRT
