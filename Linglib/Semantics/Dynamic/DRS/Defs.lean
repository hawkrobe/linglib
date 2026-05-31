import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Basic

/-!
# Discourse Representation Structures (faithful, model-theoretic core)
@cite{kamp-reyle-1993}

A faithful Lean model of the canonical DRS data type, built on mathlib's
`FirstOrder.Language` so its semantics can be given model-theoretically (via
`FirstOrder.Language.Structure` / `Realize`), exactly as Kamp & Reyle define it
(verifying embeddings into a model, Def. 1.4.4–1.4.5).

A DRS is a pair `⟨referents, conditions⟩` (Def. 1.4.1): `referents` is the
*universe* `U` — a finite set of discourse referents — and `conditions` a
collection of DRS-conditions. Conditions are **atomic** (`rel`, `eq`) or
**complex** (`neg`, `imp`, `dis`); sub-DRSs occur *only* inside complex
conditions. Relation symbols come arity-indexed from a `FirstOrder.Language`.

## Main declarations

* `DRS L V`, `Condition L V` — the mutual data type over a language `L` (relation
  signature) and discourse-referent type `V`.
* `DRS.merge` — the `⊕` operation (set-union referents, concatenate conditions).
* `DirectlySubordinate`, `Subordinate`, `WeakSubordinate` — immediate
  subordination (Def. 1.4.10(i), extended to `⇒`/`∨` in Ch. 2) and its
  `Relation.TransGen` / `ReflTransGen` closures (Def. 1.4.10(ii)). Accessibility
  (Def. 1.4.11) is host-relative and lives in `DRS/Basic.lean` (`accessibleFrom`).

## Implementation notes

* `referents` is the textbook "universe `U`"; named for its contents because
  `universe` is a Lean keyword and `univ` collides with `Finset.univ`.
* The recursive `conditions` field is a `List`: Lean forbids nesting an inductive
  through `Finset`/`Multiset`. Set semantics are imposed by the interpretation.
* The namespace is transitional `DRT` while the legacy `_root_.DRS` is migrated
  out; it promotes to the root namespace once the legacy type is retired.
-/

open FirstOrder

namespace DRT

universe u v w

mutual
/-- A discourse representation structure: the pair `⟨referents, conditions⟩`
(@cite{kamp-reyle-1993}, Def. 1.4.1). `referents` is the universe `U` (a finite
set of discourse referents); `conditions` the DRS-conditions. -/
inductive DRS (L : Language.{u, v}) (V : Type w) where
  | mk (referents : Finset V) (conditions : List (Condition L V))
/-- A DRS-condition (@cite{kamp-reyle-1993}, Def. 1.4.1): atomic (`rel`, `eq`) or
complex (`neg`, `imp`, `dis`). Sub-DRSs occur only inside complex conditions. -/
inductive Condition (L : Language.{u, v}) (V : Type w) where
  /-- Atomic condition: `n`-ary relation symbol `R` applied to referents `args`. -/
  | rel {n : ℕ} (R : L.Relations n) (args : Fin n → V)
  /-- Atomic equality condition `u = v`. -/
  | eq (u v : V)
  /-- Complex condition `¬K`. -/
  | neg (K : DRS L V)
  /-- Complex condition `K₁ ⇒ K₂` (antecedent ⇒ consequent). -/
  | imp (ante cons : DRS L V)
  /-- Complex condition `K₁ ∨ K₂`. -/
  | dis (left right : DRS L V)
end

namespace DRS

variable {L : Language.{u, v}} {V : Type w}

/-- The referents (universe `U`) of a DRS — the discourse referents it introduces. -/
def referents : DRS L V → Finset V
  | .mk u _ => u

/-- The conditions of a DRS. -/
def conditions : DRS L V → List (Condition L V)
  | .mk _ c => c

@[simp] theorem referents_mk (u : Finset V) (c : List (Condition L V)) :
    (DRS.mk u c).referents = u := rfl

@[simp] theorem conditions_mk (u : Finset V) (c : List (Condition L V)) :
    (DRS.mk u c).conditions = c := rfl

/-- The empty DRS `⟨∅, []⟩`. -/
def empty : DRS L V := .mk ∅ []

/-- Merge `⊕`: set-union the referents, concatenate the conditions. The binary
DRS merge is @cite{muskens-1996}'s compositional operation — Kamp & Reyle
themselves combine DRSs incrementally via the construction algorithm, not a
symmetric binary `⊕`. An operation, not a syntactic constructor. -/
def merge [DecidableEq V] (K₁ K₂ : DRS L V) : DRS L V :=
  .mk (K₁.referents ∪ K₂.referents) (K₁.conditions ++ K₂.conditions)

@[simp] theorem merge_referents [DecidableEq V] (K₁ K₂ : DRS L V) :
    (K₁.merge K₂).referents = K₁.referents ∪ K₂.referents := rfl

@[simp] theorem merge_conditions [DecidableEq V] (K₁ K₂ : DRS L V) :
    (K₁.merge K₂).conditions = K₁.conditions ++ K₂.conditions := rfl

end DRS

/-! ### Subordination and accessibility -/

/-- One-step subordination ("`K'` is *directly subordinate* to `K`"). The `neg`
case is @cite{kamp-reyle-1993} Def. 1.4.10(i); the `⇒`/`∨` cases are its Chapter 2
extension:

* the body of a `¬` is subordinate to the containing DRS;
* the antecedent of a `⇒` is subordinate to the containing DRS;
* the consequent of a `⇒` is subordinate to its *antecedent* (the ⇒ asymmetry:
  antecedent referents are accessible in the consequent, not conversely);
* each disjunct of a `∨` is subordinate to the containing DRS. -/
inductive DirectlySubordinate {L : Language.{u, v}} {V : Type w} :
    DRS L V → DRS L V → Prop where
  | neg {D K : DRS L V} : Condition.neg K ∈ D.conditions → DirectlySubordinate K D
  | impAnte {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate a D
  | impCons {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate c a
  | disL {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate l D
  | disR {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate r D

/-- `K₁ < K₂`: subordinate — transitive closure of `DirectlySubordinate`
(@cite{kamp-reyle-1993}, Def. 1.4.10(ii)). -/
abbrev Subordinate {L : Language.{u, v}} {V : Type w} : DRS L V → DRS L V → Prop :=
  Relation.TransGen DirectlySubordinate

/-- `K₁ ≤ K₂`: weakly subordinate — reflexive-transitive closure
(@cite{kamp-reyle-1993}; the `≤` of Def. 1.4.10). -/
abbrev WeakSubordinate {L : Language.{u, v}} {V : Type w} : DRS L V → DRS L V → Prop :=
  Relation.ReflTransGen DirectlySubordinate

end DRT
