import Linglib.Semantics.Dynamic.DRS.Box
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Basic

/-!
# Discourse representation structures

This file defines discourse representation structures (DRSs) over a mathlib
`FirstOrder.Language`, following [kamp-reyle-1993]. A DRS is a pair of a finite
set of *discourse referents* (the textbook's universe `U`) and a list of
*conditions* (Def. 1.4.1); a condition is atomic (`rel`, `eq`) or complex
(`neg`, with `imp`/`dis` from the Chapter 2 extension), and sub-DRSs occur only
inside complex conditions. In the literature a DRS is also drawn as a *box*,
[muskens-1996]'s `[u₁ … uₙ | γ₁ … γₘ]`.

Verification and truth are model-theoretic and live in `DRS/Verification.lean`;
the structural theory is in `DRS/Basic.lean`.

## Main declarations

* `Condition`, `DRS`: conditions and DRSs over a language `L` and referent type
  `V`; `DRS L V` is the generic container `Box` (`DRS/Box.lean`) instantiated at
  `Condition L V`.
* `DRS.merge`: the merge `⊕` — union the referents, append the conditions
  ([muskens-1996]).
* `DirectlySubordinate`, `Subordinate`, `WeakSubordinate`: immediate
  subordination and its transitive and reflexive-transitive closures
  (Def. 1.4.10, Def. 2.1.2). Accessibility is host-relative and lives in
  `DRS/Basic.lean` (`AccessibleTo`, `accessibleFrom`).

## Main statements

* `WeakSubordinate.antisymm`: weak subordination is a partial order.

## Implementation notes

* `referents` is the textbook `U`; `universe` is a Lean keyword and `univ`
  collides with `Finset.univ`.
* `Box` is a container structure the condition syntax nests through, and `DRS`
  its instantiation at `Condition L V` — Def. 1.4.1's simultaneous recursion
  without a mutual block, keeping the structure API.
* `conditions` is a `List`, since an inductive cannot nest through
  `Finset`/`Multiset`; set semantics is recovered by the interpretation
  (`Embedding.verifies_perm`, `DRS/Verification.lean`).
* `DRT` is the owning namespace, on the `FirstOrder.Language` pattern.
-/

open FirstOrder

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w}

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

/-- The empty DRS `⟨∅, []⟩`. -/
def empty : DRS L V := .mk ∅ []

instance : Inhabited (DRS L V) := ⟨empty⟩

/-- The merge `K₁ ⊕ K₂` unions the referents and appends the conditions —
[muskens-1996]'s compositional operation (Kamp & Reyle combine DRSs
incrementally via the construction algorithm instead). An operation, not a
syntactic constructor. -/
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

/-- `DirectlySubordinate K' K` says `K'` is a sub-box of one of `K`'s conditions —
the `neg` case per Def. 1.4.10(i), the `⇒`/`∨` cases per its Chapter 2 extension
(Def. 2.1.2, which subordinates *both* components of a conditional to the
containing DRS). A relation on DRS values, where the textbook's is on box
occurrences. Every clause pins the containing box in its conclusion: an unpinned
clause (such as consequent-below-antecedent) would hold of every pair of DRSs via
a manufactured container, collapsing the relation. The `⇒` visibility asymmetry
is not subordination but accessibility (`AccessibleTo`, `DRS/Basic.lean`). -/
inductive DirectlySubordinate : DRS L V → DRS L V → Prop where
  /-- The body of a `¬` is directly subordinate to the containing DRS. -/
  | neg {D K : DRS L V} : Condition.neg K ∈ D.conditions → DirectlySubordinate K D
  /-- The antecedent of a `⇒` is directly subordinate to the containing DRS. -/
  | impAnte {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate a D
  /-- The consequent of a `⇒` is directly subordinate to the containing DRS. -/
  | impCons {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate c D
  /-- The left disjunct of a `∨` is directly subordinate to the containing DRS. -/
  | disL {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate l D
  /-- The right disjunct of a `∨` is directly subordinate to the containing DRS. -/
  | disR {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate r D

/-- The `<` of Def. 1.4.10(ii): the transitive closure of `DirectlySubordinate`. -/
abbrev Subordinate : DRS L V → DRS L V → Prop :=
  Relation.TransGen DirectlySubordinate

/-- The `≤` of Def. 1.4.10(ii): the reflexive-transitive closure of
`DirectlySubordinate`. -/
abbrev WeakSubordinate : DRS L V → DRS L V → Prop :=
  Relation.ReflTransGen DirectlySubordinate

/-- A directly subordinate DRS is a structurally smaller value. -/
theorem DirectlySubordinate.sizeOf_lt {K' K : DRS L V} (h : DirectlySubordinate K' K) :
    sizeOf K' < sizeOf K := by
  obtain ⟨U, conds⟩ := K
  cases h with
  | neg h | impAnte h | impCons h | disL h | disR h =>
    have := List.sizeOf_lt_of_mem h
    simp_all
    omega

/-- Subordinate DRSs are structurally smaller; subordination chains terminate. -/
theorem Subordinate.sizeOf_lt {K' K : DRS L V} (h : Subordinate K' K) :
    sizeOf K' < sizeOf K := by
  induction h with
  | single h => exact h.sizeOf_lt
  | tail _ h ih => exact ih.trans h.sizeOf_lt

theorem Subordinate.irrefl (K : DRS L V) : ¬ Subordinate K K :=
  fun h => absurd h.sizeOf_lt (lt_irrefl _)

/-- Weak subordination is a partial order on DRS values. -/
theorem WeakSubordinate.antisymm {K' K : DRS L V} (h : WeakSubordinate K' K)
    (h' : WeakSubordinate K K') : K' = K := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | h₁
  · rfl
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h' with rfl | h₂
  · rfl
  exact absurd ((Subordinate.sizeOf_lt h₁).trans (Subordinate.sizeOf_lt h₂)) (lt_irrefl _)

end DRT
