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

/-- A DRT *box* over condition type `C`: a universe of discourse referents and
a list of conditions — the two-compartment diagram the field draws (universe
above, conditions below; [muskens-1996]'s linear `[u₁ … uₙ | γ₁ … γₘ]`). "Box"
and "DRS" name the same object in the literature, in diagrammatic vs. official
register; here `Box` is the generic shell that DRT variants re-instantiate at
their condition types (`DRS` at `Condition L V`; cf. Layered DRT's LDRSs), and
the container the condition syntax nests through. -/
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

/-- A discourse representation structure: a box of DRS-conditions — the pair
`⟨referents, conditions⟩` (Def. 1.4.1). -/
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

/-! ### Subordination -/

/-- One-step subordination ("`K'` is *directly subordinate* to `K`"). The `neg`
case is Def. 1.4.10(i); the `⇒`/`∨` cases are its Chapter 2 extension:

* the body of a `¬` is subordinate to the containing DRS;
* the antecedent of a `⇒` is subordinate to the containing DRS;
* the consequent of a `⇒` is subordinate to its *antecedent* (the ⇒ asymmetry:
  antecedent referents are accessible in the consequent, not conversely);
* each disjunct of a `∨` is subordinate to the containing DRS.

A relation on DRS *values*, where the textbook's is on box *occurrences*: on a
degenerate `imp a a` the consequent edge makes `a` subordinate to itself. -/
inductive DirectlySubordinate : DRS L V → DRS L V → Prop where
  | neg {D K : DRS L V} : Condition.neg K ∈ D.conditions → DirectlySubordinate K D
  | impAnte {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate a D
  | impCons {D a c : DRS L V} : Condition.imp a c ∈ D.conditions → DirectlySubordinate c a
  | disL {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate l D
  | disR {D l r : DRS L V} : Condition.dis l r ∈ D.conditions → DirectlySubordinate r D

/-- `K₁ < K₂`: subordinate — transitive closure of `DirectlySubordinate`
(Def. 1.4.10(ii)). Anchors Def. 1.4.10(ii) only:
accessibility (`accessibleFrom`, `DRS/Basic.lean`) does not build on this
closure. -/
abbrev Subordinate : DRS L V → DRS L V → Prop :=
  Relation.TransGen DirectlySubordinate

/-- `K₁ ≤ K₂`: weakly subordinate — reflexive-transitive closure
(the `≤` of Def. 1.4.10). Anchors Def. 1.4.10(ii) only:
accessibility does not build on this closure. -/
abbrev WeakSubordinate : DRS L V → DRS L V → Prop :=
  Relation.ReflTransGen DirectlySubordinate

end DRT
