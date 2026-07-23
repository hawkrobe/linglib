import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Plurality — Shared substrate
[kriz-spector-2021] [haslinger-etal-2025]

Substrate primitives shared across all theoretical accounts of plural
predication in this directory: a tolerance relation on `Finset Atom`
(controlling exception tolerance), the basic distribution operators
`distMaximal`/`allSatisfy`/`someSatisfy`/`noneSatisfy`, and their
decidability instances. Specialised operators (`distTolerant`,
trivalent K&S apparatus, Bar-Lev `existPL`, etc.) live in sibling
files.

## Main declarations

* `Tolerance` — reflexive, sub-plurality-respecting relation on
  `Finset Atom`.
* `Tolerance.identity`, `Tolerance.trivial` — the two anchor instances
  used by downstream Studies.
* `distMaximal` — `∀ a ∈ x, P a w`. The maximal-distribution predicate.
* `allSatisfy` — alias of `distMaximal` (kept under its K&S-paper-faithful
  name for legibility in study files).
* `someSatisfy`, `noneSatisfy` — existential and universal-negation
  duals.

## Implementation notes

This file sits under `namespace Semantics.Plurality` (the directory
umbrella) rather than `Semantics.Plurality.Basic` (filename pattern).
Consumers `open Semantics.Plurality` for substrate access; specific
theoretical accounts (`Distributivity`, `Trivalent`, `Implicature`,
`Cumulativity`, …) live under sub-namespaces and are opened separately.
-/

namespace Semantics.Plurality

variable {Atom W : Type*}

/-! ### Tolerance relations -/

/--
A tolerance relation determines which sub-pluralities count as
"similar enough" to the whole for current conversational purposes.

Formally: `⪯` is reflexive and respects mereological structure.
-/
structure Tolerance (Atom : Type*) [DecidableEq Atom] where
  /-- `y ⪯ x`: `y` is similar enough to `x`. -/
  rel : Finset Atom → Finset Atom → Prop
  /-- Decidability of the tolerance relation. -/
  decRel : ∀ x y, Decidable (rel x y)
  /-- Reflexivity. -/
  refl : ∀ x, rel x x
  /-- Tolerance implies sub-plurality. -/
  sub : ∀ x y, rel x y → x ⊆ y

/-- Per-`Tolerance` decidability instance for the relation. -/
instance Tolerance.instDecidableRel {Atom : Type*} [DecidableEq Atom]
    (tol : Tolerance Atom) (x y : Finset Atom) : Decidable (tol.rel x y) :=
  tol.decRel x y

namespace Tolerance

variable [DecidableEq Atom]

/-- Identity tolerance: only `x ⪯ x` (forces maximal reading). -/
def identity : Tolerance Atom where
  rel x y := x = y
  decRel x y := decEq x y
  refl _ := rfl
  sub x _ h := h ▸ Finset.Subset.refl x

/-- Trivial tolerance: any sub-plurality is tolerated (allows existential
    reading). [kriz-spector-2021] call this the *trivial* tolerance
    — the relation is just sub-pluralityhood, with no further restriction. -/
def trivial : Tolerance Atom where
  rel x y := x ⊆ y
  decRel _ _ := Finset.decidableDforallFinset
  refl _ := Finset.Subset.refl _
  sub _ _ h := h

end Tolerance

/-! ### Basic plural predicates -/

/-- Maximal distributive: `⟦each P⟧(x) = ∀ a ∈ x, P a`.
    The semantics of English *each*, German *jeder*. -/
def distMaximal (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ x, P a w

instance distMaximal.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (distMaximal P x w) := by unfold distMaximal; infer_instance

/-- All atoms in `x` satisfy `P` at `w`. Alias of `distMaximal` — kept
    under its K&S-paper-faithful name for legibility in study files;
    consumers may use either. -/
def allSatisfy (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  distMaximal P x w

instance allSatisfy.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (allSatisfy P x w) :=
  inferInstanceAs (Decidable (distMaximal P x w))

/-- Some atom in `x` satisfies `P` at `w`. -/
def someSatisfy (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∃ a ∈ x, P a w

instance someSatisfy.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (someSatisfy P x w) := by unfold someSatisfy; infer_instance

/-- No atom in `x` satisfies `P` at `w`. -/
def noneSatisfy (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ x, ¬ P a w

instance noneSatisfy.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (noneSatisfy P x w) := by unfold noneSatisfy; infer_instance

end Semantics.Plurality
