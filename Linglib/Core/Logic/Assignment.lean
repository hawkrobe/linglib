import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic

/-!
# Variable Assignments
[heim-kratzer-1998] [henkin-monk-tarski-1971] [spector-2025]
[beaver-krahmer-2001]

Tarski-style total assignments and their partial extension. The polymorphic
substrate shared by extensional Heim-Kratzer composition, DPL-style register
state, CDRT, Charlow continuations, and trivalent partial-valuation systems.

`Assignment E := ℕ → E` is **pre-intensional** — pure Tarski variable mapping —
so it lives in `Core/Logic/` rather than inside `Semantics/Intensional/`.
The intensional substrate (`Denot E W`, situation assignments
`Assignment W`, `DenotGS`) builds on this in `Semantics/Intensional/`.

Pointwise update of a total assignment is mathlib's `Function.update`
(no parallel API here): `Function.update_self`, `Function.update_of_ne`,
`Function.update_idem`, `Function.update_comm`, and `Function.update_eq_self`
are the update laws. The Heim-Kratzer notation `g[n ↦ x]` is declared in
`Semantics/Intensional/Variables.lean`.

## When to use `Assignment E` vs raw `Nat → E`

A struct field, function parameter, or local definition should use
`Assignment E` (or `PartialAssign E`) precisely when its semantic role is
**Tarski-style variable assignment / register state / discourse-referent
embedding** — the same role that gets `update`d by quantifier binders and
`look`ed-up by free variables.

It should *not* be `Assignment E` when the structural shape `Nat → E`
happens for an unrelated reason — e.g., model-theoretic name
interpretation functions (`Name_M` in Kamp & Reyle), arity-indexed
interpretation tables, lookup arrays, or any `Nat → α` that doesn't
participate in variable-binding semantics. Renaming those would conflate
distinct primitives.

## Out of scope

- **Discourse referents as named atomic symbols** (Kamp & Reyle 1993 DRT proper).
  The ℕ-indexed register encoding is the DPL/CDRT reading; faithful K&R
  embeddings would need an opaque `DRef` type.
- **File cards** (Heim 1982 FCS). Heim's files carry an explicit domain
  `Dom(F) ⊆ ℕ` — `PartialAssign` covers the *valuation* side, but the
  domain-as-type-level commitment of FCS lives in the FCS study file.
- **Proof-relevant context** (Bekki DTS, Asher TYS) — not a `Nat → α`.
- **Continuation *state*** (Heim file cards, sequence-of-binders update
  semantics) — handled in the FCS / DPL study files. Continuation
  *environments* (Barker, Shan, Charlow paycheck composition) DO use
  `Assignment` as the Reader environment; that case is in scope.
-/

namespace Core

-- ════════════════════════════════════════════════════════════════
-- Total Assignments (Tarski-style; the extensional substrate)
-- [heim-kratzer-1998] [henkin-monk-tarski-1971]
-- ════════════════════════════════════════════════════════════════

/-- Variable assignment: a function from natural-number indices to values in
    `E`. Instantiated at the entity type for entity pronouns (Heim & Kratzer
    1998), at the index type for situation pronouns (Hanink 2021 / Bondarenko 2023),
    at `Time` for temporal variables, and at any other carrier whenever a
    framework needs Tarski-style variable interpretation.

    Pointwise update `g[n↦d]` is `Function.update g n d`; mathlib's
    `Function.update_*` lemmas apply directly. -/
abbrev Assignment (E : Type*) := Nat → E

-- ════════════════════════════════════════════════════════════════
-- Partial Assignments
-- [spector-2025] [beaver-krahmer-2001]
-- ════════════════════════════════════════════════════════════════

/-- Partial assignment: variables may be undefined (`none`).

    Used in trivalent semantics ([spector-2025], [beaver-krahmer-2001])
    where `g(x) = none` means variable `x` is not valued. The trivalent
    *application* rule that turns this into the third value `#` lives with
    the predicate machinery in `Semantics/Presupposition/`, not here. -/
abbrev PartialAssign (D : Type*) := Nat → Option D

namespace PartialAssign

variable {D : Type*}

/-- A partial assignment that values no variables. -/
def empty : PartialAssign D := λ _ => none

/-- Update a partial assignment at index `n`: `Function.update` with the
    value wrapped in `some`. -/
def update (g : PartialAssign D) (n : Nat) (d : D) : PartialAssign D :=
  Function.update g n (some d)

/-- Whether variable `n` is valued by `g`. -/
def valued (g : PartialAssign D) (n : Nat) : Bool :=
  (g n).isSome

@[simp] theorem update_at (g : PartialAssign D) (n : Nat) (d : D) :
    (g.update n d) n = some d := by
  simp [update]

@[simp] theorem update_ne (g : PartialAssign D) {n m : Nat} (d : D)
    (h : m ≠ n) : (g.update n d) m = g m := by
  simp [update, h]

/-- Updating a partial assignment at `n` to its existing value is a no-op:
`g.update n a = g` whenever `g n = some a`. The partial-assignment analogue
of `Function.update_eq_self`; needed by formalisations that recover the
witness as `g(x).get` (e.g., Mandelkern's bounded theory §5.6 atomic
bound-equivalence proofs). -/
theorem update_self {g : PartialAssign D} {n : Nat} {a : D}
    (h : g n = some a) : g.update n a = g := by
  rw [update, ← h]; exact Function.update_eq_self n g

@[simp] theorem valued_update_at (g : PartialAssign D) (n : Nat) (d : D) :
    (g.update n d).valued n = true := by simp [update, valued]

@[simp] theorem valued_update_ne (g : PartialAssign D) {n m : Nat} (d : D)
    (h : m ≠ n) : (g.update n d).valued m = g.valued m := by
  simp [update, valued, h]

theorem valued_empty (n : Nat) : (empty (D := D)).valued n = false := rfl

/-- Coerce a total assignment to a partial assignment (always valued). -/
def ofTotal (g : Assignment D) : PartialAssign D :=
  λ n => some (g n)

theorem valued_ofTotal (g : Assignment D) (n : Nat) :
    (ofTotal g).valued n = true := rfl

end PartialAssign

-- ════════════════════════════════════════════════════════════════
-- Plural Assignments
-- [van-den-berg-1996] [nouwen-2003] [brasoveanu-2008]
-- [spector-2025] [haug-dalrymple-2020]
-- ════════════════════════════════════════════════════════════════

/-- Plural assignment: a set of atomic (partial) assignments.

    Originates in plural dynamic semantics ([van-den-berg-1996],
    [nouwen-2003], [brasoveanu-2008]). The plural information
    state is the basic carrier of Plural CDRT (Brasoveanu, Dotlačil) and
    its partial extension PPCDRT (Haug 2014, [haug-dalrymple-2020]).
    Spector's static reuse ([spector-2025]) is the trivalent point
    of this primitive: variables that are *singular* across the plural
    state behave classically; variables that are not are gappy.

    Wrapped in a structure so the bespoke `Membership` instance is found
    by typeclass search instead of mathlib's `Set` instances.

    Consumers: `Studies/Spector2025.lean` (trivalent),
    `Semantics/Dynamic/PPCDRT/` (plural partial CDRT). -/
@[ext] structure PluralAssign (D : Type*) where
  /-- The membership predicate on atomic assignments. -/
  pred : PartialAssign D → Prop

namespace PluralAssign

variable {D : Type*}

instance : Membership (PartialAssign D) (PluralAssign D) where
  mem G g := G.pred g

/-- Whether `G` contains at least one atomic assignment.
    Named `IsNonempty` rather than `Nonempty` to avoid shadowing
    `_root_.Nonempty`. -/
def IsNonempty (G : PluralAssign D) : Prop := ∃ g, g ∈ G

/-- Restrict a plural assignment to atomic assignments mapping `x` to `a`.
    Spector §6.2: `G_{x=a}` is the subset of `G` where `g(x) = a`. -/
def restrict (G : PluralAssign D) (x : Nat) (a : D) : PluralAssign D :=
  ⟨λ g => g ∈ G ∧ g x = some a⟩

/-- Whether any atomic assignment in `G` is defined for `x`. -/
def defined (G : PluralAssign D) (x : Nat) : Prop :=
  ∃ g, g ∈ G ∧ (g x).isSome

/-- The universal plural assignment: contains every partial assignment.
    Spector §6: the starting context contains all pairs. -/
def null : PluralAssign D := ⟨λ _ => True⟩

/-- Build a plural assignment from a predicate. -/
def ofPred (p : PartialAssign D → Prop) : PluralAssign D := ⟨p⟩

/-- The singleton plural assignment containing exactly `g`. The minimal
    plural state — used for the singleton-collapse bridges between PPCDRT
    and the singular CDRT-style semantics. -/
def singleton (g : PartialAssign D) : PluralAssign D := ⟨λ g' => g' = g⟩

/-- Witness-level singularity: `G` assigns `x` uniquely to `d`.
    Spector §6.2: at least one atomic assignment maps `x` to `d`,
    and all assignments in `G` that define `x` agree on `d`.

    NOTE: this allows assignments where `x` is undefined to coexist
    with assignments where `x = d` (only the *defined* rows are required
    to agree). The all-defined reading would be stronger; the present
    reading is the one Spector's static reuse of plural states needs. -/
def singularAt (G : PluralAssign D) (x : Nat) (d : D) : Prop :=
  (∃ g, g ∈ G ∧ g x = some d) ∧ (∀ g, g ∈ G → (g x).isSome → g x = some d)

/-- `singular G x` ↔ there is some `d` such that `G` assigns `x` uniquely to it.
    Spector's `atomic(x)` predicate; replaces `U(x)` from the simplified system. -/
def singular (G : PluralAssign D) (x : Nat) : Prop :=
  ∃ d, G.singularAt x d

/-- Sum-of-values for dref `n` across the plural state. Spector §6.2 and
    [haug-dalrymple-2020]'s `∪u` operator (paper §2.1, eq 8): the set
    of values that `n` takes across all atomic assignments in `G`. -/
def sumDref (G : PluralAssign D) (n : Nat) : Set D :=
  { d | ∃ g ∈ G, g n = some d }

end PluralAssign

end Core
