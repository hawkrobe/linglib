import Mathlib.Init

/-!
# Variable Assignments
@cite{heim-kratzer-1998} @cite{henkin-monk-tarski-1971} @cite{spector-2025}
@cite{beaver-krahmer-2001}

Tarski-style total assignments and their partial extension. The polymorphic
substrate shared by extensional Heim-Kratzer composition, DPL-style register
state, CDRT, Charlow continuations, and trivalent partial-valuation systems.

`Assignment E := ℕ → E` is **pre-intensional** — pure Tarski variable mapping —
so it lives at the top of `Core` rather than inside `Core.IntensionalLogic`.
The intensional substrate (`Frame`, `SitAssignment F := Assignment F.Index`,
`DenotGS`) builds on this in `Core/IntensionalLogic/`.

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
distinct primitives. (`KRModel.names : Nat → E` in
`Theories/Semantics/Dynamic/DRT/Basic.lean` documents one such case.)

## Out of scope

- **Discourse referents as named atomic symbols** (Kamp & Reyle 1993 DRT proper).
  The ℕ-indexed register encoding is the DPL/CDRT reading; faithful K&R
  embeddings would need an opaque `DRef` type.
- **File cards** (Heim 1982 FCS). Heim's files carry an explicit domain
  `Dom(F) ⊆ ℕ` — `PartialAssign` covers the *valuation* side, but the
  domain-as-type-level commitment of FCS lives in the FCS study file.
- **Set-of-assignments / plural information states**. `PluralAssign` was
  promoted out of this file; the only consumer is Spector 2025, where the
  type now lives as `Spector2025.PluralAssign` in
  `Phenomena/Anaphora/Studies/Spector2025.lean` (paper-local rather than
  globally available under `Core`).
- **Proof-relevant context** (Bekki DTS, Asher TYS) — not a `Nat → α`.
- **Continuation *state*** (Heim file cards, sequence-of-binders update
  semantics) — handled in the FCS / DPL study files. Continuation
  *environments* (Barker, Shan, Charlow paycheck composition) DO use
  `Assignment` as the Reader environment; that case is in scope.
-/

namespace Core

-- ════════════════════════════════════════════════════════════════
-- Total Assignments (Tarski-style; the extensional substrate)
-- @cite{heim-kratzer-1998} @cite{henkin-monk-tarski-1971}
-- ════════════════════════════════════════════════════════════════

/-- Variable assignment: a function from natural-number indices to values in
    `E`. Instantiated at `F.Entity` for entity pronouns (Heim & Kratzer
    1998), at `F.Index` for situation pronouns (Hanink 2021 / Bondarenko 2023),
    at `Time` for temporal variables, and at any other carrier whenever a
    framework needs Tarski-style variable interpretation. -/
abbrev Assignment (E : Type*) := Nat → E

namespace Assignment

/-- Pointwise update `g[n↦d]`: set register `n` to `d`, leaving all other
    registers fixed. -/
def update {E : Type*} (g : Assignment E) (n : Nat) (d : E) : Assignment E :=
  λ m => if m = n then d else g m

@[simp] theorem update_at {E : Type*} (g : Assignment E) (n : Nat) (d : E) :
    (g.update n d) n = d := by simp [update]

@[simp] theorem update_ne {E : Type*} (g : Assignment E) {n m : Nat} (d : E)
    (h : m ≠ n) : (g.update n d) m = g m := by simp [update, h]

@[simp] theorem update_overwrite {E : Type*} (g : Assignment E) (n : Nat) (x y : E) :
    (g.update n x).update n y = g.update n y := by
  funext m; simp [update]; split <;> rfl

theorem update_comm {E : Type*} (g : Assignment E) {n m : Nat} (x y : E)
    (h : n ≠ m) : (g.update n x).update m y = (g.update m y).update n x := by
  funext k; simp [update]; by_cases hn : k = n <;> by_cases hm : k = m <;> simp_all

@[simp] theorem update_self {E : Type*} (g : Assignment E) (n : Nat) :
    g.update n (g n) = g := by
  funext i; simp [update]; intro h; exact congrArg g h.symm

end Assignment

-- ════════════════════════════════════════════════════════════════
-- Partial Assignments
-- @cite{spector-2025} @cite{beaver-krahmer-2001}
-- ════════════════════════════════════════════════════════════════

/-- Partial assignment: variables may be undefined (`none`).

    Used in trivalent semantics (@cite{spector-2025}, @cite{beaver-krahmer-2001})
    where `g(x) = none` means variable `x` is not valued. The trivalent
    *application* rule that turns this into the third value `#` lives with
    the predicate machinery in `Theories/Semantics/Presupposition/`, not here. -/
abbrev PartialAssign (D : Type*) := Nat → Option D

namespace PartialAssign

variable {D : Type*}

/-- A partial assignment that values no variables. -/
def empty : PartialAssign D := λ _ => none

/-- Update a partial assignment at index `n`. -/
def update (g : PartialAssign D) (n : Nat) (d : D) : PartialAssign D :=
  λ m => if m = n then some d else g m

/-- Whether variable `n` is valued by `g`. -/
def valued (g : PartialAssign D) (n : Nat) : Bool :=
  (g n).isSome

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

end Core
