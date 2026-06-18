import Linglib.Core.Order.Relation

/-!
# Clause: theory-neutral clause size and transparency

A clause's *size* and its *transparency to a dependency* are framework-neutral
notions: every theory of clause structure (Minimalist cartography, HPSG, CCG, …)
ranks its clauses and tells you when a dependency can reach inside one. This
file owns those notions so that downstream consumers — sequence of tense
(`Semantics/Tense/Sequence`), relative-clause opacity, long-distance Agree — do
**not** import any one framework's machinery (`Cat`, `fValue`, …).

A framework *provides* the interface: e.g. `Minimalist.ComplementSize.toClauseSize`
ranks a complement by its functional grade. Reasoning about opacity then runs
through `Clause.Size` / `Clause.transparentTo`, not through `Cat`.

The whole notion reduces to `Core.Order`: a size is a grade in a scale, and a
clause is transparent to a dependency stopped at `boundary` iff its grade is
*before* (below) the boundary.
-/

namespace Clause

open Core.Order

/-- A theory-neutral clause size: a grade in a scale, decoupled from any
    framework's representation. The scale is `ℕ` — every framework can rank its
    clauses into it (Minimalist via `fValue`, …) — but consumers should reason
    through `transparentTo`, not the numeral. -/
abbrev Size : Type := ℕ

/-- A clause of size `s` is transparent to a dependency whose opacity boundary
    is `boundary` iff its grade is strictly below the boundary in the scale —
    `Core.Order.before`. (Selective opacity, the Williams Cycle in the abstract:
    a dependency stopped at `boundary` reaches into everything smaller.) -/
def transparentTo (s boundary : Size) : Prop := holds before s boundary

instance (s boundary : Size) : Decidable (transparentTo s boundary) :=
  inferInstanceAs (Decidable (holds _ _ _))

@[simp] theorem transparentTo_iff (s boundary : Size) :
    transparentTo s boundary ↔ s < boundary := holds_before s boundary

/-- **Upward entailment** (the abstract Williams Cycle): if a clause is opaque
    to a dependency, every larger clause is opaque too. Framework instances
    (e.g. `Minimalist`'s `upward_entailment`) are special cases. -/
theorem opaque_upward {s₁ s₂ boundary : Size}
    (h : ¬ transparentTo s₁ boundary) (hle : s₁ ≤ s₂) :
    ¬ transparentTo s₂ boundary := by
  rw [transparentTo_iff, not_lt] at h ⊢
  exact le_trans h hle

end Clause
