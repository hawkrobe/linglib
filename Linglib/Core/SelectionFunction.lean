import Mathlib.Data.Set.Basic

/-!
# Selection Functions
@cite{stalnaker-1968}

A **selection function** in the sense of @cite{stalnaker-1968}: given a
world `w` and a non-empty proposition `A ⊆ W`, return a unique
"selected" world `s w A ∈ A` — intuitively, the closest A-world to `w`.

Selection functions are characterized by two axioms:

- **Inclusion**: `s w A ∈ A` whenever `A` is non-empty (the selected
  world satisfies the input proposition).
- **Centering**: if `w ∈ A`, then `s w A = w` (when `w` itself is in
  `A`, the closest A-world is `w` itself).

These two axioms suffice for many semantic applications:
@cite{stalnaker-1968} conditionals, @cite{cariani-santorio-2018}'s
selectional semantics for *will*, and Schulz's choice-function
conditionals all rely on selection functions of this form.

Behavior on empty `A` is left unspecified: the axioms are vacuous
there, and concrete instances may pick any default.
-/

namespace Core

/-- A **selection function** on `W`: maps a world and a proposition to
    a "selected" world, satisfying @cite{stalnaker-1968}'s Inclusion
    and Centering axioms. -/
structure SelectionFunction (W : Type*) where
  /-- The selection map. -/
  sel : W → Set W → W
  /-- **Inclusion**: if `A` is non-empty, the selected world is in `A`. -/
  inclusion : ∀ (w : W) (A : Set W), A.Nonempty → sel w A ∈ A
  /-- **Centering**: if `w ∈ A`, then `sel w A = w`. -/
  centering : ∀ (w : W) (A : Set W), w ∈ A → sel w A = w

namespace SelectionFunction

variable {W : Type*}

/-- Centering specialized to a singleton: `sel w {w} = w`. -/
theorem sel_singleton (s : SelectionFunction W) (w : W) :
    s.sel w {w} = w :=
  s.centering w _ rfl

/-- The selected world satisfies the input proposition (Inclusion). -/
theorem sel_mem (s : SelectionFunction W) (w : W) (A : Set W)
    (hA : A.Nonempty) : s.sel w A ∈ A :=
  s.inclusion w A hA

end SelectionFunction

end Core
