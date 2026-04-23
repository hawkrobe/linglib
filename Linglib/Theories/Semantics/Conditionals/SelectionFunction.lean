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

namespace Semantics.Conditionals

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

/-- **Selection Excluded Middle** — the structural origin of @cite{stalnaker-1968}'s
    Conditional Excluded Middle and @cite{cariani-santorio-2018}'s Will
    Excluded Middle. Because `sel w f` is a *single* world, every
    predicate evaluated there satisfies excluded middle. The selection
    function reduces a quantificational question over a set to a
    propositional question at one point. -/
theorem sel_em (s : SelectionFunction W) (A : W → Prop) (f : Set W)
    (w : W) :
    A (s.sel w f) ∨ ¬ A (s.sel w f) :=
  Classical.em _

/-- **Selection Negation Swap** — negation commutes through evaluation
    at the selected world: applying a pointwise-negated predicate to
    `sel w f` is the same as negating the application. This is the
    structural origin of @cite{cariani-santorio-2018}'s Negation Swap
    for *will*. The equivalence is `Iff.rfl` once the prejacent has
    been reduced to a propositional question at the selected point. -/
theorem sel_neg_swap (s : SelectionFunction W) (A : W → Prop) (f : Set W)
    (w : W) :
    (fun w' => ¬ A w') (s.sel w f) ↔ ¬ A (s.sel w f) := Iff.rfl

end SelectionFunction

/-- **Pairwise preference induced by a selection function.**

`w₁` is preferred to `w₂` from center `w₀` iff when choosing between
just the two of them, the selection function picks `w₁`. -/
def selectionPrefers {W : Type*} (s : SelectionFunction W)
    (w₀ w₁ w₂ : W) : Prop :=
  s.sel w₀ {w₁, w₂} = w₁

/-- **A selection function is coherent** iff its induced pairwise
preference is transitive. This is the content of @cite{stalnaker-1981}'s
claim that selection functions determine a *well-ordering* of possible
worlds.

Not all selection functions satisfying `inclusion` + `centering` are
coherent — coherence is an additional rationality constraint. -/
def SelectionFunction.isCoherent {W : Type*} (s : SelectionFunction W) : Prop :=
  ∀ w₀ w₁ w₂ w₃ : W,
    selectionPrefers s w₀ w₁ w₂ → selectionPrefers s w₀ w₂ w₃ →
    selectionPrefers s w₀ w₁ w₃

end Semantics.Conditionals
