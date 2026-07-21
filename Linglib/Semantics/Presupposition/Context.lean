import Linglib.Semantics.Presupposition.Basic
import Linglib.Discourse.CommonGround

/-!
# Presupposition–Context Bridge
[stalnaker-1974] [heim-1983] [lewis-1979]

Canonical operations connecting presuppositions (`PartialProp W`) to contexts
(`ContextSet W`): the shared vocabulary for projection, filtering,
accommodation, and conceivability.

## Main declarations

* `presupSatisfied` — the context entails the presupposition (filtering).
* `presupSatisfiable` — some context world satisfies it (conceivability).
* `presupProjects` — the context does not entail it (projection).
* `accommodate` — restrict the context to presupposition worlds.

## Conceivability

`presupSatisfiable` is the conceivability check needed for
[enguehard-2024]'s conceivability presupposition: a number feature's
presupposition is *conceivable* in the common ground iff there exists some
world in the context set satisfying it.
-/

namespace Semantics.Presupposition.Context

open Semantics.Presupposition
open CommonGround

variable {W : Type*}

/-! ### Core operations -/

/-- A presupposition is **satisfied** (filtered) in context `c` iff the context
    entails it: every world in the context satisfies the presupposition.

    This is Karttunen's filtering condition and Schlenker's local satisfaction. -/
abbrev presupSatisfied (c : ContextSet W) (p : PartialProp W) : Prop := c ⊆ p.presup

/-- A presupposition is **satisfiable** (conceivable) in context `c` iff some
    world in the context satisfies it.

    This is Enguehard's conceivability condition: a singular indefinite's number
    presupposition is conceivable iff the common ground contains a world where
    the witness set has the right cardinality. -/
abbrev presupSatisfiable (c : ContextSet W) (p : PartialProp W) : Prop :=
  (c ∩ p.presup).Nonempty

/-- A presupposition **projects** from context `c` iff it is NOT satisfied
    (not filtered). Projection is the complement of filtering. -/
abbrev presupProjects (c : ContextSet W) (p : PartialProp W) : Prop :=
  ¬ presupSatisfied c p

/-- **Accommodate** a presupposition: restrict the context to worlds where
    the presupposition holds.

    [lewis-1979]: "presupposition P comes into existence." -/
abbrev accommodate (c : ContextSet W) (presup : Set W) : ContextSet W := c ∩ presup

/-- Accommodation is **informative** iff the presupposition is not already
    entailed — accommodation actually changes the context. -/
abbrev accommodationInformative (c : ContextSet W) (presup : Set W) : Prop :=
  ¬ c ⊆ presup

/-- Accommodation is **consistent** iff the restricted context is non-empty —
    the presupposition is compatible with the context. -/
abbrev accommodationConsistent (c : ContextSet W) (presup : Set W) : Prop :=
  (accommodate c presup).Nonempty

/-! ### Theorems -/

/-- Satisfaction implies satisfiability (when the context is non-empty). -/
theorem satisfied_implies_satisfiable (c : ContextSet W) (p : PartialProp W)
    (hne : c.Nonempty) (hsat : presupSatisfied c p) : presupSatisfiable c p := by
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw, hsat hw⟩

/-- If the presupposition is not even satisfiable, it projects. -/
theorem not_satisfiable_implies_projects (c : ContextSet W) (p : PartialProp W)
    (hne : c.Nonempty) (h : ¬ presupSatisfiable c p) : presupProjects c p :=
  fun hsat => h (satisfied_implies_satisfiable c p hne hsat)

/-- After accommodation, the presupposition is satisfied. -/
theorem accommodate_entails_presup (c : ContextSet W) (presup : Set W) :
    accommodate c presup ⊆ presup :=
  Set.inter_subset_right

/-- Accommodation is idempotent: accommodating what's already satisfied
    doesn't change the context. -/
theorem accommodate_idempotent (c : ContextSet W) (presup : Set W)
    (h : c ⊆ presup) : accommodate c presup = c :=
  Set.inter_eq_left.mpr h

/-- Accommodation strengthens the context: fewer worlds survive. -/
theorem accommodate_strengthens (c : ContextSet W) (presup : Set W) :
    accommodate c presup ⊆ c :=
  Set.inter_subset_left

/-- Accommodation consistency = presupposition satisfiable in context. -/
theorem accommodationConsistent_iff_satisfiable (c : ContextSet W) (p : PartialProp W) :
    accommodationConsistent c p.presup ↔ presupSatisfiable c p := Iff.rfl

/-- Accommodation via `PartialProp.defined`: accommodating `p.presup` restricts
    to worlds where `p.defined` holds. -/
theorem accommodate_eq_defined (c : ContextSet W) (p : PartialProp W) (w : W) :
    w ∈ accommodate c p.presup ↔ w ∈ c ∧ PartialProp.defined w p :=
  Iff.rfl

/-! ### `HasContextSet` generalizations -/

/-- Presupposition satisfied relative to any discourse state with a
    context set. Works with `CommonGround W`, `Commitment.CommitmentSlate W`,
    `LocalCtx W`, and any other state implementing `HasContextSet`. -/
abbrev presupSatisfiedIn {S : Type*} [HasContextSet S W] (s : S) (p : PartialProp W) : Prop :=
  presupSatisfied (HasContextSet.toContextSet s) p

/-- Presupposition satisfiable (conceivable) relative to any discourse state. -/
abbrev presupSatisfiableIn {S : Type*} [HasContextSet S W] (s : S) (p : PartialProp W) : Prop :=
  presupSatisfiable (HasContextSet.toContextSet s) p

/-- Presupposition projects from any discourse state. -/
abbrev presupProjectsFrom {S : Type*} [HasContextSet S W] (s : S) (p : PartialProp W) : Prop :=
  presupProjects (HasContextSet.toContextSet s) p

end Semantics.Presupposition.Context
