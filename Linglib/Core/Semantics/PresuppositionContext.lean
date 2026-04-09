import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Semantics.CommonGround

/-!
# Presupposition–Context Bridge
@cite{stalnaker-1974} @cite{heim-1983} @cite{lewis-1979}

Canonical operations connecting presuppositions (`PrProp W`) to contexts
(`ContextSet W`). Before this module, every downstream file that needed
both reimplemented the same bridge with different names:

- `LocalContext.presupFiltered` = `c.entails p.presup`
- `Accommodation.globalAccommodate` = `c.update presup`
- `Accommodation.isInformative` = `¬ c.entails presup`

This module provides a shared vocabulary so that projection, filtering,
accommodation, and conceivability are defined once and reused everywhere.

## Core Operations

| Operation | Meaning | Use site |
|-----------|---------|----------|
| `presupSatisfied` | presup entailed by context | filtering |
| `presupSatisfiable` | ∃ world in context with presup | conceivability |
| `presupProjects` | presup NOT entailed | projection |
| `accommodate` | restrict context to presup worlds | accommodation |

## Conceivability

`presupSatisfiable` is the conceivability check needed for
@cite{enguehard-2024}'s conceivability presupposition: a number feature's
presupposition is *conceivable* in the common ground iff there exists some
world in the context set satisfying it.
-/

namespace Core.PresuppositionContext

open Core.Presupposition
open Core.Proposition
open Core.CommonGround

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. Core Operations
-- ════════════════════════════════════════════════════════════════

/-- A presupposition is **satisfied** (filtered) in context `c` iff the context
    entails it: every world in the context satisfies the presupposition.

    This is Karttunen's filtering condition and Schlenker's local satisfaction. -/
def presupSatisfied (c : ContextSet W) (p : PrProp W) : Prop :=
  c.entails p.presup

/-- A presupposition is **satisfiable** (conceivable) in context `c` iff some
    world in the context satisfies it.

    This is Enguehard's conceivability condition: a singular indefinite's number
    presupposition is conceivable iff the common ground contains a world where
    the witness set has the right cardinality. -/
def presupSatisfiable (c : ContextSet W) (p : PrProp W) : Prop :=
  c.compatible p.presup

/-- A presupposition **projects** from context `c` iff it is NOT satisfied
    (not filtered). Projection is the complement of filtering. -/
def presupProjects (c : ContextSet W) (p : PrProp W) : Prop :=
  ¬ presupSatisfied c p

/-- **Accommodate** a presupposition: restrict the context to worlds where
    the presupposition holds.

    @cite{lewis-1979}: "presupposition P comes into existence." -/
def accommodate (c : ContextSet W) (presup : Prop' W) : ContextSet W :=
  c.update presup

/-- Accommodation is **informative** iff the presupposition is not already
    entailed — accommodation actually changes the context. -/
def accommodationInformative (c : ContextSet W) (presup : Prop' W) : Prop :=
  ¬ c.entails presup

/-- Accommodation is **consistent** iff the restricted context is non-empty —
    the presupposition is compatible with the context. -/
def accommodationConsistent (c : ContextSet W) (presup : Prop' W) : Prop :=
  (accommodate c presup).nonEmpty

-- ════════════════════════════════════════════════════════════════
-- § 2. Theorems
-- ════════════════════════════════════════════════════════════════

/-- Projection and filtering are complementary. -/
theorem projects_iff_not_satisfied (c : ContextSet W) (p : PrProp W) :
    presupProjects c p ↔ ¬ presupSatisfied c p := Iff.rfl

/-- Satisfaction implies satisfiability (when the context is non-empty). -/
theorem satisfied_implies_satisfiable (c : ContextSet W) (p : PrProp W)
    (hne : c.nonEmpty) (hsat : presupSatisfied c p) : presupSatisfiable c p := by
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw, hsat w hw⟩

/-- If the presupposition is not even satisfiable, it projects. -/
theorem not_satisfiable_implies_projects (c : ContextSet W) (p : PrProp W)
    (hne : c.nonEmpty) (h : ¬ presupSatisfiable c p) : presupProjects c p := by
  intro hsat
  exact h (satisfied_implies_satisfiable c p hne hsat)

/-- After accommodation, the presupposition is satisfied. -/
theorem accommodate_entails_presup (c : ContextSet W) (presup : Prop' W) :
    (accommodate c presup).entails presup :=
  fun _ h => h.2

/-- Accommodation is idempotent: accommodating what's already satisfied
    doesn't change the context. -/
theorem accommodate_idempotent (c : ContextSet W) (presup : Prop' W)
    (h : c.entails presup) : ∀ w, accommodate c presup w ↔ c w := by
  intro w
  exact ⟨fun ⟨hw, _⟩ => hw, fun hw => ⟨hw, h w hw⟩⟩

/-- Accommodation strengthens the context: fewer worlds survive. -/
theorem accommodate_strengthens (c : ContextSet W) (presup : Prop' W) :
    ∀ w, accommodate c presup w → c w :=
  fun _ h => h.1

/-- Accommodation consistency = presupposition satisfiable in context. -/
theorem accommodationConsistent_iff_satisfiable (c : ContextSet W) (p : PrProp W) :
    accommodationConsistent c p.presup ↔ presupSatisfiable c p := by
  constructor
  · intro ⟨w, hw_c, hw_p⟩; exact ⟨w, hw_c, hw_p⟩
  · intro ⟨w, hw_c, hw_p⟩; exact ⟨w, hw_c, hw_p⟩

/-- Accommodation via `PrProp.defined`: accommodating `p.presup` restricts
    to worlds where `p.defined` holds. -/
theorem accommodate_eq_defined (c : ContextSet W) (p : PrProp W) :
    ∀ w, accommodate c p.presup w ↔ c w ∧ PrProp.defined w p :=
  fun _ => Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § 3. HasContextSet Generalizations
-- ════════════════════════════════════════════════════════════════

/-- Presupposition satisfied relative to any discourse state with a
    context set. Works with `CG W`, `BContextSet W`, etc. -/
def presupSatisfiedIn {S : Type*} [HasContextSet S W] (s : S) (p : PrProp W) : Prop :=
  presupSatisfied (HasContextSet.toContextSet s) p

/-- Presupposition satisfiable (conceivable) relative to any discourse state. -/
def presupSatisfiableIn {S : Type*} [HasContextSet S W] (s : S) (p : PrProp W) : Prop :=
  presupSatisfiable (HasContextSet.toContextSet s) p

/-- Presupposition projects from any discourse state. -/
def presupProjectsFrom {S : Type*} [HasContextSet S W] (s : S) (p : PrProp W) : Prop :=
  presupProjects (HasContextSet.toContextSet s) p

end Core.PresuppositionContext
