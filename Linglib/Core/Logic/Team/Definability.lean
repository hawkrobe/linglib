import Linglib.Core.Logic.Team.Closure

/-!
# Definability and expressive completeness for team-semantic logics

@cite{anttila-2025}

A **team property** over a point type `α` is a class of teams,
`Set (Finset α)` — the same object `Team/Closure.lean` calls a "team-set".
A formula `φ` *defines* the team property consisting of all teams that
support it. The organizing theorem for the team-semantic family
(@cite{anttila-2025}) is **expressive completeness**: the class of
properties a logic can define equals a class fixed by closure conditions
(downward closure, union closure, convexity, the empty-team property) —
plus invariance under bounded bisimulation in the modal case.

This file is the *substrate* for that program. It defines definability
and the definable class over an abstract support relation
`s : Form → Finset α → Prop`, so every logic — bilateral or unilateral,
modal or propositional — instantiates it with its own `support M`. It does
**not** import any logic: each logic's expressive-completeness theorem
lives with the logic and *consumes* `definableClass_subset` here.

The reusable bridge is `definableClass_subset`: a per-logic closure
theorem (`supClosed_support`, `isLowerSet_support`, …, proved in each
logic's file) becomes the *soundness* half of expressive completeness
(definable class ⊆ closure class) by one application. The hard *converse*
half — every property in the class is definable, via normal forms — is the
per-logic work the roadmap tracks.

## Main definitions

* `TeamProperty α` — a class of teams, `Set (Finset α)`.
* `definedBy s φ` — the team property defined by `φ` under support `s`.
* `Definable s P`, `definableClass s` — the definable properties (written
  `⟦L⟧` in @cite{anttila-2025} for a logic `L` with support relation `s`).
* `ExpressivelyCompleteFor s C`, `SoundFor s C` — the completeness and
  soundness relations against a class `C` of team properties.
* `definableClassWhere s Q` — the *fragment-relative* definable class
  (properties defined by a formula satisfying `Q`); `definableClass` is the
  `Q := fun _ => True` case. Logics with no unconditional cell (e.g. QBSML,
  whose closure properties hold only NE-free) state soundness against this.
* `downwardClosedProperties`, `unionClosedProperties`, `convexProperties`,
  `emptyTeamProperties`, `flatProperties` — the closure "cells" the
  completeness theorems characterise logics against.

## Main results

* `definableClass_subset` — the reusable soundness bridge.

## Roadmap

This file is phase 1 of the team-semantics family roadmap; see
`Core/Logic/Modal/README.md`. The closure predicates it packages come from
`Team/Closure.lean` (themselves mathlib `Order/` predicates).
-/

namespace Core.Logic.Team

/-! ### Team properties and definability -/

section Definability

variable {α : Type*} {Form : Type*}

/-- A **team property** over points `α` is a class of teams. A formula defines
    the property consisting of all teams in which it is true. Identical to the
    "team-set" `T : Set (Finset α)` of `Team/Closure.lean`; the alias marks the
    role in the expressive-completeness program. -/
abbrev TeamProperty (α : Type*) : Type _ := Set (Finset α)

/-- The team property **defined by** `φ` under support relation `s`: the class
    of all teams supporting `φ`. -/
def definedBy (s : Form → Finset α → Prop) (φ : Form) : TeamProperty α :=
  { t | s φ t }

/-- `P` is **definable** under `s` if some formula defines it. -/
def Definable (s : Form → Finset α → Prop) (P : TeamProperty α) : Prop :=
  ∃ φ : Form, P = definedBy s φ

/-- The class of team properties **definable** under `s` — written `⟦L⟧` in
    @cite{anttila-2025} for a logic `L` with support relation `s`. Expressive
    completeness is the statement `definableClass s = C`. -/
def definableClass (s : Form → Finset α → Prop) : Set (TeamProperty α) :=
  { P | Definable s P }

@[simp] theorem mem_definableClass {s : Form → Finset α → Prop}
    {P : TeamProperty α} : P ∈ definableClass s ↔ ∃ φ, P = definedBy s φ :=
  Iff.rfl

/-- A logic, given by its support relation `s`, is **expressively complete** for
    a class `C` of team properties iff the definable properties are exactly `C`. -/
def ExpressivelyCompleteFor (s : Form → Finset α → Prop)
    (C : Set (TeamProperty α)) : Prop :=
  definableClass s = C

/-- `s` is **sound for** `C`: every definable property lies in `C`. The easy half
    of expressive completeness, supplied by the per-logic closure theorems via
    `definableClass_subset`. -/
def SoundFor (s : Form → Finset α → Prop) (C : Set (TeamProperty α)) : Prop :=
  definableClass s ⊆ C

/-- **The soundness bridge.** If every formula's support set has closure property
    `C`, then every definable property does. Apply with a per-logic closure
    theorem — e.g. `definableClass_subset (fun φ => supClosed_support M φ)` yields
    the soundness half of BSML's expressive completeness. -/
theorem definableClass_subset {s : Form → Finset α → Prop}
    {C : TeamProperty α → Prop} (h : ∀ φ, C (definedBy s φ)) :
    definableClass s ⊆ { P | C P } := by
  intro P hP
  simp only [mem_definableClass] at hP
  obtain ⟨φ, rfl⟩ := hP
  exact h φ

/-- Expressive completeness implies soundness. -/
theorem ExpressivelyCompleteFor.soundFor {s : Form → Finset α → Prop}
    {C : Set (TeamProperty α)} (h : ExpressivelyCompleteFor s C) : SoundFor s C :=
  h.le

/-! ### Fragment-relative definability

Some logics have no unconditional closure cell — only a *fragment* of the
language does. The leading case is QBSML (@cite{aloni-vanormondt-2023}), whose
support is flat only for NE-free formulas (Proposition 4.1 / Fact 2). For such
logics the soundness statement is `definableClassWhere s Q ⊆ C`, where `Q`
carves out the fragment. -/

/-- The team properties **definable under `s` by a formula satisfying `Q`**.
    `definableClass s = definableClassWhere s (fun _ => True)`; the fragment
    predicate `Q` restricts to a sublanguage (e.g. the NE-free fragment). -/
def definableClassWhere (s : Form → Finset α → Prop) (Q : Form → Prop) :
    Set (TeamProperty α) :=
  { P | ∃ φ, Q φ ∧ P = definedBy s φ }

/-- **Fragment-relative soundness bridge.** If every `Q`-formula's support set
    has closure property `C`, every `Q`-definable property does. The fragment
    analogue of `definableClass_subset`. -/
theorem definableClassWhere_subset {s : Form → Finset α → Prop}
    {Q : Form → Prop} {C : TeamProperty α → Prop}
    (h : ∀ φ, Q φ → C (definedBy s φ)) :
    definableClassWhere s Q ⊆ { P | C P } := by
  rintro P ⟨φ, hQ, rfl⟩
  exact h φ hQ

end Definability

/-! ### Closure cells

The classes of team properties the expressive-completeness theorems
characterise logics against. The "cell" a logic occupies (see the cell map in
`Core/Logic/Modal/README.md`) is an intersection of these: BSML is
`convexProperties ∩ unionClosedProperties`, ML(⊆) and BSML⊘ are
`unionClosedProperties ∩ emptyTeamProperties`, dependence and inquisitive logic
are `downwardClosedProperties ∩ emptyTeamProperties`. -/

section Cells

variable {α : Type*}

/-- The class of **downward-closed** (persistent) team properties. -/
def downwardClosedProperties : Set (TeamProperty α) := { P | IsLowerSet P }

/-- The class of **convex** team properties (`Set.OrdConnected` under `⊆`). -/
def convexProperties : Set (TeamProperty α) := { P | Set.OrdConnected P }

/-- The class of team properties with the **empty-team property**. -/
def emptyTeamProperties : Set (TeamProperty α) := { P | ∅ ∈ P }

variable [DecidableEq α]

/-- The class of **union-closed** team properties. -/
def unionClosedProperties : Set (TeamProperty α) := { P | SupClosed P }

/-- The **flat** team properties: downward-closed ∩ union-closed ∩ empty-team
    (Anttila Proposition 2.2.2, via `Team/Closure.lean`'s `isFlat_iff`). -/
def flatProperties : Set (TeamProperty α) := { P | IsFlat P }

end Cells

end Core.Logic.Team
