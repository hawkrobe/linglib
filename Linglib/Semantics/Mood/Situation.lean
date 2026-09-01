/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Reference.Context.Shifts

/-!
# Situation-level mood operators

[mendes-2025]'s mood operators work like determiners for situations:
`SUBJ` introduces a new situation dref constrained to the historical
alternatives of the anchor (like indefinite *a*), `IND` retrieves an
existing situation and tests same-worldhood (like definite *the*).
The Subordinate Future of Portuguese/Spanish — present morphology with
future reference in subordinate contexts — is his main application:
SF is subjunctive, introducing a future situation dref that the main
clause retrieves for temporal anchoring (`conditionalSF`).

## Main declarations

* `SitPred`, `sameWorld` — situation predicates and the modal kernel.
* `SUBJ`, `IND` — the situation-level mood operators.
* `conditionalSF` — the SF conditional.
* `nonVeridical`, `subj_nonveridical` — subjunctive non-veridicality.
* `subjShift` — SUBJ as a tower context shift.
-/

namespace Mood

open Intensional (Index)
open HistoricalAlternatives

/-- A situation predicate, relating a described situation to its anchor. -/
abbrev SitPred (W T : Type*) := Index W T → Index W T → Prop

/-- The modal kernel: two situations share their world coordinate.
`abbrev` so `decide`/`rw` see through it. -/
abbrev sameWorld {W T : Type*}
    (s₁ s₂ : Index W T) : Prop :=
  s₁.world = s₂.world

variable {W T : Type*} (history : HistoricalAlternatives W T)
  (P : SitPred W T) (s₀ : Index W T)

/-- The subjunctive introduces a new situation dref from the historical
alternatives of the anchor — an indefinite for situations
([mendes-2025], Definition on p.29). -/
def SUBJ [LE T] : Prop :=
  ∃ s₁ : Index W T,
    s₁ ∈ historicalBase history s₀ ∧ P s₁ s₀

/-- The indicative retrieves existing situations and tests that they
share a world — a definite for situations ([mendes-2025], Definition
on p.29). -/
def IND (s₁ s₂ : Index W T) : Prop :=
  sameWorld s₂ s₁ ∧ P s₂ s₁

/-- A conditional with an SF antecedent: `SUBJ` introduces the *if*
situation, and the consequent is temporally anchored to it — why SF
enables future reference ([mendes-2025]). -/
def conditionalSF [LE T]
    (antecedent : Index W T → Prop)
    (consequent : Index W T → Index W T → Prop)
    (s₀ : Index W T) : Prop :=
  SUBJ history (λ s₁ s₀' => antecedent s₁ → consequent s₁ s₀') s₀

/-- Surviving `IND` means the two situations share a world. -/
theorem ind_same_world (s₁ s₂ : Index W T)
    (h : IND P s₁ s₂) : s₂.world = s₁.world :=
  h.1

/-- With a reflexive history, the anchor itself is always an option. -/
theorem subj_current_option [Preorder T]
    (h_refl : history.reflexive) (h_P : P s₀ s₀) :
    SUBJ history P s₀ :=
  ⟨s₀, ⟨h_refl s₀, le_refl s₀.time⟩, h_P⟩

/-- The introduced situation is a temporal anchor at or after the base
situation's time — the mechanism SF exploits for future reference, and
the parallel to attitude verbs shifting embedded evaluation to matrix
event time (`Studies/VonStechow2009.lean`). -/
theorem subj_temporal_anchor [LE T]
    (h : SUBJ history P s₀) :
    ∃ s₁, s₁ ∈ historicalBase history s₀ ∧ s₁.time ≥ s₀.time ∧ P s₁ s₀ := by
  obtain ⟨s₁, h_hist, h_P⟩ := h
  exact ⟨s₁, h_hist, h_hist.2, h_P⟩

/-! ### Non-veridicality -/

/-- A propositional operator is non-veridical iff `F p` can hold
without `p` ([giannakidou-1998]). -/
def nonVeridical
    (F : (Index W T → Prop) → Index W T → Prop) : Prop :=
  ∃ (P : Index W T → Prop) (s : Index W T),
    F P s ∧ ¬P s

/-- `SUBJ` is non-veridical whenever the history branches: the
introduced situation may differ from the actual one. -/
theorem subj_nonveridical [LE T]
    (h_branching : ∃ s₀ s₁ : Index W T,
      s₁ ∈ historicalBase history s₀ ∧ s₀ ≠ s₁) :
    nonVeridical (λ P s₀ => SUBJ history (λ s₁ _ => P s₁) s₀) := by
  obtain ⟨s₀, s₁, h₁, hne⟩ := h_branching
  exact ⟨(· = s₁), s₀, ⟨s₁, h₁, rfl⟩, hne⟩

/-! ### SUBJ as tower push

Entering a subjunctive clause pushes a mood-labeled context shift to
the coordinates of the introduced situation; the existential
quantification over situations is a separate semantic step. The tower
version tracks depth for depth-sensitive operations (presupposition,
tense indexing). -/

/-- The mood-labeled context shift to the introduced situation's world
and time. -/
def subjShift {E P : Type*} (newWorld : W) (newTime : T) :
    Semantics.Context.ContextShift (Semantics.Context.KContext W E P T) where
  apply := λ c => { c with world := newWorld, time := newTime }
  label := .mood

end Mood
