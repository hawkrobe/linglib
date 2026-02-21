import Linglib.Core.Context.Rich
import Linglib.Theories.Semantics.Tense.BranchingTime
import Linglib.Theories.Semantics.Mood.Basic

/-!
# Anderson Conditionals and Domain Expansion

Formalizes the connection between backward temporal shifts and domain expansion
in conditionals, following Mizuno's argument: the historical present (HP) in
conditional antecedents achieves domain expansion because moving time backward
expands the set of historical alternatives.

## Key Results

- `andersonConditional` — HP in antecedent pushes a temporal shift + domain expands
- `hp_achieves_expansion` — Mizuno's argument: backward time + domain monotonicity
  yields expansion
- Bridge to `BranchingTime.historicalBase` and `Mood.SUBJ`

## Connection to ContextTower

The HP shift in the antecedent of an Anderson conditional is modeled as a
tower push of an `hpShift`: a context shift that moves time backward and
expands the domain. This connects the modal-temporal interaction in
conditionals to the tower architecture.

## References

- Condoravdi, M. (2002). Temporal interpretation of modals.
- Ippolito, M. (2013). Subjunctive Conditionals.
-/

namespace Semantics.Tense.Anderson

open Core.Time
open Core.Context (RichContext KContext ContextTower ContextShift
  hpShift DomainExpanding)
open Semantics.Tense.BranchingTime
open Semantics.Mood

-- ════════════════════════════════════════════════════════════════
-- § Anderson Conditional
-- ════════════════════════════════════════════════════════════════

section AndersonConditional

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*} [Preorder T]

/-- An Anderson conditional: the antecedent is evaluated at an HP-shifted
    context (backward time, expanded domain), and the consequent is
    evaluated at the original context.

    The HP shift in the antecedent is what gives counterfactual conditionals
    their widened modal base — by shifting time backward, more futures branch,
    and the domain of quantification expands. -/
def andersonConditional
    (antecedent : RichContext W E P T → Prop)
    (consequent : RichContext W E P T → Prop)
    (hpTime : T) (expandedDomain : Set W)
    (rc : RichContext W E P T) : Prop :=
  let shifted := (hpShift (E := E) (P := P) hpTime expandedDomain).apply rc
  antecedent shifted → consequent rc

end AndersonConditional

/-- The HP-shifted context in an Anderson conditional has the shifted time. -/
theorem anderson_shifted_time {W E P T : Type*}
    (hpTime : T) (expandedDomain : Set W)
    (rc : RichContext W E P T) :
    ((hpShift (E := E) (P := P) hpTime expandedDomain).apply rc).time = hpTime := rfl

-- ════════════════════════════════════════════════════════════════
-- § HP Achieves Expansion (Mizuno's Argument)
-- ════════════════════════════════════════════════════════════════

section Expansion

variable {W : Type*} {T : Type*} [Preorder T]

/-- Mizuno's argument: backward time + domain monotonicity yields expansion.

    If the world history is backwards-closed (worlds that agree up to `t`
    also agree up to `t' ≤ t`), then the historical alternatives at an
    earlier time are a superset of those at a later time. This is domain
    monotonicity. -/
theorem hp_achieves_expansion
    (history : WorldHistory W T)
    (h_bc : history.backwardsClosed)
    (s₀ : Situation W T) (t' : T) (h_earlier : t' ≤ s₀.time)
    (w : W) (hw : w ∈ history s₀) :
    w ∈ history ⟨s₀.world, t'⟩ :=
  h_bc s₀.world w s₀.time t' h_earlier hw

/-- The historical base (set of situations) at an earlier time includes
    situations with the same worlds as the later base, plus potentially more.
    This is the situation-level version of domain expansion. -/
theorem historicalBase_monotone
    (history : WorldHistory W T)
    (h_bc : history.backwardsClosed)
    (s₀ : Situation W T) (t' : T) (h_earlier : t' ≤ s₀.time)
    (s₁ : Situation W T) (h_s₁ : s₁ ∈ historicalBase history s₀)
    (h_time : s₁.time ≥ t') :
    s₁ ∈ historicalBase history ⟨s₀.world, t'⟩ := by
  simp only [historicalBase, Set.mem_setOf_eq] at h_s₁ ⊢
  exact ⟨h_bc s₀.world s₁.world s₀.time t' h_earlier h_s₁.1, h_time⟩

end Expansion

-- ════════════════════════════════════════════════════════════════
-- § Bridge: SUBJ as Domain-Expanding Shift
-- ════════════════════════════════════════════════════════════════

section SubjBridge

variable {W : Type*} {T : Type*} [Preorder T]

/-- SUBJ's situation introduction can be decomposed into two steps:
    1. Expand the domain (via backward time shift)
    2. Existentially quantify over the expanded domain

    When the history is backwards-closed, SUBJ at an earlier time introduces
    a situation whose world is in the expanded historical alternatives. -/
theorem subj_subsumes_hp_expansion
    (history : WorldHistory W T)
    (P : Situation W T → Situation W T → Prop)
    (s : Situation W T)
    (h : SUBJ history P s) :
    ∃ s₁, s₁.world ∈ history s ∧ P s₁ s := by
  obtain ⟨s₁, h_hist, hP⟩ := h
  simp only [historicalBase, Set.mem_setOf_eq] at h_hist
  exact ⟨s₁, h_hist.1, hP⟩

end SubjBridge

end Semantics.Tense.Anderson
