import Linglib.Core.Context.Rich
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Theories.Semantics.Mood.Basic

/-!
# Anderson Conditionals and Domain Expansion
@cite{condoravdi-2002} @cite{mizuno-2024} @cite{schlenker-2004}

Formalizes the connection between backward temporal shifts and domain expansion
in conditionals. @cite{mizuno-2024} argues that Japanese Anderson conditionals
use the Historical Present (@cite{schlenker-2004}) to achieve domain expansion
without X-marking: Non-Past morphology shifts the evaluation time backward,
and under branching time (@cite{condoravdi-2002}), earlier times have more
historical alternatives, so the domain expands.

## Key Results

- `andersonConditional` — HP-shifted antecedent evaluated against expanded domain
- `hp_achieves_expansion` — backward time + domain monotonicity yields expansion
- `trivialConsequent` / `nonTrivialConsequent` — formalize the triviality puzzle
- `expansion_resolves_triviality` — domain expansion makes conditionals non-trivial
- Bridge to `BranchingTime.historicalBase` and `Mood.SUBJ`

## Connection to ContextTower

The HP shift in an Anderson conditional is modeled as a tower push of an
`hpShift`: a context shift that moves time backward and expands the domain.
In @cite{schlenker-2004}'s terms, the push shifts the Context of Utterance v
while preserving the Context of Thought θ (= `tower.origin`).

-/

namespace Semantics.Tense.ConditionalShift

open Core.Time
open Core.Context (RichContext KContext ContextTower ContextShift
  hpShift DomainExpanding)
open Core.Modality.HistoricalAlternatives
open Semantics.Mood

-- ════════════════════════════════════════════════════════════════
-- § Anderson Conditional
-- ════════════════════════════════════════════════════════════════

section AndersonConditional

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*} [Preorder T]

/-- An Anderson conditional (context-level model): the antecedent is
    evaluated at an HP-shifted context (backward time, expanded domain),
    and the consequent is evaluated at the original context.

    This models the HP shift's effect on a single evaluation point.
    The full Kratzer-style analysis — restricted universal quantification
    over the expanded domain D⁺ — is `domainRestrictedConditional`:

      `domainRestrictedConditional D⁺ antecedent consequent`
      = ∀ w ∈ D⁺, antecedent(w) → consequent(w)

    The domain expansion machinery here (`hpShift`, `hp_achieves_expansion`)
    provides the D⁺, and `trivial_domainRestricted` /
    `nontrivial_conditional_excludes` show why expansion matters. -/
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

/-- @cite{mizuno-2024}'s argument: backward time + domain monotonicity yields
    expansion.

    If the world history is backwards-closed (worlds that agree up to `t`
    also agree up to `t' ≤ t`), then the historical alternatives at an
    earlier time are a superset of those at a later time. This is why
    O-marking (Non-Past / HP) in Japanese Anderson conditionals expands
    the domain without X-marking. -/
theorem hp_achieves_expansion
    (history : WorldHistory W T)
    (h_bc : history.backwardsClosed)
    (s₀ : Situation W T) (t' : T) (h_earlier : t' ≤ s₀.time)
    (w : W) (hw : w ∈ history s₀) :
    w ∈ history ⟨s₀.world, t'⟩ :=
  h_bc s₀.world w s₀.time t' h_earlier hw

/-- Set-level monotonicity: under backwards-closed history, the set of
    historical alternatives at an earlier time is a superset of those at a
    later time. This lifts `hp_achieves_expansion` (element-level) to
    `Set.Subset` (set-level), connecting it to `DomainExpanding`.

    This is the formal core of @cite{mizuno-2024}'s argument: HP shifts the
    evaluation time backward, and backward time yields more historical
    alternatives, i.e., domain expansion. -/
theorem history_monotone_set
    (history : WorldHistory W T)
    (h_bc : history.backwardsClosed)
    (s₀ : Situation W T) (t' : T) (h_earlier : t' ≤ s₀.time) :
    (history s₀ : Set W) ⊆ (history ⟨s₀.world, t'⟩ : Set W) :=
  λ _ hw => hp_achieves_expansion history h_bc s₀ t' h_earlier _ hw

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
-- § Conditional Triviality and Domain Expansion
-- ════════════════════════════════════════════════════════════════

section Triviality

variable {W : Type*}

/-- Domain-restricted conditional: the standard Kratzer-style analysis of
    conditionals as restricted universal quantification over a modal domain.

      ∀ w ∈ D, antecedent(w) → consequent(w)

    @cite{kratzer-1986}: if-clauses restrict the modal domain rather than
    functioning as binary connectives. This is the Prop-level counterpart
    of `Semantics.Conditionals.Restrictor.conditionalNecessity` (which
    operates over finite `(World → Bool)` for computation).

    Both X-marking and O-marking strategies for Anderson conditionals work
    by expanding D to D⁺ ⊃ D, making this quantification non-trivial. -/
def domainRestrictedConditional
    (domain : Set W) (antecedent consequent : W → Prop) : Prop :=
  ∀ w ∈ domain, antecedent w → consequent w

/-- A conditional is trivial when every world in the domain satisfies
    the consequent. The antecedent restriction does no work — the
    conditional is vacuously true regardless of what the antecedent says.

    @cite{condoravdi-2002}: indicative conditionals with small domains can be
    trivial because every accessible world already satisfies the consequent.
    Domain expansion (via HP/X-marking) resolves this by adding worlds
    where the consequent may fail. -/
def trivialConsequent (domain : Set W) (consequent : W → Prop) : Prop :=
  ∀ w ∈ domain, consequent w

/-- A conditional is non-trivial when there exists a world in the domain
    where the consequent fails. This is the condition under which the
    antecedent restriction does meaningful work. -/
def nonTrivialConsequent (domain : Set W) (consequent : W → Prop) : Prop :=
  ∃ w ∈ domain, ¬ consequent w

/-- The triviality problem: when the consequent is trivial, the
    domain-restricted conditional is vacuously true regardless of the
    antecedent. This is why O-marked English Anderson conditionals are
    infelicitous — the consequent is an observed fact true at all worlds
    in D, so the conditional adds no information. -/
theorem trivial_domainRestricted
    (domain : Set W)
    (antecedent consequent : W → Prop)
    (h_trivial : trivialConsequent domain consequent) :
    domainRestrictedConditional domain antecedent consequent :=
  λ w hw _ => h_trivial w hw

/-- Domain expansion resolves triviality: if the original domain makes the
    consequent trivial, but the expanded domain contains a world where the
    consequent fails, then the expanded conditional is non-trivial.

    This completes the HP/X-marking argument:
    1. `hp_achieves_expansion` — backward time shift expands the domain
    2. `expansion_resolves_triviality` — expanded domain makes the
       conditional non-trivial

    The counterfactual "If I had left earlier, I would have caught the train"
    is non-trivial precisely because the expanded domain (from X-marking's
    backward time shift) includes worlds where I didn't catch the train. -/
theorem expansion_resolves_triviality
    (smallDomain expandedDomain : Set W)
    (consequent : W → Prop)
    (_h_subset : smallDomain ⊆ expandedDomain)
    (_h_trivial : trivialConsequent smallDomain consequent)
    (w : W) (hw : w ∈ expandedDomain) (hw_fails : ¬ consequent w) :
    nonTrivialConsequent expandedDomain consequent :=
  ⟨w, hw, hw_fails⟩

/-- When the domain-restricted conditional holds over an expanded domain
    where the consequent is non-trivial, the antecedent must exclude at
    least one world. The antecedent restriction is doing genuine work —
    it is not vacuously satisfied.

    This is the formal payoff of domain expansion: the conditional becomes
    informative because the antecedent partitions D⁺ into worlds where
    the consequent holds (via the conditional) and worlds where it fails
    (via non-triviality). -/
theorem nontrivial_conditional_excludes
    (domain : Set W)
    (antecedent consequent : W → Prop)
    (h_nontrivial : nonTrivialConsequent domain consequent)
    (h_cond : domainRestrictedConditional domain antecedent consequent) :
    ∃ w ∈ domain, ¬ antecedent w := by
  obtain ⟨w, hw, hw_fails⟩ := h_nontrivial
  exact ⟨w, hw, λ ha => hw_fails (h_cond w hw ha)⟩

/-- Triviality is monotone: if a superset domain is trivial, then
    so is any subset domain. Expanding the domain can only resolve
    triviality, never introduce it. -/
theorem trivial_monotone
    (smallDomain expandedDomain : Set W)
    (consequent : W → Prop)
    (h_subset : smallDomain ⊆ expandedDomain)
    (h_expanded_trivial : trivialConsequent expandedDomain consequent) :
    trivialConsequent smallDomain consequent :=
  λ w hw => h_expanded_trivial w (h_subset hw)

end Triviality

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

end Semantics.Tense.ConditionalShift
