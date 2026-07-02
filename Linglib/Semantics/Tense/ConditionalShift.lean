import Linglib.Semantics.Modality.HistoricalAlternatives

/-!
# Anderson Conditionals and Domain Expansion
[condoravdi-2002] [mizuno-2024] [schlenker-2004]

Formalizes the connection between backward temporal shifts and domain expansion
in conditionals. [mizuno-2024] argues that Japanese Anderson conditionals
use the Historical Present ([schlenker-2004]) to achieve domain expansion
without X-marking: Non-Past morphology shifts the evaluation time backward, and
live possibilities monotonically shrink as time develops, so the earlier-time
domain is larger. The shrinking assumption is [mizuno-2024]'s own; the
substrate encodes it as a backwards-closed `HistoricalAlternatives`, whose
independent anchor is [condoravdi-2002]'s historical modal base.

## Key results

- `hp_achieves_expansion` / `history_antitone` — backward time over a
  backwards-closed history yields domain expansion
- `trivialConsequent` / `nonTrivialConsequent` — the triviality puzzle
- `expansion_resolves_triviality` — a consequent-falsifying world makes the
  expansion strict (`D ⊂ D⁺`) and the expanded consequent non-trivial
- `nontrivial_conditional_excludes` — a non-trivial conditional's antecedent
  excludes a world: the conditional is informative
-/

namespace Tense.ConditionalShift

open Intensional (WorldTimeIndex)

/-! ### HP achieves expansion (Mizuno's argument) -/

section Expansion

variable {W : Type*} {T : Type*} [Preorder T]

/-- [mizuno-2024]'s argument: backward time + domain monotonicity yields
    expansion.

    If the world history is backwards-closed (worlds that agree up to `t`
    also agree up to `t' ≤ t`), then the historical alternatives at an
    earlier time are a superset of those at a later time. This is why
    O-marking (Non-Past / HP) in Japanese Anderson conditionals expands
    the domain without X-marking. -/
theorem hp_achieves_expansion
    (history : HistoricalAlternatives W T)
    (h_bc : history.backwardsClosed)
    (s₀ : WorldTimeIndex W T) (t' : T) (h_earlier : t' ≤ s₀.time)
    (w : W) (hw : w ∈ history s₀) :
    w ∈ history ⟨s₀.world, t'⟩ :=
  h_bc s₀.world w s₀.time t' h_earlier hw

/-- Under a backwards-closed history, the live possibilities at a world
    shrink monotonically as time develops: the set of historical
    alternatives is antitone in the time coordinate. This is the formal
    core of [mizuno-2024]'s argument — HP shifts the evaluation time
    backward, and backward time yields more historical alternatives,
    i.e., domain expansion. -/
theorem history_antitone
    (history : HistoricalAlternatives W T) (h_bc : history.backwardsClosed)
    (w : W) :
    Antitone (λ t => (history ⟨w, t⟩ : Set W)) :=
  λ _ _ h_le _ hw => hp_achieves_expansion history h_bc ⟨w, _⟩ _ h_le _ hw

end Expansion

/-! ### Conditional triviality and domain expansion -/

section Triviality

variable {W : Type*}

/-- Domain-restricted conditional: the standard Kratzer-style analysis of
    conditionals as restricted universal quantification over a modal domain.

      ∀ w ∈ D, antecedent(w) → consequent(w)

    [kratzer-1986]: if-clauses restrict the modal domain rather than
    functioning as binary connectives. This is the Prop-level counterpart
    of `Semantics.Conditionals.Restrictor.conditionalNecessity` (which
    operates over finite `(World → Bool)` for computation); the bridge is
    `Restrictor.conditionalNecessity_iff_domainRestricted`.

    Both X-marking and O-marking strategies for Anderson conditionals work
    by expanding D to D⁺ ⊃ D, making this quantification non-trivial. -/
def domainRestrictedConditional
    (domain : Set W) (antecedent consequent : W → Prop) : Prop :=
  ∀ w ∈ domain, antecedent w → consequent w

/-- A conditional is trivial when every world in the domain satisfies
    the consequent. The antecedent restriction does no work — the
    conditional is vacuously true regardless of what the antecedent says.
    In an Anderson conditional the consequent is an observed fact, so it
    holds throughout the non-expanded domain of live possibilities
    ([mizuno-2024], §2, citing Stalnaker 1975 and von Fintel 1999). -/
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
    consequent trivial and the expanded domain contains a world where the
    consequent fails, then the expansion is *strict* (the witness cannot be
    live — [mizuno-2024]'s D ⊂ D⁺) and the expanded consequent is
    non-trivial.

    This completes the HP/X-marking argument:
    1. `hp_achieves_expansion` — backward time shift expands the domain
    2. `expansion_resolves_triviality` — the expanded conditional is
       non-trivial -/
theorem expansion_resolves_triviality
    (smallDomain expandedDomain : Set W)
    (consequent : W → Prop)
    (h_subset : smallDomain ⊆ expandedDomain)
    (h_trivial : trivialConsequent smallDomain consequent)
    (w : W) (hw : w ∈ expandedDomain) (hw_fails : ¬ consequent w) :
    smallDomain ⊂ expandedDomain ∧
      nonTrivialConsequent expandedDomain consequent :=
  ⟨(Set.ssubset_iff_of_subset h_subset).mpr
      ⟨w, hw, λ h_live => hw_fails (h_trivial w h_live)⟩,
    w, hw, hw_fails⟩

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

end Triviality

end Tense.ConditionalShift
