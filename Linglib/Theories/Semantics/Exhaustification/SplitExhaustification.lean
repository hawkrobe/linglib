import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! # Split Exhaustification: General Theory
@cite{alonso-ovalle-moghiseh-2025}

General theorems grounding the split exhaustification analysis of
Existential Free Choice Items (EFCIs). These results hold for arbitrary
domains — not specific world types — capturing the logical core of
the analysis at full generality.

The study file `Phenomena/Modality/Studies/AlonsoOvalleMoghiseh2025.lean`
verifies each result computationally via `native_decide` on 2-book worlds.
This file proves them structurally, without `native_decide`.

## Architecture

Split exhaustification factors the exhaustivity operator into two
independent components:

- **O_σ** (scalar): exhaustifies w.r.t. numeral-scale alternatives
  (e.g., "at least 2" for "one"), clause-bounded below modals
- **O_EXH-D** (domain): exhaustifies w.r.t. pre-exhaustified subdomain
  alternatives, scoping above modals

The split is necessary because single-operator exhaustification with all
alternatives yields ⊥ (`exhAll`) or vacuity (`exhB`) for 2-element
domains (`root_full_exh_contradiction`).

## Results

1. **Scalar uniqueness**: O_σ yields "exactly one" (`scalar_exh_uniqueness`)
2. **Exclusive-alt negation**: O_EXH-D yields "at least two"
   (`neg_all_exclusive_alts`)
3. **Two-element FC**: for |D| = 2, "at least two" = "all"
   (`fc_two_element`)
4. **Root contradiction**: full exh on |D| = 2 → ⊥
   (`root_full_exh_contradiction`)
5. **DE weakening**: antecedent strengthening weakens conditionals
   (`strict_antecedent_weakening`)
6. **DE domain vacuousness**: domain alts entailed in DE
   (`de_domain_alt_entailed`)
-/

namespace Exhaustification.SplitExhaustification


-- ============================================================
-- § 1. Scalar Exhaustification → Uniqueness
-- ============================================================

/-!
## Scalar Uniqueness

O_σ exhaustifies "at least one" w.r.t. the scalar alternative "at least
two," yielding "exactly one." This is yek-i's root reading: the partial
exhaustification rescue mechanism prunes domain alternatives and applies
only O_σ, producing uniqueness without modal insertion.
-/

/-- **Scalar uniqueness**: "at least one and not at least two" is
equivalent to "exactly one."

This is the semantic content of O_σ: with a single scalar alternative
(the next numeral on the Horn scale), innocent exclusion trivially
returns that alternative (singleton MCE), and its negation gives
uniqueness. General over any domain D — no finiteness needed. -/
theorem scalar_exh_uniqueness {D : Type*} (P : D → Prop) :
    ((∃ d, P d) ∧ ¬∃ d₁ d₂, d₁ ≠ d₂ ∧ P d₁ ∧ P d₂) ↔
    ∃ d, P d ∧ ∀ e, P e → e = d := by
  constructor
  · rintro ⟨⟨d, hd⟩, hNotTwo⟩
    exact ⟨d, hd, fun e he => by_contra fun hne =>
      hNotTwo ⟨e, d, hne, he, hd⟩⟩
  · rintro ⟨d, hd, huniq⟩
    exact ⟨⟨d, hd⟩, fun ⟨d₁, d₂, hne, h1, h2⟩ =>
      hne ((huniq d₁ h1).trans (huniq d₂ h2).symm)⟩


-- ============================================================
-- § 2. Domain Exhaustification → Free Choice
-- ============================================================

/-!
## Free Choice from Exclusive-Alt Negation

O_EXH-D negates pre-exhaustified domain alternatives. Each says "d is
the EXCLUSIVE satisfier" (P d ∧ ∀e≠d, ¬P e). Negating all of these,
combined with existence, yields a cardinality lower bound:

- **General**: at least 2 satisfy P
- **|D| = 2**: both satisfy P (full free choice)

The general-to-specific factoring explains why FC emerges specifically
from the 2-element structure: "at least 2 out of 2" = "all."
-/

/-- **Exclusive-alt negation → plurality**: if at least one element
satisfies P, and no element is the exclusive satisfier, then at least
two distinct elements satisfy P.

This is the content of O_EXH-D: each pre-exhaustified domain alternative
is innocently excludable (they form a single MCE since they can all be
simultaneously negated), and negating all of them forces multiple
satisfiers. General over any domain D. -/
theorem neg_all_exclusive_alts {D : Type*} (P : D → Prop)
    (hExist : ∃ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧ P d₁ ∧ P d₂ := by
  obtain ⟨d, hd⟩ := hExist
  by_contra hNoTwo
  exact hNegExcl d ⟨hd, fun e hne hPe => hNoTwo ⟨e, d, hne, hPe, hd⟩⟩

/-- **Two-element free choice**: for a two-element domain, existence plus
negation of all exclusive alternatives forces every element to satisfy P.

This completes the FC derivation for yek-i under deontic modals:
O_EXH-D negates the two exclusive modal alternatives, and since |D| = 2,
"at least 2 satisfy ◇P" becomes "both satisfy ◇P" — free choice. -/
theorem fc_two_element (P : Fin 2 → Prop)
    (hExist : ∃ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    ∀ d, P d := by
  obtain ⟨d₁, d₂, hne, h1, h2⟩ := neg_all_exclusive_alts P hExist hNegExcl
  intro d; fin_cases d <;> fin_cases d₁ <;> fin_cases d₂ <;> simp_all


-- ============================================================
-- § 3. Root Contradiction
-- ============================================================

/-!
## Root Contradiction: Why Rescue Mechanisms Are Needed

For a 2-element domain, full exhaustification (negating both the scalar
alternative and both exclusive domain alternatives) is contradictory.
This motivates the EFCI rescue typology (Table 2):

- *vreun* (−,−): no rescue → ungrammatical in root
- *irgendein* (+,−): modal insertion → covert □ → epistemic ignorance
- *yek-i* (−,+): partial exhaustification → O_σ only → uniqueness
-/

/-- **Root contradiction**: asserting "at least one," negating "all"
(scalar), and negating both exclusive domain alternatives yields ⊥
for a two-element domain.

Proof: negating both exclusives gives FC (both hold), contradicting
"not all." This is a STRUCTURAL impossibility, not an artifact of
the specific world type used for computational verification. -/
theorem root_full_exh_contradiction (P : Fin 2 → Prop)
    (hExist : ∃ d, P d)
    (hNotAll : ¬∀ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    False :=
  hNotAll (fc_two_element P hExist hNegExcl)

/-- Uniqueness (from scalar-only exhaustification) is satisfiable:
unlike full exhaustification, O_σ alone yields a consistent result.
This witnesses that partial exhaustification is a genuine rescue. -/
theorem uniqueness_satisfiable :
    ∃ P : Fin 2 → Prop, ∃ d, P d ∧ ∀ e, P e → e = d :=
  ⟨(· = 0), 0, rfl, fun _ h => h⟩

/-- Uniqueness precludes universality: "exactly one" entails "not all"
for any domain with at least two elements. This shows O_σ's result is
strictly between the assertion and the full-exh contradiction. -/
theorem uniqueness_precludes_universality {D : Type*} {a b : D}
    (hab : a ≠ b) (P : D → Prop)
    (hUniq : ∃ d, P d ∧ ∀ e, P e → e = d) :
    ¬∀ d, P d := by
  obtain ⟨d, _, huniq⟩ := hUniq
  intro hall
  exact hab ((huniq a (hall a)).trans (huniq b (hall b)).symm)


-- ============================================================
-- § 4. DE Contexts: Maximize Strength & Domain Vacuousness
-- ============================================================

/-!
## DE Contexts: Plain Existential Force

Two independent mechanisms ensure EFCIs contribute plain existential
force in downward-entailing contexts:

1. **Maximize Strength blocks O_σ**: scalar exhaustification strengthens
   the conditional's antecedent, which WEAKENS the overall conditional.
   Since this loses information, Maximize Strength prevents it.

2. **O_EXH-D is vacuous**: the full-domain conditional entails each
   subdomain conditional (since P d → ∃x P x), so domain alternatives
   are weaker than the assertion and not in NW — nothing to exclude.
-/

/-- **Antecedent monotonicity**: strengthening a conditional's antecedent
weakens the conditional. If Q → P (Q is stronger), then (P → R) entails
(Q → R) (but not vice versa in general).

In EFCI terms: ∃!x P(x) → ∃x P(x), so (∃x → R) entails (∃!x → R).
Scalar exhaustification replaces ∃x with ∃!x in the antecedent,
weakening the matrix. Maximize Strength blocks this. -/
theorem antecedent_weakening {P Q R : Prop} (hQP : Q → P) :
    (P → R) → (Q → R) :=
  fun hPR hQ => hPR (hQP hQ)

/-- **Strict weakening witness**: when Q ⊂ P strictly (Q → P but
∃w with P w, ¬Q w, ¬R w), there is a world where the weaker conditional
P → R fails but the stronger conditional Q → R holds.

This witnesses the information loss: the world where P holds and Q doesn't
(e.g., "bought both books") makes (P → R) false but (Q → R) vacuously
true, demonstrating strict weakening. -/
theorem strict_antecedent_weakening {W : Type*} (P Q R : W → Prop)
    (hWitness : ∃ w, P w ∧ ¬Q w ∧ ¬R w) :
    ∃ w, ¬(P w → R w) ∧ (Q w → R w) := by
  obtain ⟨w, hPw, hNQw, hNRw⟩ := hWitness
  exact ⟨w, fun hPR => hNRw (hPR hPw), fun hQw => absurd hQw hNQw⟩

/-- **Domain alternatives entailed in DE**: the full-domain conditional
(∃x P(x)) → R entails each subdomain conditional P(d) → R, since
P d → ∃x P(x) for any d.

Consequence: domain alternatives are weakened by the DE operator (they
are entailed by the assertion), so they are not in NW(assertion) and
IE is empty — O_EXH-D contributes nothing. -/
theorem de_domain_alt_entailed {D : Type*} (P : D → Prop) (R : Prop) (d : D) :
    ((∃ x, P x) → R) → (P d → R) :=
  fun h hPd => h ⟨d, hPd⟩


end Exhaustification.SplitExhaustification
