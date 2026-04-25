import Linglib.Theories.Semantics.Dynamic.Intensional

/-!
# Bilateral Denotations for ICDRT Contexts

Bilateral (positive/negative) update semantics instantiated for
ICDRT contexts (@cite{krahmer-muskens-1995}). This captures the
DN-DRT / BUS mechanism applied to ICDRT's `IContext` type.

This bilateral structure is NOT the same as @cite{hofmann-2025}'s full
ICDRT analysis, which derives accessibility from veridicality + discourse
consistency rather than bilateral negation (§5.1.1). The bilateral approach
cannot handle disagreement or modal subordination contexts.

## Cross-cutting smell: two competing approaches to cross-disjunct anaphora

This file and `Phenomena/Anaphora/Studies/Hofmann2025.lean` are two
formalizations of the same empirical territory — cross-negation and
cross-disjunct anaphora (the "bathroom sentence" pattern: *Either
there's no bathroom, or it's upstairs*). They are not stacked
extensions; they are competitors.

| Approach | Mechanism | Solves | Doesn't solve |
|----------|-----------|--------|---------------|
| Bilateral (this file) | Two update channels; negation = swap | DNE, bathroom sentence | Disagreement, modal subordination, speaker-vs-hearer commitment |
| Full ICDRT (@cite{hofmann-2025}) | Propositional drefs + per-speaker DiscContext + veridicality classification | All of the above + three-way veridical/hypothetical/counterfactual | Pays in intensional machinery |

The bilateral approach is the lighter formalism — a single information
state with two update polarities. The full ICDRT machinery (per-speaker
commitment sets, three-way veridicality) is heavier but covers cases
the bilateral approach structurally cannot. Choose by phenomenon: if
disagreement or modal subordination are in scope, use the full ICDRT;
if only the basic bathroom pattern matters, the bilateral apparatus
here suffices.

The empirical comparison is formalized in
`Phenomena/Anaphora/Studies/Hofmann2025.lean §7`, which proves both
approaches solve the bathroom sentence and identifies the four cases
(disagreement, modal subordination, three-way veridicality
classification, negated existential truth conditions) where ICDRT is
strictly more expressive.
-/

namespace Semantics.Dynamic.Bilateral.ICDRT

open Semantics.Dynamic.Core
open Core


/--
Bilateral ICDRT denotation: positive and negative updates.

Following @cite{krahmer-muskens-1995}'s bilateral negation: formulas have
both positive and negative interpretations, and negation swaps them.
This gives double negation elimination (DNE), which Hofmann uses but
does not require — ICDRT's flat update with propositional drefs handles
double negation via complementation over propositional drefs (§4.1).

Note: this bilateral structure captures the DN-DRT / BUS mechanism
(§5.1.1) but NOT the full ICDRT analysis. ICDRT derives accessibility
from veridicality + discourse consistency, which covers cases (modal
subordination, disagreement) that bilateral accounts cannot (§5.1.1).
-/
structure BilateralICDRT (W : Type*) (E : Type*) where
  /-- Positive update (assertion) -/
  positive : IContext W E → IContext W E
  /-- Negative update (denial) -/
  negative : IContext W E → IContext W E

namespace BilateralICDRT

variable {W E : Type*}

/-- Negation: swap positive and negative -/
def neg (φ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := φ.negative
  negative := φ.positive

/-- Double negation elimination (definitional). -/
@[simp]
theorem neg_neg (φ : BilateralICDRT W E) : φ.neg.neg = φ := rfl

/-- Atomic proposition -/
def atom (prop : W → Prop) : BilateralICDRT W E where
  positive := λ c => c.update prop
  negative := λ c => c.update (λ w => ¬prop w)

/-- Conjunction: sequence positive updates -/
def conj (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := λ c => ψ.positive (φ.positive c)
  negative := λ c => φ.negative c ∪ (φ.positive c ∩ ψ.negative (φ.positive c))

/-- Notation -/
prefix:max "∼" => neg
infixl:65 " ⊗ " => conj

end BilateralICDRT


/--
Extend context with random assignment for variable v.

Only assigns real entities (not ⋆), tracking assignments in all worlds (flat).
-/
def extendContext {W E : Type*}
    (c : IContext W E)
    (v : IVar)
    (domain : Set E)
    : IContext W E :=
  { jw |
    ∃ i e,
      (i, jw.2) ∈ c ∧
      e ∈ domain ∧
      jw.1 = i.updateIndivConst v (.some e) }

/--
Bilateral existential with flat update.

The existential introduces drefs in both positive and negative
updates. This is what makes double negation accessible:

⟦¬¬∃x.P(x)⟧^+ = ⟦∃x.P(x)⟧^+ (by DNE)

The dref x introduced in the inner scope is accessible in the outer scope
because flat update introduces it globally.
-/
def BilateralICDRT.exists_ {W E : Type*}
    (_p : PVar)
    (v : IVar)
    (domain : Set E)
    (body : BilateralICDRT W E)
    : BilateralICDRT W E where
  positive := λ c =>
    let extended := extendContext c v domain
    body.positive extended
  negative := λ c =>
    { gw ∈ c | ∀ e ∈ domain,
        let g' := gw.1.updateIndivConst v (.some e)
        (g', gw.2) ∉ body.positive (extendContext c v domain) }


/-- Context extension includes witnesses: if (i, w) ∈ c and e ∈ domain,
    then the extended pair is in the extended context. -/
theorem extendContext_mem {W E : Type*}
    (c : IContext W E) (v : IVar) (domain : Set E)
    (i : ICDRTAssignment W E) (w : W) (e : E)
    (hc : (i, w) ∈ c) (he : e ∈ domain) :
    (i.updateIndivConst v (.some e), w) ∈ extendContext c v domain :=
  ⟨i, e, hc, he, rfl⟩

/-- Atomic positive and negative updates cover the context: every
    assignment-world pair is either verified or falsified. -/
theorem atom_complementary {W E : Type*} (prop : W → Prop) (c : IContext W E) :
    (BilateralICDRT.atom prop).positive c ∪ (BilateralICDRT.atom prop).negative c = c :=
  Set.ext (λ ⟨_, w⟩ =>
    ⟨λ h => h.elim And.left And.left,
     λ h => (em (prop w)).elim (Or.inl ⟨h, ·⟩) (Or.inr ⟨h, ·⟩)⟩)

/-- Atomic positive and negative updates are disjoint: no pair is both
    verified and falsified. -/
theorem atom_disjoint {W E : Type*} (prop : W → Prop) (c : IContext W E) :
    (BilateralICDRT.atom prop).positive c ∩ (BilateralICDRT.atom prop).negative c = ∅ :=
  Set.ext (λ ⟨_, _⟩ =>
    ⟨λ ⟨⟨_, hp⟩, ⟨_, hnp⟩⟩ => hnp hp, False.elim⟩)


end Semantics.Dynamic.Bilateral.ICDRT
