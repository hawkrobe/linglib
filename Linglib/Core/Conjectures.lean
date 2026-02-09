/-
# Conjectures

Formal statements of conjectures: propositions that might or might not be true.

Unlike `sorry`-marked theorems (believed true, proof incomplete), these are
genuinely open questions stated as `def : Prop` — no axioms, no unsoundness.

If a conjecture is proved, promote it to a `theorem` in the appropriate module.
If refuted, replace the body with `False` and add a counterexample comment.
-/

import Linglib.Core.Intension
import Linglib.Core.ModalLogic
import Mathlib.Data.Rat.Defs

namespace Core.Conjectures

open Core.ModalLogic (AgentAccessRel)
open Core.Intension (Intension IsRigid)

/-! ## BToM ↔ Intensional Logic Correspondence

Bayesian Theory of Mind (Frank & Goodman) and Hintikka-style intensional
semantics use different primitives — probabilistic credences vs categorical
accessibility — but should be two views of the same structure.

- Montague/Hintikka: R(x, w, w') means w' is compatible with x's beliefs in w
- Goodman/Frank: P_x(w' | w) is x's credence in w' given w
-/

/-- Accessibility = non-zero belief: w' is accessible from w for agent x
iff x assigns positive credence to w' given w. -/
def accessibility_iff_positive_credence (W E : Type*)
    (R : AgentAccessRel W E) (credence : E → W → W → ℚ) : Prop :=
  ∀ x w w', R x w w' = true ↔ credence x w w' > 0

/-- □_x p (agent x believes p) iff P_x(p) = 1.
Categorical doxastic necessity is the probability-1 limit. -/
def box_iff_credence_one (W E : Type*)
    (R : AgentAccessRel W E) (credence : E → W → W → ℚ) : Prop :=
  ∀ x w (p : BProp W),
    (∀ w', R x w w' = true → p w' = true) ↔
    (∀ w', credence x w w' > 0 → p w' = true)

/-- Rigid designators = common ground with credence 1.
An intension is rigid iff every agent in every world assigns it the
same value across all positively-credenced worlds. -/
def rigid_iff_common_ground (W E τ : Type*)
    (credence : E → W → W → ℚ) : Prop :=
  ∀ (f : Intension W τ), IsRigid f ↔
    ∀ (x : E) (w w' : W), credence x w w' > 0 → f w' = f w

/-! ## RSA ≅ EXH Characterization

When do the Rational Speech Acts pragmatic theory and grammatical
exhaustification make identical predictions?

- Frank & Goodman (2012); Bergen, Levy & Goodman (2016) — RSA
- Fox (2007); Chierchia, Fox & Spector (2012) — EXH
-/

/-- RSA and EXH coincide under specific conditions:
uniform prior, high rationality, depth one, no QUD sensitivity.

This is the "Characterization Theorem" — the conjectured boundary
between notational variants and genuine empirical disagreement. -/
def rsa_exh_equivalence {U W : Type*}
    (rsa_positive : U → W → Prop)       -- RSA L1(u,w) > 0
    (exh_true : U → W → Prop)           -- EXH(u) true at w
    (uniform_prior : Prop) (high_rationality : Prop)
    (depth_one : Prop) (no_qud : Prop) : Prop :=
  (uniform_prior ∧ high_rationality ∧ depth_one ∧ no_qud) →
    ∀ u w, rsa_positive u w ↔ exh_true u w

/-! ## RSA Algebraic Metatheory

Structural properties of the RSA listener/speaker recursion as a
mathematical object (fixed points, limits, monotonicity).
-/

/-- RSA iteration converges to a unique fixed point for any α > 0. -/
def rsa_fixed_point_unique {U W : Type*}
    (iterate : (U → W → ℚ) → (U → W → ℚ))
    (α : ℚ) (_ : α > 0) : Prop :=
  ∃ f : U → W → ℚ, iterate f = f ∧
    ∀ g : U → W → ℚ, iterate g = g → g = f

/-- Refining lexical meanings (shrinking denotations) can only strengthen
RSA pragmatic inferences, never weaken them. -/
def lexicon_refinement_monotone {U W : Type*}
    (meaning₁ meaning₂ : U → BProp W)
    (L1 : (U → BProp W) → U → W → ℚ) : Prop :=
  (∀ u w, meaning₂ u w = true → meaning₁ u w = true) →
    ∀ u w, L1 meaning₂ u w ≤ L1 meaning₁ u w

/-- In the α → ∞ limit, soft-max RSA speaker converges to
iterated best response (argmax / tropical semiring). -/
def rsa_tropical_limit {U W : Type*}
    (S1 : ℚ → U → W → ℚ)
    (bestResponse : U → W → ℚ) : Prop :=
  ∀ u w (ε : ℚ), ε > 0 →
    ∃ α₀ : ℚ, ∀ α, α > α₀ → (S1 α u w - bestResponse u w) ^ 2 < ε

/-! ## Neural-Symbolic Emergence

Can RSA-like pragmatic reasoning emerge from raw language model
next-token distributions via appropriate coarse-graining?
-/

/-- Coarsening a language model's token-level predictions into
world-level meanings recovers RSA pragmatic distributions (approximately). -/
def rsa_from_coarsened_lm {U W : Type*}
    (coarsened : U → W → ℚ)   -- LM coarsened to world-level
    (L1 : U → W → ℚ) : Prop :=
  ∀ u w (ε : ℚ), ε > 0 →
    (coarsened u w - L1 u w) ^ 2 < ε

/-! ## Almog Independence Conjecture

The three mechanisms of direct reference (designation, singular proposition,
referential use) are empirically independent: natural language supplies
expressions exercising every non-empty subset.

See `IntensionalSemantics.Reference.Almog2014.IndependenceWitness` for
the formal content. -/

/-- Almog's independence thesis: for any two of the three mechanisms,
there exists an expression exhibiting one but not the other.
Stated abstractly — the formal witness is in Almog2014.lean. -/
def almog_independence_conjecture (Mechanism : Type*) (exprs : List (List Mechanism)) : Prop :=
  ∀ m₁ m₂ : Mechanism, m₁ ≠ m₂ →
    (∃ e ∈ exprs, m₁ ∈ e ∧ m₂ ∉ e) ∧
    (∃ e ∈ exprs, m₂ ∈ e ∧ m₁ ∉ e)

/-! ## Phase-Bounded Exhaustification

Phases as local computation domains for pragmatic inference.
Charlow (2014, 2020): scope islands = evaluation boundaries.
Chierchia/Fox/Spector (2012): Exh applies at scope positions.
Hypothesis: phase boundaries delimit where Exh/RSA applies.
-/

/-- Exh applies at phase boundaries: alternatives are evaluated
    within the phase domain, not globally.

    If computation is phase-bounded, then local exhaustification
    (within a phase) and global exhaustification (across the whole
    structure) should agree within a phase domain. -/
def exh_at_phase_boundaries {U W : Type*}
    (exh_local : U → W → Prop)
    (exh_global : U → W → Prop)
    (phase_bounded : Prop) : Prop :=
  phase_bounded → ∀ u w, exh_local u w ↔ exh_global u w

/-- Phase-bounded RSA: pragmatic computation is local to phases.
    S1 optimizes within the current phase, not globally.

    If two utterances are in the same phase, S1's local computation
    (within the phase) matches S1's global computation. -/
def rsa_phase_locality {U W : Type*}
    (S1_local : U → W → ℚ)
    (S1_global : U → W → ℚ)
    (same_phase : U → U → Prop) : Prop :=
  ∀ u₁ u₂ w, same_phase u₁ u₂ → S1_local u₁ w = S1_global u₁ w

/-- Phase-bounded alternative computation: alternatives for an expression
    are computed from material within the same phase, not globally.

    This connects to Chierchia (2006) / Fox & Katzir (2011):
    the set of alternatives depends on what's locally available. -/
def phase_bounded_alternatives {U : Type*}
    (local_alts : U → List U)
    (global_alts : U → List U)
    (in_same_phase : U → U → Prop) : Prop :=
  ∀ u, (∀ a ∈ local_alts u, in_same_phase u a) ∧
       (∀ a ∈ global_alts u, ¬in_same_phase u a → a ∉ local_alts u)

end Core.Conjectures
