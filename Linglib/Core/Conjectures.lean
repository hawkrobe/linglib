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

open Core.Proposition (BProp)
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

end Core.Conjectures
