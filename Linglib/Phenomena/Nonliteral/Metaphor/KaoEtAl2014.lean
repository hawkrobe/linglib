import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{kao-etal-2014-hyperbole} — Metaphor @cite{kao-etal-2014-metaphor}

"Formalizing the Pragmatics of Metaphor Understanding"
Proceedings of the Annual Meeting of the Cognitive Science Society, 36, 719-724

## The Model

Domain: "He is a whale" metaphor. 2 categories (whale, person) × 2³ feature
combinations (large, graceful, majestic) = 16 world states. 2 utterances
(= categories). 3 QUDs (= features).

- **L0**: L0(w|u) = P(features|category) if category = u, 0 otherwise
- **S1**: QUD-projected rpow: S1(u|g,w) ∝ [Σ_{w': g(w')=g(w)} L0(w'|u)]^α
- **L1**: L1(w|u) ∝ P(cat) · P(features|cat) · Σ_g P(g) · S1(u|g,w)

Parameters: α = 3, P(whale) = 1/100, P(person) = 99/100

## Qualitative Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | P(person \| "whale") > P(whale \| "whale") | `nonliteral` |
| 2 | P(large=T \| "whale") > P(large=F \| "whale") | `feature_large` |
| 3 | P(graceful=T \| "whale") > P(graceful=F \| "whale") | `feature_graceful` |
| 4 | P(majestic=T \| "whale") > P(majestic=F \| "whale") | `feature_majestic` |
| 5 | Specific QUD → higher P(large=T) than vague QUD | `context_sensitivity` |
| 6 | P(person \| "person") > P(whale \| "person") | `literal_correct` |

-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Metaphor.KaoEtAl2014

open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Empirical Findings
-- ============================================================================

/-- The 6 qualitative findings from @cite{kao-etal-2014-hyperbole}.
    Each model of metaphor should formalize and prove all 6 findings. -/
inductive Finding where
  /-- Hearing "whale" about a person, the listener infers the referent
      is a person, not literally a whale. -/
  | nonliteral
  /-- Metaphor elevates the "large" feature above its prior. -/
  | feature_large
  /-- Metaphor elevates the "graceful" feature above its prior. -/
  | feature_graceful
  /-- Metaphor elevates the "majestic" feature above its prior. -/
  | feature_majestic
  /-- A specific QUD ("Is he large?") raises P(large=T) higher than a
      vague QUD ("What is he like?"). -/
  | context_sensitivity
  /-- Hearing "person", the listener correctly infers the referent is a person. -/
  | literal_correct
  deriving DecidableEq, Repr

def findings : List Finding :=
  [.nonliteral, .feature_large, .feature_graceful, .feature_majestic,
   .context_sensitivity, .literal_correct]

-- ============================================================================
-- §2. Domain Types
-- ============================================================================

/-- Categories: whale (metaphor vehicle) and person (literal referent).
    Categories double as utterance types. -/
inductive Cat where
  | whale | person
  deriving DecidableEq, Repr

/-- QUDs: which feature is the speaker trying to communicate? -/
inductive Goal where
  | large | graceful | majestic
  deriving DecidableEq, Repr

/-- World = category × large × graceful × majestic. -/
abbrev World := Cat × Bool × Bool × Bool

instance : Fintype Cat where
  elems := {.whale, .person}
  complete := fun x => by cases x <;> simp

instance : Fintype Goal where
  elems := {.large, .graceful, .majestic}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §3. Empirical Priors
-- ============================================================================

/-- Feature prior P(large, graceful, majestic | category).
    Unnormalized counts (×10000) from Experiment 1b / memo code. -/
def featurePrior (c : Cat) (large graceful majestic : Bool) : ℝ :=
  match c, large, graceful, majestic with
  | .whale,  true,  true,  true  => 3059
  | .whale,  true,  true,  false => 1381
  | .whale,  true,  false, true  => 1791
  | .whale,  true,  false, false => 1310
  | .whale,  false, true,  true  => 947
  | .whale,  false, true,  false => 531
  | .whale,  false, false, true  => 602
  | .whale,  false, false, false => 379
  | .person, true,  true,  true  => 1169
  | .person, true,  true,  false => 1058
  | .person, true,  false, true  => 1157
  | .person, true,  false, false => 1308
  | .person, false, true,  true  => 1529
  | .person, false, true,  false => 1281
  | .person, false, false, true  => 1147
  | .person, false, false, false => 1351

/-- Category prior. Unnormalized: whale = 1, person = 99. -/
def catPrior : Cat → ℝ
  | .whale => 1
  | .person => 99

-- ============================================================================
-- §4. Literal Semantics
-- ============================================================================

/-- L0 meaning: P(features|category) when category matches utterance, 0 otherwise.
    The feature prior is baked into L0 following RSAConfig convention. -/
def meaning (_q : Goal) (u : Cat) (w : World) : ℝ :=
  if u == w.1 then featurePrior w.1 w.2.1 w.2.2.1 w.2.2.2 else 0

-- ============================================================================
-- §5. QUD Projection
-- ============================================================================

/-- Project a world onto the QUD-relevant feature. -/
def project (w : World) (q : Goal) : Bool :=
  match q with
  | .large    => w.2.1
  | .graceful => w.2.2.1
  | .majestic => w.2.2.2

/-- Sum L0 over the QUD equivalence class of w under goal q. -/
noncomputable def qudProject (q : Goal) (f : World → ℝ) (w : World) : ℝ :=
  (Finset.univ.filter (fun w' => project w' q = project w q)).sum f

-- ============================================================================
-- §6. RSAConfig
-- ============================================================================

/-- @cite{kao-etal-2014-hyperbole} metaphor model, parametric in goal prior.

    S1 score is rpow(projected_L0, α) — the paper's Eq. 5 without
    utterance cost. This directly encodes the paper's equations and
    lets `rsa_predict` handle the interval arithmetic. -/
noncomputable def cfg (goalPrior : Goal → ℝ) (hp : ∀ g, 0 ≤ goalPrior g) :
    RSA.RSAConfig Cat World where
  Latent := Goal
  meaning := fun _ => meaning
  meaning_nonneg := by
    intro _ q u ⟨c, a, b, d⟩; simp only [meaning]
    split <;> (try exact le_refl 0)
    cases c <;> cases a <;> cases b <;> cases d <;> simp [featurePrior]
  s1Score l0 α q w u := rpow (qudProject q (l0 u) w) α
  s1Score_nonneg _ _ _ _ u hl _ :=
    rpow_nonneg (Finset.sum_nonneg (fun w' _ => hl u w')) _
  α := 3
  α_pos := by positivity
  worldPrior := fun w => catPrior w.1 * featurePrior w.1 w.2.1 w.2.2.1 w.2.2.2
  worldPrior_nonneg := by
    intro ⟨c, a, b, d⟩; apply mul_nonneg
    · cases c <;> simp [catPrior]
    · cases c <;> cases a <;> cases b <;> cases d <;> simp [featurePrior]
  latentPrior := fun _ g => goalPrior g
  latentPrior_nonneg := fun _ g => hp g

/-- Vague QUD condition: uniform goal prior ("What is he like?"). -/
noncomputable abbrev vagueCfg :=
  cfg (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Specific QUD condition: large-biased goal prior ("Is he large?"). -/
noncomputable abbrev specificCfg :=
  cfg (fun g => match g with | .large => 6 | .graceful => 2 | .majestic => 2)
    (fun g => by cases g <;> positivity)

-- ============================================================================
-- §7. Bridge Theorems
-- ============================================================================

-- Nonliteral interpretation: P(person | "whale") > P(whale | "whale")

/-- The listener infers the referent is a person, not literally a whale. -/
theorem nonliteral :
    vagueCfg.L1_marginal .whale (fun w => w.1 == .person) >
    vagueCfg.L1_marginal .whale (fun w => w.1 == .whale) := by
  rsa_predict

-- Feature elevation: metaphor raises all three features

/-- P(large=T | "whale") > P(large=F | "whale"). -/
theorem feature_large :
    vagueCfg.L1_marginal .whale (fun w => w.2.1 == true) >
    vagueCfg.L1_marginal .whale (fun w => w.2.1 == false) := by
  rsa_predict

/-- P(graceful=T | "whale") > P(graceful=F | "whale"). -/
theorem feature_graceful :
    vagueCfg.L1_marginal .whale (fun w => w.2.2.1 == true) >
    vagueCfg.L1_marginal .whale (fun w => w.2.2.1 == false) := by
  rsa_predict

/-- P(majestic=T | "whale") > P(majestic=F | "whale"). -/
theorem feature_majestic :
    vagueCfg.L1_marginal .whale (fun w => w.2.2.2 == true) >
    vagueCfg.L1_marginal .whale (fun w => w.2.2.2 == false) := by
  rsa_predict

-- Context sensitivity: cross-cfg comparison

/-- Under specific QUD, P(large=T | "whale") is higher than under vague QUD. -/
theorem context_sensitivity :
    specificCfg.L1_marginal .whale (fun w => w.2.1 == true) >
    vagueCfg.L1_marginal .whale (fun w => w.2.1 == true) := by
  rsa_predict

-- Literal: P(person | "person") > P(whale | "person")

/-- Hearing "person", the listener correctly infers the referent is a person. -/
theorem literal_correct :
    vagueCfg.L1_marginal .person (fun w => w.1 == .person) >
    vagueCfg.L1_marginal .person (fun w => w.1 == .whale) := by
  rsa_predict

-- ============================================================================
-- §8. Verification
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
noncomputable def formalize : Finding → Prop
  | .nonliteral =>
      vagueCfg.L1_marginal .whale (fun w => w.1 == .person) >
      vagueCfg.L1_marginal .whale (fun w => w.1 == .whale)
  | .feature_large =>
      vagueCfg.L1_marginal .whale (fun w => w.2.1 == true) >
      vagueCfg.L1_marginal .whale (fun w => w.2.1 == false)
  | .feature_graceful =>
      vagueCfg.L1_marginal .whale (fun w => w.2.2.1 == true) >
      vagueCfg.L1_marginal .whale (fun w => w.2.2.1 == false)
  | .feature_majestic =>
      vagueCfg.L1_marginal .whale (fun w => w.2.2.2 == true) >
      vagueCfg.L1_marginal .whale (fun w => w.2.2.2 == false)
  | .context_sensitivity =>
      specificCfg.L1_marginal .whale (fun w => w.2.1 == true) >
      vagueCfg.L1_marginal .whale (fun w => w.2.1 == true)
  | .literal_correct =>
      vagueCfg.L1_marginal .person (fun w => w.1 == .person) >
      vagueCfg.L1_marginal .person (fun w => w.1 == .whale)

/-- The RSA model accounts for all 6 empirical findings from @cite{kao-etal-2014-hyperbole}. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact nonliteral
  · exact feature_large
  · exact feature_graceful
  · exact feature_majestic
  · exact context_sensitivity
  · exact literal_correct

end Phenomena.Nonliteral.Metaphor.KaoEtAl2014
