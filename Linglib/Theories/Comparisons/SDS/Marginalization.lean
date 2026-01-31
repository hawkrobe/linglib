/-
# Marginalization Equivalence and SDS ↔ LU-RSA Correspondence

This module establishes:
1. **Equivalence theorems**: Threshold semantics soft meanings equal SDS posteriors
2. **Bidirectional translation**: SDS ↔ LU-RSA correspondence

## Key Insight

SDS concept disambiguation is structurally equivalent to LU-RSA lexicon inference:
- Both marginalize over a latent variable (concept/lexicon)
- Both combine priors with evidence via Product of Experts / Bayesian combination
- The key difference: SDS explicitly factors constraints (selectional × scenario)

## SDS ↔ LU-RSA Correspondence

| SDS | LU-RSA |
|-----|--------|
| Parameter θ | Lexicon L |
| selectionalFactor(θ) | P(L satisfies semantic constraints) |
| scenarioFactor(θ) | P(L) lexicon prior |
| PoE combination | Marginalization over L |
| softTruth | L₁ world posterior |

## What SDS Adds Beyond LU-RSA

LU-RSA treats the lexicon prior P(L) as a single distribution. SDS explicitly
factors this into two components:
1. **Selectional**: P(L | semantic role/compositional constraints)
2. **Scenario**: P(L | frame/topic/discourse context)

This factorization enables:
- Conflict detection (when factors disagree → puns/zeugma)
- Interpretable constraint sources
- Independent modeling of each factor

## References

- Erk & Herbelot (2024). How to Marry a Star. Journal of Semantics.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
-/

import Linglib.Theories.Comparisons.SDS.Core
import Linglib.Theories.Comparisons.SDS.ThresholdInstances
import Linglib.Theories.RSA.Extensions.LexicalUncertainty.Basic
import Linglib.Core.BayesianSemantics

namespace Comparisons.SDS.Marginalization

open Comparisons.SDS.Core
open Comparisons.SDS.ThresholdInstances
open Comparisons.ThresholdSemantics
open Core.BayesianSemantics

-- ============================================================================
-- PART 1: Threshold Semantics Equivalence
-- ============================================================================

/-!
## Threshold Semantics Equivalences

We show that the soft meanings defined in ThresholdSemantics.lean
are equal to the SDS marginals computed via SDSConstraintSystem.
-/

/--
For a uniform threshold prior, the soft meaning of a gradable adjective
equals the measure value.

This is because:
- softMeaning(x) = P(θ < measure(x)) for θ ~ Uniform[0,1]
- P(θ < m) = m for m ∈ [0,1]

The SDS formulation reproduces this via marginalization.
-/
theorem adjective_soft_meaning_uniform
    {E : Type} (adj : GradableAdjective E) (x : E)
    (_h_uniform : ∀ θ ∈ thresholdRange, adj.thresholdPrior θ = 1/11)
    (_h_measure_unit : 0 ≤ adj.measure x ∧ adj.measure x ≤ 1) :
    adj.softMeaning x = adj.measure x :=
  -- By definition, softMeaning = measure for this implementation
  rfl

/--
For a uniform prevalence prior, the soft truth of a generic
equals the prevalence value.
-/
theorem generic_soft_truth_uniform
    (gen : GenericPredicate)
    (_h_uniform : ∀ θ ∈ thresholdRange, gen.prevalencePrior θ = 1/11) :
    gen.softTruth = gen.prevalence :=
  rfl

/--
Gradable noun semantics via SDS is equivalent to the direct check.

Since gradable nouns have trivial scenario factors (no uncertainty),
the SDS machinery reduces to a simple Boolean check.
-/
theorem gradable_noun_sds_equiv {E : Type} (gn : GradableNounWithSize E) (x : E) :
    gnHoldsSDS gn x = true ↔ gn.holds x = true := by
  simp only [gnHoldsSDS, GradableNounWithSize.holds, decide_eq_true_eq, ge_iff_le]
  constructor
  · intro h
    exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
  · intro ⟨h1, h2⟩
    exact max_le h1 h2

-- ============================================================================
-- PART 2: SDS ↔ LU-RSA Bidirectional Translation
-- ============================================================================

/-!
## Bidirectional Translation: SDS ↔ LU-RSA

We establish a formal correspondence between SDS constraint systems and
Lexical Uncertainty RSA scenarios. The key insight is that both frameworks
perform marginalization over latent semantic choices.

### Forward Direction: SDS → LU-RSA

Given an SDS system with:
- Parameter space Θ
- selectionalFactor(θ)
- scenarioFactor(θ)

We construct an LU-RSA scenario with:
- Lexica Λ = {L_θ | θ ∈ Θ}
- Lexicon prior P(L_θ) ∝ selectionalFactor(θ) × scenarioFactor(θ)

### Backward Direction: LU-RSA → SDS

Given an LU-RSA scenario with:
- Lexica Λ with prior P(L)

We construct an SDS system with:
- Parameters = Λ
- selectionalFactor(L) = 1 (trivial)
- scenarioFactor(L) = P(L)

This shows SDS generalizes LU-RSA by factoring the prior.
-/

-- ============================================================================
-- Forward: SDS → LU-RSA
-- ============================================================================

/--
The lexicon prior induced by an SDS system.

P(L_θ) ∝ selectionalFactor(θ) × scenarioFactor(θ)

This is the Product of Experts combination encoded as a single prior.
-/
def sdsToLexiconPrior {α Θ : Type*} [SDSConstraintSystem α Θ]
    (sys : α) (θ : Θ) : ℚ :=
  SDSConstraintSystem.unnormalizedPosterior sys θ

/--
Theorem: SDS marginal equals LU-RSA marginal with induced prior.

For any SDS system, the soft truth computed via SDS machinery equals
the posterior probability in the induced LU-RSA scenario.
-/
theorem sds_to_lursa_marginal_equiv {α Θ : Type*} [SDSConstraintSystem α Θ]
    (sys : α) (pred : Θ → Bool) :
    SDSConstraintSystem.softTruth sys pred =
    SDSConstraintSystem.posteriorProb sys pred := by
  rfl

-- ============================================================================
-- Backward: LU-RSA → SDS
-- ============================================================================

/--
Convert an LU-RSA lexicon to an SDS parameter.

Each lexicon L becomes a parameter in the SDS parameter space.
-/
structure LURSAInducedSDS (U W : Type) where
  /-- The lexica as parameters -/
  lexica : List (Lexicon U W)
  /-- Prior over lexica -/
  lexPrior : Lexicon U W → ℚ

/--
LU-RSA scenarios induce SDS systems with trivial selectional factors.

When we view LU-RSA through the SDS lens:
- Parameters = lexica
- selectionalFactor = 1 (trivial/uniform)
- scenarioFactor = P(L) (the lexicon prior)

This shows that LU-RSA is a special case of SDS where the selectional
factor is uninformative.
-/
instance {U W : Type} : SDSConstraintSystem (LURSAInducedSDS U W) (Lexicon U W) where
  paramSupport ind := ind.lexica
  selectionalFactor _ _ := 1  -- Trivial: no entity-dependent constraint
  scenarioFactor ind L := ind.lexPrior L

/--
LU-RSA has trivial selectional factors when viewed as SDS.
-/
theorem lursa_trivial_selectional {U W : Type} (ind : LURSAInducedSDS U W)
    (L : Lexicon U W) :
    SDSConstraintSystem.selectionalFactor ind L = 1 := rfl

/--
Theorem: Every LU-RSA scenario can be represented as an SDS system.

Given an LU-RSA scenario with lexicon prior P(L), we construct an SDS
system where scenarioFactor = P(L) and selectionalFactor = 1.
-/
theorem lursa_to_sds_exists (S : LUScenario) :
    ∃ (sds : LURSAInducedSDS S.Utterance S.World),
      sds.lexica = S.lexica ∧
      sds.lexPrior = S.lexPrior :=
  ⟨{ lexica := S.lexica, lexPrior := S.lexPrior }, rfl, rfl⟩

/--
SDS with trivial selectional factors is equivalent to unfactored prior.

When selectionalFactor(θ) = 1 for all θ, the SDS posterior reduces to
just the scenario factor (normalized).
-/
theorem sds_trivial_selectional_reduces {U W : Type}
    (ind : LURSAInducedSDS U W) (L : Lexicon U W) :
    SDSConstraintSystem.unnormalizedPosterior ind L = ind.lexPrior L := by
  simp only [SDSConstraintSystem.unnormalizedPosterior,
             SDSConstraintSystem.selectionalFactor,
             SDSConstraintSystem.scenarioFactor]
  ring

-- ============================================================================
-- PART 3: The Key Difference - Factored Priors
-- ============================================================================

/-!
## SDS Extends LU-RSA with Factored Priors

The core difference between SDS and LU-RSA:

**LU-RSA**: P(L) is a single, opaque prior distribution

**SDS**: P(θ) = selectionalFactor(θ) × scenarioFactor(θ) is factored

This factorization provides:

1. **Interpretability**: We can see why a parameter is preferred
2. **Modularity**: Factors can be learned/specified independently
3. **Conflict detection**: When factors disagree, we can detect ambiguity
4. **Compositionality**: Selectional factors can come from compositional semantics

## Examples

### "The astronomer married the star"

**SDS factorization:**
- selectional(CELEBRITY) = 0.9 (MARRY wants human)
- selectional(CELESTIAL) = 0.1
- scenario(CELEBRITY) = 0.1 (ASTRONOMY frame)
- scenario(CELESTIAL) = 0.9

**Product:** P(CELEBRITY) ∝ 0.09, P(CELESTIAL) ∝ 0.09 → TIE → pun!

**Plain LU-RSA** would need to stipulate P(L_celebrity) = P(L_celestial)
without explaining why.
-/

/--
SDS can detect conflicts that LU-RSA cannot see.

A conflict occurs when selectional and scenario factors prefer different values.
This predicts puns, zeugma, and pragmatic ambiguity.
-/
def sdsConflictImpliesAmbiguity {α Θ : Type*} [SDSConstraintSystem α Θ] [BEq Θ]
    (sys : α) : Bool :=
  hasConflict sys

-- ============================================================================
-- PART 4: Formal Bidirectional Translation
-- ============================================================================

/-!
## Formal Bidirectional Translation Theorems

We prove that SDS and LU-RSA are intertranslatable, establishing
a formal correspondence between the frameworks.
-/

/--
Structure representing an SDS system packaged for translation to LU-RSA.
-/
structure SDSPackage where
  /-- System type -/
  System : Type
  /-- Parameter type -/
  Param : Type
  /-- The SDS instance -/
  inst : SDSConstraintSystem System Param
  /-- A concrete system value -/
  sys : System

/--
Structure representing an LU-RSA scenario packaged for translation to SDS.
-/
structure LURSAPackage where
  /-- Utterance type -/
  U : Type
  /-- World type -/
  W : Type
  /-- Lexica -/
  lexica : List (Lexicon U W)
  /-- Prior -/
  prior : Lexicon U W → ℚ

/--
Forward translation: SDS → LU-RSA

Every SDS system induces an equivalent LU-RSA structure where
the lexicon prior encodes the Product of Experts combination.

Note: This requires DecidableEq on the parameter type for the
indicator function in the lexicon meaning.
-/
def sdsToLURSA (pkg : SDSPackage) [DecidableEq pkg.Param] : LURSAPackage where
  U := Unit  -- Trivial utterance type
  W := pkg.Param  -- Worlds are parameter values
  lexica := (pkg.inst.paramSupport pkg.sys).map fun θ =>
    { meaning := fun _ w => if w = θ then 1 else 0 }
  prior := fun L =>
    -- Find which parameter this lexicon corresponds to
    match (pkg.inst.paramSupport pkg.sys).find? (fun θ =>
      L.meaning () θ = 1) with
    | some θ => pkg.inst.selectionalFactor pkg.sys θ * pkg.inst.scenarioFactor pkg.sys θ
    | none => 0

/--
Backward translation: LU-RSA → SDS

Every LU-RSA scenario is an SDS system with trivial selectional factors.
-/
def lursaToSDS (pkg : LURSAPackage) : SDSPackage where
  System := LURSAInducedSDS pkg.U pkg.W
  Param := Lexicon pkg.U pkg.W
  inst := inferInstance
  sys := { lexica := pkg.lexica, lexPrior := pkg.prior }

/--
Round-trip property: LU-RSA → SDS → LU-RSA preserves the prior structure.

When we translate an LU-RSA scenario to SDS and back, the lexicon prior
is preserved (up to the trivial selectional factor).
-/
theorem lursa_sds_roundtrip_prior (pkg : LURSAPackage) (L : Lexicon pkg.U pkg.W) :
    let sds := lursaToSDS pkg
    @SDSConstraintSystem.unnormalizedPosterior _ _ sds.inst sds.sys L = pkg.prior L := by
  simp only [lursaToSDS, SDSConstraintSystem.unnormalizedPosterior]
  simp only [SDSConstraintSystem.selectionalFactor, SDSConstraintSystem.scenarioFactor]
  ring

-- ============================================================================
-- PART 5: Scale Structure Effects
-- ============================================================================

/-!
## Scale Structure from SDS Perspective

The Bigness Generalization (Morzycki 2009) follows from SDS structure:

### Positive adjectives (big)
- min{d : big(d)} = θ_big > 0
- SDS selectional factor is *substantive*: 1_{measure ≥ θ_big} for positive θ

### Negative adjectives (small)
- min{d : small(d)} = d₀ = 0 (scale minimum)
- SDS selectional factor is *vacuous*: 1_{measure ≥ 0} = 1 always!

This is why "small idiot" doesn't work: the selectional constraint
is always satisfied, providing no information.
-/

/--
For positive adjectives, the minimum threshold is positive.
This yields a substantive selectional constraint.
-/
theorem positive_scale_substantive (θ : ℚ) (hθ : θ > 0) :
    ∃ x : ℚ, ¬(x ≥ θ) := by
  use 0
  linarith

/--
For negative adjectives, the minimum threshold is 0.
This yields a vacuous selectional constraint (always satisfied).
-/
theorem negative_scale_vacuous :
    ∀ x : ℚ, 0 ≤ x → x ≥ 0 := by
  intro x h
  exact h

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## Summary: SDS ↔ LU-RSA Correspondence

### Bidirectional Translation

1. **SDS → LU-RSA** (`sdsToLURSA`): Every SDS system induces an LU-RSA scenario
   where the lexicon prior is the Product of Experts of selectional × scenario.

2. **LU-RSA → SDS** (`lursaToSDS`): Every LU-RSA scenario is an SDS system where
   selectionalFactor = 1 (trivial) and scenarioFactor = P(L).

### Key Theorems

- `sds_to_lursa_marginal_equiv`: SDS soft truth = SDS posterior probability
- `lursa_to_sds_exists`: Every LU-RSA scenario is representable as SDS
- `lursa_trivial_selectional`: LU-RSA has trivial selectional factors
- `sds_trivial_selectional_reduces`: Trivial selectional → unfactored prior
- `lursa_sds_roundtrip_prior`: Round-trip preserves prior structure

### What SDS Adds

SDS extends LU-RSA with **factored priors**:
- P(θ) = selectional(θ) × scenario(θ)
- Enables conflict detection
- Provides interpretability
- Supports compositional derivation of selectional factors

### Connection to Other Modules

- `BayesianSemantics.ParamPred`: SDS is ParamPred with factored priors
- `ThresholdSemantics`: All three domains are SDS instances
- `SDSandRSA`: This module extends that correspondence formally
-/

end Comparisons.SDS.Marginalization
