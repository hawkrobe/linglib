/-
# Pipeline: Composing Theories with Grounded Dependencies

This module defines the architecture for composing theories into complete
analyses where all dependencies bottom out.

## Motivation

A theory component may stipulate requirements (e.g., RSA needs a meaning
function). If nothing provides that requirement, the analysis is incomplete.
This architecture makes dependencies explicit and ensures they're satisfied.

## Key Insight

We DON'T assume a fixed syntax → semantics → pragmatics pipeline.
Some theories cross these boundaries:
- CCG couples syntax and semantics
- DRT couples semantics and discourse
- Construction grammar doesn't cleanly separate levels

Instead, we just require: **every requirement must be provided by something**.

## Architecture

```
┌─────────────────┐     ┌─────────────────┐
│   Component A   │────▶│   Component B   │
│  provides: {X}  │     │  requires: {X}  │
│  requires: {Y}  │     │  provides: {Z}  │
└────────┬────────┘     └─────────────────┘
         │
         ▼
┌─────────────────┐
│   Component C   │
│  provides: {Y}  │  ← bottoms out (no requirements)
│  requires: {}   │
└─────────────────┘
```

A **complete analysis** is a set of components where all requirements
are satisfied by some provider. The dependency graph must bottom out.

## Status

This is a placeholder/roadmap. Full implementation would require:
1. Defining capability types for what theories provide/require
2. Building the dependency resolution mechanism
3. Proving completeness for theory combinations

## References

- Goodman & Frank (2016) - RSA as pragmatics layer
- Montague (1973) - Compositional semantics
- Steedman (2000) - CCG syntax-semantics interface
-/

import Linglib.Core.Basic

namespace Pipeline

-- ============================================================================
-- General Dependency Architecture
-- ============================================================================

/--
A **capability** is something a theory can provide or require.

Examples:
- `meaning : Interp → World → Bool` (truth conditions)
- `derivations : List Derivation` (parse trees)
- `probDist : World → ℚ` (probability distribution)

This is intentionally abstract - concrete capabilities are defined
by specific theory interfaces below.
-/
structure Capability where
  name : String
  /-- The type this capability provides -/
  ty : Type
  deriving Repr

/--
A **theory component** declares what it provides and requires.

A component is grounded if all its requirements are satisfied
by other components (or it has no requirements).
-/
structure TheoryComponent where
  name : String
  provides : List Capability
  requires : List Capability

/--
A requirement is **satisfied** if some component provides it.
-/
def requirementSatisfied (req : Capability) (components : List TheoryComponent) : Prop :=
  ∃ c ∈ components, req ∈ c.provides

/--
A set of components is **complete** if all requirements are satisfied.
This means the dependency graph bottoms out.
-/
def componentsComplete (components : List TheoryComponent) : Prop :=
  ∀ c ∈ components, ∀ req ∈ c.requires, requirementSatisfied req components

/--
A **grounded theory** is a set of components that is complete.
-/
structure GroundedTheory where
  components : List TheoryComponent
  complete : componentsComplete components

-- ============================================================================
-- Level-Based Interfaces (One Possible Factoring)
-- ============================================================================

/-
The following interfaces represent ONE way to factor theories.
Not all theories fit this mold - CCG couples syntax/semantics,
DRT couples semantics/discourse, etc.

These are provided for convenience but are not the only way
to structure a complete analysis.
-/

-- ============================================================================
-- Level 1: Syntax Interface
-- ============================================================================

/--
What a syntax theory must provide to semantics.

A syntax theory produces derivations that can be interpreted semantically.
Different syntax theories (CCG, HPSG, Minimalism) may have different
derivation types, but they must all support semantic interpretation.
-/
class SyntaxTheory (T : Type) where
  /-- The type of syntactic derivations -/
  Derivation : Type
  /-- Surface string of a derivation -/
  surface : Derivation → List String
  /-- Well-formedness predicate -/
  wellFormed : Derivation → Prop

-- ============================================================================
-- Level 2: Semantics Interface
-- ============================================================================

/--
What a semantics theory must provide to pragmatics.

A semantics theory takes syntactic derivations and produces meanings.
The meaning function may be parameterized by interpretation choices
(e.g., scope, coercion, ellipsis resolution).
-/
class SemanticsTheory (T : Type) where
  /-- Type of possible worlds / models -/
  World : Type
  /-- Type of interpretation parameters (scope choices, etc.) -/
  Interp : Type
  /-- Enumeration of worlds -/
  worlds : List World
  /-- Enumeration of interpretations -/
  interps : List Interp
  /-- Truth conditions: given interpretation and world, is utterance true? -/
  meaning : Interp → World → Bool

-- ============================================================================
-- Level 3: Pragmatics Interface
-- ============================================================================

/--
What a pragmatics theory produces.

A pragmatics theory takes meanings and produces enriched interpretations:
probability distributions, implicatures, etc.
-/
class PragmaticsTheory (T : Type) where
  /-- Type of pragmatic outputs (distributions, implicatures, etc.) -/
  Output : Type
  /-- What the theory requires from semantics -/
  RequiredWorld : Type
  RequiredInterp : Type
  /-- The meaning function this theory needs -/
  requiredMeaning : RequiredInterp → RequiredWorld → Bool
  /-- Compute pragmatic output given the meaning function -/
  compute : Output

-- ============================================================================
-- Grounded Pragmatics
-- ============================================================================

/--
A pragmatics theory is **grounded** if there exists a semantics theory
that provides exactly the meaning function the pragmatics requires.

This prevents "floating" pragmatic predictions that aren't derivable
from any compositional semantics.
-/
structure GroundedPragmatics where
  /-- The pragmatics theory -/
  pragmatics : Type
  [pragInst : PragmaticsTheory pragmatics]
  /-- The semantics theory that grounds it -/
  semantics : Type
  [semInst : SemanticsTheory semantics]
  /-- Proof that the types match -/
  worldMatch : PragmaticsTheory.RequiredWorld pragmatics = SemanticsTheory.World semantics
  interpMatch : PragmaticsTheory.RequiredInterp pragmatics = SemanticsTheory.Interp semantics
  /-- Proof that the meaning functions agree -/
  meaningMatch : HEq
    (PragmaticsTheory.requiredMeaning (T := pragmatics))
    (SemanticsTheory.meaning (T := semantics))

-- ============================================================================
-- Complete Analysis Pipeline
-- ============================================================================

/--
A phenomenon specifies empirical data that theories should predict.
-/
class Phenomenon (P : Type) where
  /-- Description of the phenomenon -/
  description : String
  /-- The empirical observations (percentages, judgments, etc.) -/
  EmpiricalData : Type
  /-- The predictions a theory should make -/
  Prediction : Type
  /-- Does a prediction match the data? -/
  predictionMatches : Prediction → EmpiricalData → Prop

/--
A **complete analysis** of a phenomenon is:
1. A grounded pragmatics (semantics + pragmatics that are compatible)
2. A proof that the predictions match the empirical data

This is the gold standard: an end-to-end account from compositional
semantics through pragmatics to empirical predictions.
-/
structure CompleteAnalysis (P : Type) [inst : Phenomenon P] where
  /-- The grounded theory stack -/
  stack : GroundedPragmatics
  /-- The predictions this stack makes -/
  predictions : inst.Prediction
  /-- The empirical data -/
  data : inst.EmpiricalData
  /-- Proof that predictions match data -/
  correct : inst.predictionMatches predictions data

-- ============================================================================
-- Pipeline Composition (Placeholder)
-- ============================================================================

/--
Given a list of syntax theories, semantics theories, and pragmatics theories,
enumerate all compatible pipelines.

TODO: Implement when we have enough theories formalized.
-/
def enumeratePipelines
    (syntaxTheories : List Type)
    (semanticsTheories : List Type)
    (pragmaticsTheories : List Type) : List GroundedPragmatics :=
  sorry  -- Would check compatibility and return valid combinations

/--
Test which pipelines correctly predict a phenomenon.

TODO: Implement when we have the pipeline enumeration.
-/
def workingPipelines (P : Type) [Phenomenon P] : List GroundedPragmatics :=
  sorry  -- Would filter enumeratePipelines by those that predict correctly

-- ============================================================================
-- Example: Scontras & Pearl 2021 (Sketch)
-- ============================================================================

/-
For Scontras & Pearl 2021, a complete analysis would be:

```
structure ScontrasPearl2021Analysis where
  -- Semantics: Montague with scope ambiguity
  semantics := Montague.Scope.everyHorseDidntJump_parametric

  -- Pragmatics: RSA with lifted interpretation variable
  pragmatics := RSA.ScontrasPearl2021

  -- Grounding proof: RSA meaning comes from Montague
  grounded := rsa_meaning_from_montague

  -- Prediction proof: RSA ordering matches empirical ordering
  correct := rsa_and_empirical_agree
```

See: Theories/RSA/ScontrasPearl2021.lean for the actual implementation.
-/

-- ============================================================================
-- Future Work
-- ============================================================================

/-
## TODO

1. **Formalize syntax interfaces**: What CCG/HPSG/Minimalism provide
2. **Syntax-semantics interface**: How derivations become meanings
3. **Enumerate theory combinations**: Which syntax+semantics+pragmatics stacks exist
4. **Automated testing**: Check all pipelines against all phenomena
5. **Coverage matrix**: Which phenomena have complete analyses

## Design Questions

- Should interfaces be typeclasses or structures?
- How to handle partial analyses (syntax only, or semantics only)?
- How to represent "this theory doesn't handle this phenomenon"?
- Should we distinguish "not yet implemented" from "in principle impossible"?
-/

end Pipeline
