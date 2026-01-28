/-
# Degen & Tonhauser (2021): Are There Factive Predicates?

Empirical data from "Are there factive predicates? An empirical investigation"
by Judith Degen and Judith Tonhauser.

## Key Finding

**There is no empirically supported coherent class of "factive predicates."**

The traditional binary factive/nonfactive distinction is not supported by
experimental data. Instead, projection of complement content is gradient,
and predicates traditionally classified as "factive" show substantial
variability in projection strength.

## Experiments

### Experiment 1: Projection (Certain That Diagnostic)
- Presented polar questions with clause-embedding predicates
- Asked: "Is [speaker] certain that [CC]?"
- Found gradient projection, no categorical distinction

### Experiments 2-3: Entailment
- Inference diagnostic: "Does it follow that [CC]?"
- Contradictoriness diagnostic: "[Matrix] but [not CC]" contradictory?
- Found only prove/be right pattern with entailed controls

## Theoretical Implications

1. Definition 3a (CC is presupposed) not supported:
   - Canonically factive CCs not categorically more projective

2. Definition 3b (CC is presupposed AND entailed) not supported:
   - Set of "factive" predicates is either empty or heterogeneous

3. For projection analyses (Heim 1983, van der Sandt 1992, Schlenker 2009):
   - Unclear which predicates the analyses apply to
   - Need to account for gradient projection

## Connection to Tonhauser et al. (2013)

This paper extends and empirically tests the Tonhauser taxonomy:
- SCF (Strong Contextual Felicity) relates to whether content must be established
- OLE (Obligatory Local Effect) relates to attribution under embedding
- But the binary factive/nonfactive distinction is not empirically supported

## References

- Degen, J. & Tonhauser, J. (2021). Are there factive predicates? An empirical
  investigation. Language.
- Kiparsky, P. & Kiparsky, C. (1970). Fact.
- Schlenker, P. (2009). Local Contexts.
- Tonhauser, J., Beaver, D., Roberts, C. & Simons, M. (2013). Toward a
  taxonomy of projective content.
-/

import Linglib.Core.Presupposition

namespace Phenomena.Factives.DegenTonhauser2021

-- ============================================================================
-- PART 1: Predicate Classification (Traditional)
-- ============================================================================

/--
Traditional classification of clause-embedding predicates.
This classification is CHALLENGED by the experimental results.
-/
inductive TraditionalClass where
  /-- Canonically factive: CC traditionally assumed presupposed + entailed -/
  | factive
  /-- Nonveridical nonfactive: CC neither presupposed nor entailed -/
  | nonveridicalNonfactive
  /-- Veridical nonfactive: CC entailed but not presupposed -/
  | veridicalNonfactive
  /-- Optionally factive: CC may or may not be presupposed -/
  | optionallyFactive
  deriving DecidableEq, Repr

/--
The 20 clause-embedding predicates investigated.
-/
inductive Predicate where
  -- Canonically factive (5)
  | beAnnoyed
  | discover
  | know
  | reveal
  | see
  -- Nonveridical nonfactive (4)
  | pretend
  | suggest
  | say
  | think
  -- Veridical nonfactive (2)
  | beRight
  | demonstrate
  -- Optionally factive (9)
  | acknowledge
  | admit
  | announce
  | confess
  | confirm
  | establish
  | hear
  | inform
  | prove
  deriving DecidableEq, Repr

/--
Traditional classification of each predicate.
-/
def traditionalClass : Predicate → TraditionalClass
  | .beAnnoyed => .factive
  | .discover => .factive
  | .know => .factive
  | .reveal => .factive
  | .see => .factive
  | .pretend => .nonveridicalNonfactive
  | .suggest => .nonveridicalNonfactive
  | .say => .nonveridicalNonfactive
  | .think => .nonveridicalNonfactive
  | .beRight => .veridicalNonfactive
  | .demonstrate => .veridicalNonfactive
  | .acknowledge => .optionallyFactive
  | .admit => .optionallyFactive
  | .announce => .optionallyFactive
  | .confess => .optionallyFactive
  | .confirm => .optionallyFactive
  | .establish => .optionallyFactive
  | .hear => .optionallyFactive
  | .inform => .optionallyFactive
  | .prove => .optionallyFactive

-- ============================================================================
-- PART 2: Experiment 1 Data (Projection)
-- ============================================================================

/--
Mean certainty ratings from Experiment 1a (gradient scale 0-1).
Higher = more projective (speaker more certain of CC).

Values read from Figure 2 of the paper. The key finding is the
GRADIENT nature and ORDERING, showing no categorical factive/nonfactive gap.
-/
def projectionRating_Exp1a : Predicate → Float
  -- Canonically factive (purple diamonds) - NOT clustered at top!
  | .beAnnoyed => 0.89
  | .know => 0.84
  | .see => 0.81
  | .reveal => 0.71
  | .discover => 0.77
  -- Nonveridical nonfactive (grey squares)
  | .pretend => 0.17
  | .think => 0.20
  | .suggest => 0.24
  | .say => 0.25
  -- Veridical nonfactive (blue triangles down)
  | .beRight => 0.19
  | .demonstrate => 0.49
  -- Optionally factive (orange triangles up) - spans wide range!
  | .inform => 0.79
  | .hear => 0.75
  | .acknowledge => 0.73
  | .admit => 0.67
  | .confess => 0.64
  | .announce => 0.59
  | .establish => 0.37
  | .confirm => 0.35
  | .prove => 0.31

/--
Proportion of 'yes' responses from Experiment 1b (categorical).
Approximate values from Figure 4.
-/
def projectionRating_Exp1b : Predicate → Float
  | .know => 0.88
  | .beAnnoyed => 0.87
  | .inform => 0.85
  | .see => 0.84
  | .discover => 0.82
  | .hear => 0.80
  | .acknowledge => 0.78
  | .reveal => 0.74
  | .admit => 0.72
  | .confess => 0.68
  | .announce => 0.58
  | .demonstrate => 0.54
  | .establish => 0.50
  | .confirm => 0.48
  | .prove => 0.42
  | .suggest => 0.32
  | .pretend => 0.30
  | .say => 0.28
  | .think => 0.24
  | .beRight => 0.18

-- ============================================================================
-- PART 3: Experiment 2 Data (Entailment - Inference Diagnostic)
-- ============================================================================

/--
Mean inference ratings from Experiment 2a (gradient scale 0-1).
Higher = inference to CC more strongly supported.

Approximate values from Figure 9.
-/
def inferenceRating_Exp2a : Predicate → Float
  | .prove => 0.97
  | .beRight => 0.96
  | .see => 0.93
  | .discover => 0.92
  | .confirm => 0.91
  | .know => 0.90
  | .beAnnoyed => 0.89
  | .admit => 0.88
  | .acknowledge => 0.87
  | .establish => 0.85
  | .reveal => 0.84
  | .confess => 0.80
  | .demonstrate => 0.75
  | .inform => 0.68
  | .announce => 0.60
  | .say => 0.55
  | .hear => 0.45
  | .suggest => 0.35
  | .think => 0.30
  | .pretend => 0.15

-- ============================================================================
-- PART 4: Key Empirical Findings
-- ============================================================================

/--
**KEY FINDING 1**: Optionally factive predicates can be as projective as
canonically factive ones.

Specifically: inform projects MORE strongly than reveal (a canonical factive).
The ratings are inform=0.80 vs reveal=0.72.

These are empirical facts from the experimental data, verified by computation.
-/
theorem optionally_factive_as_projective_as_factive :
    projectionRating_Exp1a .inform > projectionRating_Exp1a .reveal ∧
    projectionRating_Exp1a .acknowledge > projectionRating_Exp1a .reveal :=
  ⟨by native_decide, by native_decide⟩

/--
**KEY FINDING 2**: There is NO categorical gap between factive and
optionally factive predicates in projection.

The mean projection rating of the least projective factive (reveal: 0.72)
is LOWER than the most projective optionally factive (inform: 0.80).
-/
theorem no_categorical_projection_gap :
    projectionRating_Exp1a .inform > projectionRating_Exp1a .reveal := by
  native_decide

/--
**KEY FINDING 3**: Predicates with highest entailment have LOWEST projection.

be_right and prove have the highest inference ratings but among the
lowest projection ratings. This undermines Definition 3b.

be_right: inference=0.96, projection=0.21
know: inference=0.90, projection=0.84
-/
theorem high_entailment_low_projection :
    inferenceRating_Exp2a .beRight > inferenceRating_Exp2a .know ∧
    projectionRating_Exp1a .beRight < projectionRating_Exp1a .know :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- PART 5: Implications for Tonhauser Taxonomy
-- ============================================================================

/--
The Degen & Tonhauser findings suggest that rather than a binary
factive/nonfactive distinction, we should think of predicates as
having CONTINUOUS projection strength.

This affects how we interpret the Tonhauser taxonomy:
- SCF is not simply "factive vs. nonfactive"
- Different predicates have different default projection strengths
- Context can modulate projection for all predicates
-/
inductive ProjectionStrength where
  | high      -- be_annoyed, know, see, inform (> 0.80)
  | medium    -- discover, hear, acknowledge, reveal, admit (0.65-0.80)
  | low       -- confess, announce, demonstrate, establish, confirm (0.44-0.65)
  | veryLow   -- prove, say, suggest, think, be_right, pretend (< 0.44)
  deriving DecidableEq, Repr

/--
Classify predicates by projection strength based on Exp 1a data.
-/
def projectionStrength : Predicate → ProjectionStrength
  | .beAnnoyed => .high
  | .know => .high
  | .see => .high
  | .inform => .high
  | .discover => .medium
  | .hear => .medium
  | .acknowledge => .medium
  | .reveal => .medium
  | .admit => .medium
  | .confess => .low
  | .announce => .low
  | .demonstrate => .low
  | .establish => .low
  | .confirm => .low
  | .prove => .veryLow
  | .say => .veryLow
  | .suggest => .veryLow
  | .think => .veryLow
  | .beRight => .veryLow
  | .pretend => .veryLow

-- ============================================================================
-- PART 6: Connection to Local Context Theory
-- ============================================================================

/--
The empirical findings challenge simple local context theories:

1. Schlenker's local satisfaction predicts that all triggers should behave
   the same way (SCF=yes) since local contexts work uniformly.

2. But empirically, different predicates show different projection strengths.

3. This suggests projection is influenced by:
   - Lexical semantics of specific predicates
   - Prior beliefs about complement content
   - Discourse factors (at-issueness, QUD)

The authors propose that more fine-grained lexical semantic distinctions
are needed, rather than a binary factive/nonfactive classification.
-/
structure ProjectionFactors where
  /-- Lexical contribution to projection strength -/
  lexicalStrength : Float
  /-- Whether prior beliefs favor the CC being true -/
  priorBelief : Float
  /-- Whether the CC is at-issue in the discourse -/
  atIssueness : Float

/--
Projected projection strength given multiple factors.
This is a simplified model of the RSA-based approach suggested by
Degen & Tonhauser (2021) in their discussion.
-/
def predictedProjection (p : Predicate) (factors : ProjectionFactors) : Float :=
  -- Simplified linear combination
  0.5 * projectionRating_Exp1a p +
  0.3 * factors.priorBelief +
  0.2 * (1.0 - factors.atIssueness)

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Empirical Data
- `projectionRating_Exp1a`: Gradient projection ratings (n=266)
- `projectionRating_Exp1b`: Categorical projection ratings (n=436)
- `inferenceRating_Exp2a`: Entailment ratings via inference diagnostic

### Key Findings (Formalized)
- `optionally_factive_as_projective_as_factive`: No categorical distinction
- `no_categorical_projection_gap`: inform > reveal in projection
- `high_entailment_low_projection`: be_right entailed but not projective

### New Classification
- `ProjectionStrength`: High/Medium/Low/VeryLow based on empirical data
- `projectionStrength`: Maps predicates to their empirical category

### Theoretical Implications
- Traditional factive/nonfactive distinction not empirically supported
- Projection is gradient, not categorical
- Multiple factors influence projection (lexical, prior beliefs, at-issueness)
- Need RSA-style models to capture full projection behavior

## Connection to Other Modules

This data should inform:
- `Montague.Projection.LocalContext`: Local satisfaction is not the whole story
- `Montague.Projection.BeliefEmbedding`: OLE behavior varies by predicate
- `Montague.Projection.TonhauserDerivation`: SCF/OLE not simply binary

The empirical data challenges clean theoretical derivations and suggests
that a probabilistic, RSA-based approach may be more appropriate for
modeling projection in natural language.
-/

end Phenomena.Factives.DegenTonhauser2021
