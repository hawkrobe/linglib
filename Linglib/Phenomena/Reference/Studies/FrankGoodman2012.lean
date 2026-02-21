import Linglib.Core.Empirical
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Montague.Modification
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frank & Goodman (2012) @cite{frank-goodman-2012}

"Predicting Pragmatic Reasoning in Language Games"
Science 336(6084): 998

## Paradigm

Three objects varying on two dimensions (color × shape) in a reference game.
Speaker produces a single feature word; listener identifies the target object.

Context: {blue_square, blue_circle, green_square}
Utterances: {blue, green, square, circle}

## Architecture

Belief-based RSA with no latent variables. S1 score = L0(w|u)^α, using `rpow`
so that false utterances (L0 = 0) correctly get score 0. When α = 1, this
reduces to S1(u|w) ∝ L0(w|u).

## Qualitative Findings

The paper introduced the RSA framework and demonstrated that pragmatic
inferences in reference games can be predicted by modeling listeners as
reasoning about rational, informative speakers.

| # | Finding | Word | Comparison | Mechanism |
|---|---------|------|------------|-----------|
| 1 | Pragmatic narrowing | "square" | blue_sq > green_sq | S1 prefers "green" for green_sq |
| 2 | Pragmatic narrowing | "blue" | blue_sq > blue_circ | S1 prefers "circle" for blue_circ |
| 3 | Unique reference | "green" | green_sq > blue_sq | "green" applies only to green_sq |
| 4 | Unique reference | "circle" | blue_circ > blue_sq | "circle" applies only to blue_circ |

Model predictions correlate r² = 0.99 with human judgments. All proofs
use `rsa_predict`.

## Formalization Coverage

- **L1 predictions** (§6): All 4 listener comparisons proved via `rsa_predict`
- **S1 predictions** (§6b): Speaker informativity preferences proved via `rsa_predict`
- **Size principle** (§6c): Eq. 2 demonstrated — S1 prefers smaller extensions
- **Montague grounding** (§5b): Feature semantics grounded in intersective
  predicate modification (Heim & Kratzer 1998)
- **Structural properties** (§5): Feature uniqueness/ambiguity proved by `rfl`

## References

- Frank, M.C. & Goodman, N.D. (2012). Predicting Pragmatic Reasoning in
  Language Games. Science 336(6084): 998.
- Degen, J. (2023). The Rational Speech Act Framework. §2.
- Tenenbaum, J.B. & Griffiths, T.L. (2001). Generalization, similarity, and
  Bayesian inference. Behavioral and Brain Sciences 24(4): 629–640.
- Heim, I. & Kratzer, A. (1998). Semantics in Generative Grammar, Ch. 4.
-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.FrankGoodman2012

open Phenomena

-- ============================================================================
-- §1. Empirical Data
-- ============================================================================

def citation : String :=
  "Frank & Goodman (2012). Science 336(6084): 998."

def measure : MeasureSpec :=
  { scale := .proportion, task := .forcedChoice, unit := "probability 0-1" }

/-- The 4 qualitative findings from Frank & Goodman (2012).

    Each finding is an L1 comparison between two objects given a word.
    Findings 1–2 are the core pragmatic results (ambiguous words get
    narrowed). Findings 3–4 are baseline sanity checks (unique identifiers
    trivially select the referent). -/
inductive Finding where
  /-- Hearing "square" → blue_square over green_square.
      The core RSA insight: "green" uniquely identifies green_square,
      so a speaker saying "square" probably means blue_square.
      Evidence: model-human r² = 0.99 (Figure 1). -/
  | square_pragmatic_narrowing
  /-- Hearing "blue" → blue_square over blue_circle.
      Parallel inference: "circle" uniquely identifies blue_circle,
      so "blue" signals blue_square. -/
  | blue_pragmatic_narrowing
  /-- Hearing "green" → green_square (unique identifier, no pragmatics needed). -/
  | green_unique_reference
  /-- Hearing "circle" → blue_circle (unique identifier, no pragmatics needed). -/
  | circle_unique_reference
  deriving DecidableEq, BEq, Repr

def findings : List Finding :=
  [.square_pragmatic_narrowing, .blue_pragmatic_narrowing,
   .green_unique_reference, .circle_unique_reference]

-- ============================================================================
-- §2. Domain Types
-- ============================================================================

/-- The three objects in the classic reference game context (Figure 1).

    Modeled as an enumeration rather than Color × Shape because the context
    has only 3 of 4 possible combinations — no green_circle. -/
inductive Object where
  | blue_square | blue_circle | green_square
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- The four single-word utterances (feature predicates). -/
inductive Feature where
  | blue | green | square | circle
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §3. Literal Semantics
-- ============================================================================

/-- Characteristic function: ⟦feature⟧(object). -/
def Feature.appliesTo (f : Feature) (o : Object) : Bool :=
  match f, o with
  | .blue, .blue_square => true
  | .blue, .blue_circle => true
  | .green, .green_square => true
  | .square, .blue_square => true
  | .square, .green_square => true
  | .circle, .blue_circle => true
  | _, _ => false

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

open RSA Real in
/-- The Frank & Goodman (2012) reference game as an RSAConfig.

    - Meaning: Boolean feature semantics (1 if applies, 0 otherwise)
    - S1 score: belief-based rpow — score = L0(w|u)^α
    - α = 1 (standard rationality)
    - No latent variables (Unit)
    - Uniform world prior -/
noncomputable def cfg : RSAConfig Feature Object where
  meaning _ u w := if u.appliesTo w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by positivity
  worldPrior_nonneg _ := by positivity

-- ============================================================================
-- §5. Structural Properties
-- ============================================================================

/-- "green" uniquely identifies green_square. -/
theorem green_unique :
    Feature.appliesTo .green .green_square = true ∧
    Feature.appliesTo .green .blue_square = false ∧
    Feature.appliesTo .green .blue_circle = false :=
  ⟨rfl, rfl, rfl⟩

/-- "circle" uniquely identifies blue_circle. -/
theorem circle_unique :
    Feature.appliesTo .circle .blue_circle = true ∧
    Feature.appliesTo .circle .blue_square = false ∧
    Feature.appliesTo .circle .green_square = false :=
  ⟨rfl, rfl, rfl⟩

/-- "blue" is ambiguous between two objects. -/
theorem blue_ambiguous :
    Feature.appliesTo .blue .blue_square = true ∧
    Feature.appliesTo .blue .blue_circle = true ∧
    Feature.appliesTo .blue .green_square = false :=
  ⟨rfl, rfl, rfl⟩

/-- "square" is ambiguous between two objects. -/
theorem square_ambiguous :
    Feature.appliesTo .square .blue_square = true ∧
    Feature.appliesTo .square .green_square = true ∧
    Feature.appliesTo .square .blue_circle = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §5b. Montague Grounding
-- ============================================================================

/-! The feature semantics (`Feature.appliesTo`) is compositionally grounded
in Montague intersective predicate modification (Heim & Kratzer 1998, Ch. 4).

Each feature word denotes an intersective ⟨e,t⟩ predicate. Objects in the
reference game context are uniquely characterized by predicate modification
(conjunction) of their color and shape features:

    ⟦blue square⟧ = ⟦blue⟧ ⊓ₚ ⟦square⟧ = λx. blue(x) ∧ square(x)

This means the RSA meaning function `cfg.meaning` inherits its semantics from
Montague composition rather than being stipulated independently. -/

open Semantics.Montague.Modification in
/-- Each object is uniquely characterized by predicate modification of its
    color and shape features. Reference resolution in the game IS predicate
    modification: the listener identifies the referent by intersecting the
    denotations of the heard feature words. -/
theorem objects_from_predMod :
    (∀ o, predMod (Feature.appliesTo .blue) (Feature.appliesTo .square) o =
          decide (o = .blue_square)) ∧
    (∀ o, predMod (Feature.appliesTo .blue) (Feature.appliesTo .circle) o =
          decide (o = .blue_circle)) ∧
    (∀ o, predMod (Feature.appliesTo .green) (Feature.appliesTo .square) o =
          decide (o = .green_square)) := by
  refine ⟨fun o => ?_, fun o => ?_, fun o => ?_⟩ <;> cases o <;> rfl

-- ============================================================================
-- §5c. Extension Sizes
-- ============================================================================

/-! The paper's key theoretical contribution is the **size principle**
(Tenenbaum & Griffiths 2001, Eq. 2): the speaker probability of an utterance
is inversely proportional to its extension size |⟦u⟧|.

In RSA with α = 1 and belief-based scoring:
    S1_score(w, u) = L0(w|u)¹ = 1/|⟦u⟧|    (for true utterances)
    S1_score(w, u) = 0                        (for false utterances)

Features with smaller extensions are more *informative* and thus preferred
by S1. The S1 predictions in §6b demonstrate this: unique features (size 1)
always beat ambiguous features (size 2). -/

/-- Extension size: number of objects a feature applies to. -/
def extensionSize (f : Feature) : Nat :=
  ((Finset.univ : Finset Object).filter (fun o => f.appliesTo o = true)).card

/-- Unique features have extension size 1; ambiguous features have size 2. -/
theorem extension_sizes :
    extensionSize .green = 1 ∧ extensionSize .circle = 1 ∧
    extensionSize .blue = 2 ∧ extensionSize .square = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §6. Predictions
-- ============================================================================

/-! All RSA levels derive from `cfg`:

- `cfg.L0 () u w` — L0 posterior P(w|u)
- `cfg.S1 () w u` — S1 policy P(u|w)
- `cfg.L1 u w`    — L1 posterior P(w|u)

The pragmatic inferences arise because S1 prefers informative utterances:
a speaker wanting green_square says "green" (unique), so "square" signals
blue_square. Similarly, a speaker wanting blue_circle says "circle", so
"blue" signals blue_square. -/

/-- **Core RSA result**: L1("square") assigns higher probability to blue_square
    than green_square. A speaker wanting green_square would say "green"
    (uniquely identifying). Saying "square" signals blue_square. -/
theorem square_pragmatic_narrowing :
    cfg.L1 .square .blue_square > cfg.L1 .square .green_square := by
  rsa_predict

/-- L1("blue") assigns higher probability to blue_square than blue_circle.
    A speaker wanting blue_circle would say "circle" (uniquely identifying).
    Saying "blue" signals blue_square. -/
theorem blue_pragmatic_narrowing :
    cfg.L1 .blue .blue_square > cfg.L1 .blue .blue_circle := by
  rsa_predict

/-- L1("green") assigns higher probability to green_square (the only object
    "green" applies to). -/
theorem green_unique_reference :
    cfg.L1 .green .green_square > cfg.L1 .green .blue_square := by
  rsa_predict

/-- L1("circle") assigns higher probability to blue_circle (the only object
    "circle" applies to). -/
theorem circle_unique_reference :
    cfg.L1 .circle .blue_circle > cfg.L1 .circle .blue_square := by
  rsa_predict

-- ============================================================================
-- §6b. Speaker Predictions (S1)
-- ============================================================================

/-! The pragmatic listener predictions above (§6) derive from speaker behavior:
S1 prefers *informative* utterances — those that uniquely identify the target.
These S1 comparisons are the mechanism behind pragmatic narrowing. -/

/-- S1 prefers "green" over "square" for green_square.
    "green" uniquely identifies green_square; "square" is ambiguous. -/
theorem S1_green_sq_prefers_green :
    cfg.S1 () .green_square .green > cfg.S1 () .green_square .square := by
  rsa_predict

/-- S1 prefers "circle" over "blue" for blue_circle.
    "circle" uniquely identifies blue_circle; "blue" is ambiguous. -/
theorem S1_blue_circ_prefers_circle :
    cfg.S1 () .blue_circle .circle > cfg.S1 () .blue_circle .blue := by
  rsa_predict

/-- S1 is indifferent between "blue" and "square" for blue_square.
    Both features share with exactly one other object, so
    L0(blue_sq|blue) = 1/2 = L0(blue_sq|square), hence equal S1 scores. -/
theorem S1_blue_sq_indifferent :
    ¬(cfg.S1 () .blue_square .blue > cfg.S1 () .blue_square .square) := by
  rsa_predict

-- ============================================================================
-- §6c. Size Principle (Eq. 2)
-- ============================================================================

/-- The size principle in action: S1 prefers features with smaller extensions.
    Unique features (extensionSize = 1) dominate ambiguous ones (extensionSize = 2).
    This is Eq. 2 of the paper: P_S(u|w) ∝ 1/|⟦u⟧|. -/
theorem size_principle :
    cfg.S1 () .green_square .green > cfg.S1 () .green_square .square ∧
    cfg.S1 () .blue_circle .circle > cfg.S1 () .blue_circle .blue :=
  ⟨S1_green_sq_prefers_green, S1_blue_circ_prefers_circle⟩

-- ============================================================================
-- §7. Verification
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .square_pragmatic_narrowing =>
      cfg.L1 .square .blue_square > cfg.L1 .square .green_square
  | .blue_pragmatic_narrowing =>
      cfg.L1 .blue .blue_square > cfg.L1 .blue .blue_circle
  | .green_unique_reference =>
      cfg.L1 .green .green_square > cfg.L1 .green .blue_square
  | .circle_unique_reference =>
      cfg.L1 .circle .blue_circle > cfg.L1 .circle .blue_square

/-- The RSA model accounts for all 4 qualitative findings from F&G (2012). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact square_pragmatic_narrowing
  · exact blue_pragmatic_narrowing
  · exact green_unique_reference
  · exact circle_unique_reference

-- ============================================================================
-- §8. Parameterized Context Types
-- ============================================================================

/-! Frank & Goodman (2012) tested RSA predictions across **7 distinct context types**
varying feature overlap between a target object and 2 distractors. The contexts
are characterized by how many feature dimensions each distractor shares with the
target (Table 1, Figure 2).

Context 2/2b is the canonical blue_square / blue_circle / green_square example
from §2–7 above. The parameterized system below generalizes all 7 contexts via a
single `mkRefGame` constructor: a `ContextSpec` of 4 booleans determines the
full applicability matrix, and `mkRefGame` builds the RSAConfig from it. -/

-- ============================================================================
-- §8a. Domain Types
-- ============================================================================

/-- Three objects in a reference game: target + 2 distractors. -/
inductive Obj3 where
  | target | d1 | d2
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- Feature values in a 2-dimensional reference game.
    dim1_a / dim2_a are the target's values on each dimension.
    b-variants are d1-specific; c-variants are d2-specific. -/
inductive Dim2Feature where
  | dim1_a | dim1_b | dim1_c | dim2_a | dim2_b | dim2_c
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- Context specification: 4 booleans encoding distractor overlap with target.
    Each boolean indicates whether a distractor shares the target's value on
    a given dimension. -/
structure ContextSpec where
  d1_dim1 : Bool  -- distractor 1 shares target's dim1 value
  d1_dim2 : Bool  -- distractor 1 shares target's dim2 value
  d2_dim1 : Bool  -- distractor 2 shares target's dim1 value
  d2_dim2 : Bool  -- distractor 2 shares target's dim2 value

-- ============================================================================
-- §8b. Applicability Matrix
-- ============================================================================

/-- Derive the boolean applicability matrix from a context spec.
    Target features (dim1_a, dim2_a) always apply to target. A distractor
    gets the target's feature if the spec says it shares that dimension;
    otherwise it gets its own unique feature (b for d1, c for d2). -/
def ContextSpec.applies (ctx : ContextSpec) : Dim2Feature → Obj3 → Bool
  | .dim1_a, .target => true
  | .dim2_a, .target => true
  | .dim1_a, .d1 => ctx.d1_dim1
  | .dim1_b, .d1 => !ctx.d1_dim1
  | .dim2_a, .d1 => ctx.d1_dim2
  | .dim2_b, .d1 => !ctx.d1_dim2
  | .dim1_a, .d2 => ctx.d2_dim1
  | .dim1_c, .d2 => !ctx.d2_dim1
  | .dim2_a, .d2 => ctx.d2_dim2
  | .dim2_c, .d2 => !ctx.d2_dim2
  | _, _ => false

-- ============================================================================
-- §8c. RSAConfig Constructor
-- ============================================================================

open RSA Real in
/-- Build an RSAConfig from a boolean applicability matrix.
    All parameters except `meaning` are identical across contexts:
    belief-based S1 scoring with α = 1 and uniform priors. -/
noncomputable def mkRefGame (applies : Dim2Feature → Obj3 → Bool) :
    RSAConfig Dim2Feature Obj3 where
  meaning _ u w := if applies u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by positivity
  worldPrior_nonneg _ := by positivity

-- ============================================================================
-- §8d. The 7 Context Specifications
-- ============================================================================

/-! Each context is defined by its overlap pattern: d1_dim1 × d1_dim2 × d2_dim1 × d2_dim2.

| Context | d1 dim1 | d1 dim2 | d2 dim1 | d2 dim2 | Shared features |
|---------|---------|---------|---------|---------|-----------------|
| 1/1     | ✗       | ✗       | ✗       | ✗       | 0               |
| 1/2     | ✗       | ✗       | ✗       | ✓       | 1               |
| 1/3     | ✗       | ✓       | ✗       | ✓       | 2 (both dim2)   |
| 2/2a    | ✓       | ✓       | ✗       | ✗       | 2 (both d1)     |
| 2/2b    | ✓       | ✗       | ✗       | ✓       | 2 (cross)       |
| 2/3     | ✓       | ✓       | ✗       | ✓       | 3               |
| 3/3     | ✓       | ✓       | ✓       | ✓       | 4               | -/

@[reducible] def spec_1_1  : ContextSpec := ⟨false, false, false, false⟩
@[reducible] def spec_1_2  : ContextSpec := ⟨false, false, false, true⟩
@[reducible] def spec_1_3  : ContextSpec := ⟨false, true, false, true⟩
@[reducible] def spec_2_2a : ContextSpec := ⟨true, true, false, false⟩
@[reducible] def spec_2_2b : ContextSpec := ⟨true, false, false, true⟩
@[reducible] def spec_2_3  : ContextSpec := ⟨true, true, false, true⟩
@[reducible] def spec_3_3  : ContextSpec := ⟨true, true, true, true⟩

-- ============================================================================
-- §8e. RSAConfigs
-- ============================================================================

noncomputable def cfg_1_1  := mkRefGame spec_1_1.applies
noncomputable def cfg_1_2  := mkRefGame spec_1_2.applies
noncomputable def cfg_1_3  := mkRefGame spec_1_3.applies
noncomputable def cfg_2_2a := mkRefGame spec_2_2a.applies
noncomputable def cfg_2_2b := mkRefGame spec_2_2b.applies
noncomputable def cfg_2_3  := mkRefGame spec_2_3.applies
noncomputable def cfg_3_3  := mkRefGame spec_3_3.applies

-- ============================================================================
-- §8f. Predictions
-- ============================================================================

/-! Each context type produces characteristic L1 predictions. The key contrasts:

**Pragmatic narrowing** (context 2/2b): A shared feature identifies the target
because the distractor's S1 prefers a *different* unique feature. This requires
*asymmetric* alternative options — the core RSA insight.

**Symmetric non-narrowing** (context 1/2): A shared feature does NOT narrow
when both objects sharing it have equally good unique alternatives. S1 avoids
the shared feature symmetrically for both, so L1 is uniform on it.

**Symmetric indistinguishability** (contexts 2/2a, 2/3, 3/3): When two objects
share all features, no utterance can distinguish them — even pragmatic reasoning
cannot break the symmetry.

**Uniform informativity** (context 1/3): When all objects share a feature and
each has a unique alternative, S1 avoids the shared feature equally for all
objects, making L1 uniform on that feature. -/

/-- **1/1**: No feature overlap — all features uniquely identify their object.
    dim1_a uniquely picks out the target. -/
theorem L1_1_1_unique :
    cfg_1_1.L1 .dim1_a .target > cfg_1_1.L1 .dim1_a .d1 := by
  rsa_predict

/-- **1/2**: d2 shares dim2 with target, but pragmatic narrowing does NOT
    distinguish them via dim2_a. Both target and d2 have symmetric "escape
    routes" (unique dim1 features), so S1 avoids dim2_a equally for both.
    Contrast with 2/2b where asymmetric sharing enables narrowing. -/
theorem L1_1_2_no_narrowing :
    ¬(cfg_1_2.L1 .dim2_a .target > cfg_1_2.L1 .dim2_a .d2) := by
  rsa_predict

/-- **1/2**: The unique dim1 feature still identifies the target. -/
theorem L1_1_2_unique :
    cfg_1_2.L1 .dim1_a .target > cfg_1_2.L1 .dim1_a .d1 := by
  rsa_predict

/-- **1/3**: Both distractors share dim2. Each object has a unique dim1 feature,
    so S1 avoids dim2_a equally for all → L1("dim2_a") is uniform. -/
theorem L1_1_3_uniform :
    ¬(cfg_1_3.L1 .dim2_a .target > cfg_1_3.L1 .dim2_a .d1) := by
  rsa_predict

/-- **1/3**: Unique dim1 features still work despite dim2 overlap. -/
theorem L1_1_3_unique_dim1 :
    cfg_1_3.L1 .dim1_a .target > cfg_1_3.L1 .dim1_a .d1 := by
  rsa_predict

/-- **2/2a**: d1 shares both dimensions with target — they are featurally
    indistinguishable. No utterance can separate them. -/
theorem L1_2_2a_indistinguishable :
    ¬(cfg_2_2a.L1 .dim1_a .target > cfg_2_2a.L1 .dim1_a .d1) := by
  rsa_predict

/-- **2/2b**: Pragmatic narrowing — the canonical FG2012 result. d1 shares
    dim1, d2 shares dim2. S1(d1) prefers dim2_b (unique), so
    L1("dim1_a") → target over d1. Matches §6 `square_pragmatic_narrowing`
    with different types (Dim2Feature/Obj3 vs Feature/Object). -/
theorem L1_2_2b_narrowing :
    cfg_2_2b.L1 .dim1_a .target > cfg_2_2b.L1 .dim1_a .d1 := by
  rsa_predict

/-- **2/3**: d1 shares both dims (indistinguishable from target).
    dim1_a cannot separate target from d1. -/
theorem L1_2_3_d1_indistinguishable :
    ¬(cfg_2_3.L1 .dim1_a .target > cfg_2_3.L1 .dim1_a .d1) := by
  rsa_predict

/-- **3/3**: All objects share all features — completely indistinguishable.
    L1 is uniform; no utterance provides any information. -/
theorem L1_3_3_indistinguishable :
    ¬(cfg_3_3.L1 .dim1_a .target > cfg_3_3.L1 .dim1_a .d1) := by
  rsa_predict

end Phenomena.Reference.Studies.FrankGoodman2012
