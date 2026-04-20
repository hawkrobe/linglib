import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.PropertyDomain
import Linglib.Paradigms.VisualWorld
import Linglib.Theories.Pragmatics.RSA.Channel
import Linglib.Phenomena.Reference.Studies.SedivyEtAl1999

/-!
# @cite{ronderos-etal-2024}
@cite{sedivy-etal-1999} @cite{kursat-degen-2021} @cite{giles-etal-2026}
@cite{aparicio-xiang-kennedy-2015} @cite{aparicio-2017}

Perceptual, Semantic, and Pragmatic Factors Affect the Derivation of
Contrastive Inferences. *Open Mind: Discoveries in Cognitive Science*
8, 1213–1227.

## Empirical Phenomenon

Cross-linguistic visual-world eye-tracking (English, Hindi, Hungarian)
crossing a same-category contrast manipulation with three adjective
types (color, scalar, material). The paper reports two qualitatively
distinct findings, formalised here as two predicates:

1. **Contrast effect** (target-advantage analysis, §3 Results, ¶1–2):
   the contrastive inference effect — reduced cross-category competitor
   looks in the contrast condition — appears for color and scalar
   adjectives but is absent for material. The interaction term (helmert
   contrast: material vs. color+scalar) is significant.

2. **Scalar baseline disadvantage** (No-Contrast total looks, §3
   Results, ¶4): in the no-contrast condition, fixations on
   target + competitor are *lower* for scalar adjectives than for
   either color (β = 0.25, p < 0.01) or material (β = 0.24, p < 0.05).
   No significant difference between color and material. Attributed to
   scalar adjectives requiring more comparison-class processing
   (@cite{aparicio-xiang-kennedy-2015}, @cite{aparicio-2017}) — gaze
   is more distributed across all four display objects when the listener
   must construct a comparison class.

These two findings target *different mechanisms*: pattern (1) is the
perceptual / pragmatic story (visual salience of the contrastive
property modulates the contrastive inference); pattern (2) is the
semantic story (gradable adjectives demand comparison-class binding).
The paper's contribution is teasing these apart.

## Paradigm

Built on `Paradigms.VisualWorld` (@cite{huettig-rommers-meyer-2011}).
The display contains four objects (`ObjectRole`):

- `target`: the intended referent.
- `contrastingObject`: same category, opposite pole on the adjective
  dimension. Present only in the *contrast* condition.
- `crossCategoryCompetitor`: different category, sharing the
  adjective property with the target. Always present.
- `distractor`: unrelated. Always present.

Within-subjects manipulations on `Cell`:

- **Contrast** (`ContrastCondition`): same-category contrasting object
  present vs. absent.
- **AdjType**: color, scalar, material — a study-local factor that
  partitions the cell space into three strata. Adjective type is *not*
  a paradigm primitive (the @cite{huettig-rommers-meyer-2011} review
  does not single it out), so it stays study-local; the paradigm
  exposes the stratified predicates `ContrastReducesCompetitorLooksWhen`
  and `RoleSumLowerInBaselineWhen` to consume it.

Cross-linguistic generalisation (English, Hindi, Hungarian) is
*methodological* rather than structural: the paper deliberately omits
LANGUAGE as a regression predictor (treating it as a clustering unit
above participants) because the empirical claim is that the same
qualitative pattern survives across all three groups, *not* that the
effect magnitudes are identical. We therefore do not include a
`Language` field on `Cell` — it would force the predicates to make
empirically too-strong pairwise claims (e.g., the marginal-mean
helmert interaction does not entail that every Hungarian material
cell has a smaller contrast effect than every English color cell, as
Figure 3 makes visible). The cross-linguistic generalisation is
documented here in prose; if a future study formalises a
language-stratified predicate at the paradigm level, the field can be
added.

The task is held constant (instruction with definite NP across all
trials), so it is *not* lensed on `Cell` — varying it would have no
within-study consumer.

## Architectural Role

This file is an **empirical anchor**: it defines the experimental cells
and qualitative predicates that downstream theoretical models must
satisfy. The empirical claims are encoded as paradigm-level
predicates, never as `rfl`-over-stipulated-statistics theorems
(@cite{ronderos-etal-2024}'s F/β/p values are documented in prose at
each predicate, per the `CLAUDE.md` Processing scope).

The novel architectural feature relative to @cite{sedivy-etal-1999} is
**stratification**: where Sedivy's contrast effect is universal over
cells, Ronderos's is conditional on the stratum (color or scalar, not
material). The stratified predicate
`Paradigms.VisualWorld.ContrastReducesCompetitorLooksWhen` was added
to support exactly this kind of multi-factor design without inflating
the paradigm with a study-specific factor. The interaction (color and
scalar effects strictly larger than material effects) is expressed via
`Paradigms.VisualWorld.ContrastEffectLargerFor` — the paradigm-level
shape of an "X × condition" interaction.

The scalar baseline disadvantage is expressed via
`Paradigms.VisualWorld.RoleSumLowerInBaselineWhen` — also added to the
paradigm because it is a recurring analysis pattern
(@cite{aparicio-xiang-kennedy-2015} report it on color vs. scalar;
@cite{ronderos-etal-2024} replicate and extend to material vs. scalar).

## Theoretical Significance

Two prior accounts of the contrastive inference effect:

1. **Lexical comparison-class** (@cite{sedivy-etal-1999},
   @cite{bierwisch-1989}): scalar adjectives carry a free
   comparison-class variable, bound by visual context, which makes
   the contrast pair pragmatically informative. Predicts an effect
   for scalar but *not* for color or material (color and material do
   not require a comparison class — see
   `Core.PropertyDomain.requiresComparisonClass`).

2. **Perceptual discrimination** (@cite{kursat-degen-2021},
   @cite{giles-etal-2026}): high perceptual discriminability makes a
   contrastive description informative. Predicts an effect tracking
   the noise-discrimination ordering color > size > material from
   `RSA.Noise`.

Pattern (1) above is the joint envelope: scalar effect (lexical route),
color effect (perceptual route), no material effect (fails both
routes). Pattern (2) above is *additionally* required to capture the
semantic-restrictiveness signature on the no-contrast baseline, which
is observable independent of any contrast manipulation.

## Open architectural threads

- **No theoretical witness for `SatisfiesRonderosPattern`**: only the
  trivial witness `trivialLooks` is provided. A natural deepening is
  to instantiate `Theories/Pragmatics/RSA/Incremental.lean` with a
  noise-perturbed `wordApplies` (using `RSA.Noise.noiseChannel` and
  the per-domain match/mismatch parameters) and prove the resulting
  `LookProportion` satisfies the pattern — this would derive the
  Ronderos effects from the noise-discrimination ordering rather than
  observing structural alignment between two independently stipulated
  orderings. The CG-style vanilla `IncrementalSemantics` (no noise
  channel) cannot satisfy `SatisfiesRonderosPattern` because it would
  predict equal contrast effects for all adjective types — a useful
  negative result that could itself be a theorem.
- **Connection to `Theories/Semantics/Gradability/`**: Ronderos's
  semantic factor (scalar = gradable + comparison-class-dependent;
  color/material = non-gradable) is currently mediated only through
  `Core.PropertyDomain.requiresComparisonClass`. A deeper bridge
  would tie `AdjType.scalar` to the
  `Semantics.Gradability.Classification` subsective/comparison-class
  hierarchy, so the "scalar requires a comparison class" claim is
  derivable from gradability theory rather than projected via the
  domain table.
-/

namespace RonderosEtAl2024

open Paradigms.VisualWorld

-- ============================================================================
-- §1. Study-Specific Factor: Adjective Type
-- ============================================================================

/-- Adjective types crossed with the contrast manipulation.

    - `color`: black, blue, brown, green, orange, red, white, yellow.
    - `scalar`: large, narrow, short, small, tall, thick, thin, wide.
    - `material`: cotton, glass, gold, leather, metal, paper, plastic,
      wooden, woolen.

    Adjective type is a *study-local* factor — it partitions the cells
    but is not lensed (the contrast factor is the only one swapped by
    the paradigm-level predicates here). -/
inductive AdjType where
  | color
  | scalar
  | material
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Map adjective type to its `Core.PropertyDomain`. Scalar adjectives
    are spatial dimensions (`size`); color and material map to their
    eponymous domains. This is the bridge that lets cross-study
    theorems connect Ronderos's adjective-type stratification to
    Sedivy's domain-level reasoning and to `RSA.Noise`'s
    discrimination ordering. -/
def AdjType.toDomain : AdjType → Core.PropertyDomain
  | .color    => .color
  | .scalar   => .size
  | .material => .material

-- ============================================================================
-- §2. Cell
-- ============================================================================

/-- A condition cell in Ronderos's 2 × 3 design (contrast × adjective
    type). Only the contrast factor is lensed — adjective type is
    consumed by the sub-cell predicates in §3. See the module docstring
    for why `Language` is *not* a field. -/
structure Cell where
  contrast : ContrastCondition
  adjType : AdjType
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : HasContrastCondition Cell where
  contrastOf c := c.contrast
  setContrast k c := { c with contrast := k }
  contrastOf_setContrast _ _ := rfl
  setContrast_contrastOf _ := rfl
  setContrast_setContrast _ _ _ := rfl

/-- Display kind is the four-object workspace throughout, per the
    paper's Methods. Between-study constant, no lens. -/
instance : HasDisplayKind Cell where
  displayKindOf _ := .objectArray

/-! Note: no `HasTask` instance. The task is fixed (definite-NP
instruction) across all cells — a constant projection cannot satisfy
the `setTask`/`taskOf` lens laws (`taskOf (setTask k c) = k` would
force the projection to vary). Studies that hold a paradigm factor
constant should *omit* the lens, not stub it with a constant. -/

-- ============================================================================
-- §3. Sub-cell Predicates (Strata)
-- ============================================================================

/-! Adjective type partitions the cell space into three strata. The
paradigm-level predicates `ContrastReducesCompetitorLooksWhen`,
`ContrastEffectLargerFor`, and `RoleSumLowerInBaselineWhen` consume
`Cell → Prop` filters; defining the strata as Props lets us state the
empirical patterns at exactly the granularity Ronderos's analysis
reports. -/

/-- Cells whose adjective is a color term. -/
def ColorCells (c : Cell) : Prop := c.adjType = .color

/-- Cells whose adjective is a scalar (spatial-dimension) term. -/
def ScalarCells (c : Cell) : Prop := c.adjType = .scalar

/-- Cells whose adjective is a material term. -/
def MaterialCells (c : Cell) : Prop := c.adjType = .material

/-- The "inference-triggering" strata — color and scalar adjective
    types — corresponding to the helmert-coded grouping the paper uses
    for the interaction analysis (material vs. color+scalar). The name
    is *interpretive* of the paper's conclusion that this group
    produces a contrastive inference; the underlying primitive is the
    helmert contrast. -/
def InferenceTriggeringCells (c : Cell) : Prop :=
  ColorCells c ∨ ScalarCells c

-- ============================================================================
-- §4. Empirical Pattern
-- ============================================================================

/-! The Ronderos pattern is encoded as a `Prop`-valued structure with
one field per qualitative finding. The empirical claims fall into two
distinct families with two distinct observables:

- **Contrast-effect family** (target-advantage / cluster-permutation
  analyses, §3 Results ¶1–3): four fields, all over the contrast
  manipulation on cross-category-competitor looks.
- **Baseline-restrictiveness family** (No-Contrast total-looks
  analysis, §3 Results ¶4): two fields, comparing the
  target + competitor role-sum across strata in the no-contrast
  baseline.

A theory of contrastive inference "satisfies the Ronderos pattern" iff
its predicted look proportions satisfy *all* fields. Statistical
readings (the F/β/p values cited below) need a real-valued aggregator
and are out of scope for the paradigm contract. -/

/-- A look-proportion observable **satisfies the Ronderos pattern** if:

    **Contrast-effect family** (§3 Results ¶1–3):

    - `color_contrast_reduces_competitor`: paradigm-level
      `ContrastReducesCompetitorLooksWhen ColorCells` — every color
      cell shows a strictly smaller cross-category competitor look
      proportion in the contrast condition than in the no-contrast
      condition. Paper §3 ¶1: significant cluster 240–600 ms post
      adjective onset (sum-t = 39.61, p < 0.01). §3 ¶2: target-
      advantage β = 0.24, t = 2.41, p < 0.05.
    - `scalar_contrast_reduces_competitor`: same shape, restricted to
      `ScalarCells`. §3 ¶1: significant cluster 260–500 ms
      (sum-t = 33.07, p < 0.01). §3 ¶2: β = 0.19, t = 2.02, p < 0.05.
    - `material_effect_smaller`: paradigm-level
      `ContrastEffectLargerFor InferenceTriggeringCells MaterialCells`
      — the contrast effect on every inference-triggering cell strictly
      exceeds the contrast effect on every material cell. §3 ¶1
      adjective-type × condition interaction: significant cluster
      280–600 ms (sum-t = 37.96, p < 0.01). §3 ¶2 reports the material
      main effect as non-significant (β = 0.10, t = 1.08, p = 0.28).

    The *absence* of a `material_contrast_reduces_competitor` field is
    deliberate: a null finding is encoded by absence, not by adding
    `¬ ContrastReducesCompetitorLooksWhen MaterialCells looks`
    (statistical power and direction-of-null are prose, not theorem).
    The interaction field is the stronger qualitative claim that
    survives without statistical machinery: material's effect is
    *strictly smaller* than the others, not exactly zero.

    **Baseline-restrictiveness family** (§3 Results ¶4):

    - `scalar_baseline_lower_than_color`: paradigm-level
      `RoleSumLowerInBaselineWhen .noContrast [.target,
      .crossCategoryCompetitor] ScalarCells ColorCells` — in the
      no-contrast baseline, total looks on target + cross-category
      competitor are strictly lower for scalar than for color cells.
      §3 ¶4: β = 0.25, z = 2.80, p < 0.01.
    - `scalar_baseline_lower_than_material`: same shape, scalar vs.
      material. §3 ¶4: β = 0.24, z = 2.40, p < 0.05.

    The paper reports *no* significant color-vs-material baseline
    difference; we encode this null by the *absence* of a field
    asserting either direction (same convention as the contrast-effect
    null). The two scalar fields together encode the paper's
    interpretation: scalar adjectives demand comparison-class
    processing, distributing gaze across all four display objects and
    away from the two critical roles. This semantic factor is
    independent of the contrast manipulation. -/
structure SatisfiesRonderosPattern {R : Type} [LT R] [Sub R] [Add R]
    [Zero R] (looks : LookProportion Cell R) : Prop where
  color_contrast_reduces_competitor :
    ContrastReducesCompetitorLooksWhen (Cell := Cell) (R := R)
      ColorCells looks
  scalar_contrast_reduces_competitor :
    ContrastReducesCompetitorLooksWhen (Cell := Cell) (R := R)
      ScalarCells looks
  material_effect_smaller :
    ContrastEffectLargerFor (Cell := Cell) (R := R)
      .crossCategoryCompetitor InferenceTriggeringCells MaterialCells looks
  scalar_baseline_lower_than_color :
    RoleSumLowerInBaselineWhen (Cell := Cell) (R := R)
      .noContrast [.target, .crossCategoryCompetitor]
      ScalarCells ColorCells looks
  scalar_baseline_lower_than_material :
    RoleSumLowerInBaselineWhen (Cell := Cell) (R := R)
      .noContrast [.target, .crossCategoryCompetitor]
      ScalarCells MaterialCells looks

-- ============================================================================
-- §5. Non-Vacuity Witness
-- ============================================================================

/-- A trivial look model exhibiting both Ronderos shapes simultaneously.

    Cross-category competitor looks: 1 in every contrast cell;
    in no-contrast cells, color 5, scalar 4, material 2. The contrast
    effect is therefore color 4, scalar 3, material 1 — strictly
    positive everywhere with inference-triggering strata strictly
    exceeding material.

    Target looks (no-contrast only): color 5, scalar 1, material 6.
    The target + competitor role-sum in the no-contrast baseline is
    therefore color 10, scalar 5, material 8 — scalar strictly below
    both, satisfying the baseline disadvantage fields.

    Witness only — carries no theoretical content. -/
def trivialLooks : LookProportion Cell ℚ := fun role c =>
  match role, c.contrast, c.adjType with
  | .crossCategoryCompetitor, .contrast,   _         => 1
  | .crossCategoryCompetitor, .noContrast, .color    => 5
  | .crossCategoryCompetitor, .noContrast, .scalar   => 4
  | .crossCategoryCompetitor, .noContrast, .material => 2
  | .target,                  .noContrast, .color    => 5
  | .target,                  .noContrast, .scalar   => 1
  | .target,                  .noContrast, .material => 6
  | _, _, _                                          => 0

/-- The Ronderos pattern is satisfiable: `trivialLooks` satisfies all
    five fields. Without this witness the structure could in principle
    be uninhabited. -/
theorem trivial_satisfies_pattern :
    SatisfiesRonderosPattern trivialLooks where
  color_contrast_reduces_competitor := by
    intro c hc
    obtain ⟨k, a⟩ := c
    simp only [ColorCells] at hc
    subst hc
    cases k <;> simp [trivialLooks]
  scalar_contrast_reduces_competitor := by
    intro c hc
    obtain ⟨k, a⟩ := c
    simp only [ScalarCells] at hc
    subst hc
    cases k <;> simp [trivialLooks]
  material_effect_smaller := by
    intro cP cQ hP hQ
    obtain ⟨kP, aP⟩ := cP
    obtain ⟨kQ, aQ⟩ := cQ
    simp only [InferenceTriggeringCells, ColorCells, ScalarCells,
      MaterialCells] at hP hQ
    subst hQ
    rcases hP with hC | hS
    all_goals (subst_vars; cases kP <;> cases kQ <;>
      simp [contrastEffect, trivialLooks] <;> norm_num)
  scalar_baseline_lower_than_color := by
    intro cS cC hS hC
    obtain ⟨kS, aS⟩ := cS
    obtain ⟨kC, aC⟩ := cC
    simp only [ScalarCells, ColorCells] at hS hC
    subst hS; subst hC
    simp [roleSum, trivialLooks]; norm_num
  scalar_baseline_lower_than_material := by
    intro cS cM hS hM
    obtain ⟨kS, aS⟩ := cS
    obtain ⟨kM, aM⟩ := cM
    simp only [ScalarCells, MaterialCells] at hS hM
    subst hS; subst hM
    simp [roleSum, trivialLooks]; norm_num

-- ============================================================================
-- §6. Cross-Study Bridges
-- ============================================================================

/-! These theorems articulate the theoretical positions Ronderos's data
take on. They are *type-level* connections to the relevant
infrastructure (`Core.PropertyDomain`, `RSA.Noise`,
`SedivyEtAl1999`), not restated empirical claims. -/

/-- **Agreement with @cite{sedivy-etal-1999} on scalar adjectives.**
    Both studies place the scalar contrast effect on the size domain,
    which `Core.PropertyDomain` flags as requiring comparison-class
    binding. -/
theorem scalar_shares_sedivy_domain :
    AdjType.toDomain .scalar = SedivyEtAl1999.adjDomain ∧
    Core.PropertyDomain.requiresComparisonClass
      (AdjType.toDomain .scalar) = true :=
  ⟨rfl, rfl⟩

/-- **Disagreement with the comparison-class-only mechanism on color.**
    Color does *not* require comparison-class binding (so the
    Bierwisch/Sedivy mechanism alone predicts no contrast effect for
    color), yet Ronderos finds a robust color contrast effect. -/
theorem color_does_not_require_comparison_class :
    Core.PropertyDomain.requiresComparisonClass
      (AdjType.toDomain .color) = false := rfl

/-- **Material fails the comparison-class route.** Material adjectives,
    like color, do not require comparison-class binding — so the
    lexical mechanism predicts no contrast effect, consistent with
    Ronderos's null finding for material. (The lexical mechanism alone
    is insufficient for color, however; see
    `color_does_not_require_comparison_class`.) -/
theorem material_does_not_require_comparison_class :
    Core.PropertyDomain.requiresComparisonClass
      (AdjType.toDomain .material) = false := rfl

/-- **Effect ordering aligns with noise discrimination.** The
    perceptual-discrimination route predicts the cross-category
    competitor reduction to track `RSA.Noise`'s discrimination
    ordering. Ronderos's qualitative effect ordering — present for
    color and scalar, absent for material — is consistent with
    `RSA.Noise`'s ordering color (≈0.98) > size (≈0.60) > material
    (≈0.40). @cite{kursat-degen-2021} found the same direction on
    the production side; @cite{ronderos-etal-2024} extends it to
    comprehension. -/
theorem effect_ordering_aligns_with_noise_discrimination :
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination :=
  ⟨RSA.Noise.color_gt_size, RSA.Noise.size_gt_material⟩

/-- **PropertyDomain ↔ noise discrimination wiring.** Each adjective
    type maps through `AdjType.toDomain` to a `PropertyDomain` that
    `Core.PropertyDomain.noiseDiscrimination` resolves to the
    corresponding `RSA.Noise` constant. Recorded here so the bridge
    to discrimination ordering is auditable. -/
theorem adjType_to_noise_discrimination :
    Core.PropertyDomain.noiseDiscrimination (AdjType.toDomain .color)
      = some RSA.Noise.colorDiscrimination ∧
    Core.PropertyDomain.noiseDiscrimination (AdjType.toDomain .scalar)
      = some RSA.Noise.sizeDiscrimination ∧
    Core.PropertyDomain.noiseDiscrimination (AdjType.toDomain .material)
      = some RSA.Noise.materialDiscrimination :=
  ⟨rfl, rfl, rfl⟩

/-- **The two empirical families project onto different mechanisms.**
    The contrast-effect family is keyed off
    `Core.PropertyDomain.noiseDiscrimination` (perceptual route): all
    three adjective types have *some* discrimination value, but only
    those above the material level produce a contrast effect. The
    baseline-restrictiveness family is keyed off
    `Core.PropertyDomain.requiresComparisonClass` (semantic route):
    only the scalar (size) domain returns `true`, predicting the
    no-contrast baseline disadvantage to be uniquely scalar.

    This theorem records the two-mechanism factorisation as a typed
    statement: the scalar adjective type is the *unique* one whose
    domain requires a comparison class; color and material are the
    *two* whose domains have noise discrimination strictly above the
    material baseline (where "above the material baseline" means
    "strictly larger" — material is at the floor). The two
    mechanisms therefore make orthogonal predictions, and Ronderos's
    pattern is the joint envelope. -/
theorem two_mechanisms_factorise :
    -- Semantic route: scalar uniquely requires comparison class
    Core.PropertyDomain.requiresComparisonClass
      (AdjType.toDomain .scalar) = true ∧
    Core.PropertyDomain.requiresComparisonClass
      (AdjType.toDomain .color) = false ∧
    Core.PropertyDomain.requiresComparisonClass
      (AdjType.toDomain .material) = false ∧
    -- Perceptual route: color and scalar strictly above material
    RSA.Noise.colorDiscrimination > RSA.Noise.materialDiscrimination ∧
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination :=
  ⟨rfl, rfl, rfl,
   lt_trans RSA.Noise.size_gt_material RSA.Noise.color_gt_size,
   RSA.Noise.size_gt_material⟩

end RonderosEtAl2024
