import Linglib.Discourse.Accessibility
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Features.Givenness

/-!
# [ariel-2001]
[gundel-hedberg-zacharski-1993] [cardinaletti-starke-1999]

Accessibility Theory: An Overview. In Sanders, Schilperoord & Spooren (eds.),
*Text Representation: Linguistic and Psycholinguistic Aspects*, 29–87.
John Benjamins.

## Core Theory

Referential form choice is governed by the **degree of accessibility** of the
mental representation the speaker intends the addressee to retrieve. More
accessible representations license more reduced referring expressions.
Accessibility is gradient (not categorical) and is assessed via a composite
of multiple factors.

## The Accessibility Marking Scale

The 18-level `AccessibilityLevel` type and its three form-function criteria
(informativity, rigidity, attenuation) live in `Discourse/Accessibility.lean`.
This study file adds the multi-factor accessibility assessment and
comparisons with competing theories.

## Form-Function Criteria

The ordering is motivated by three partially overlapping criteria, all
anti-correlated with accessibility degree:

1. **Informativity**: amount of lexical content (more → lower accessibility)
2. **Rigidity**: ability to uniquely pick out a referent from form alone
   (proper names are rigid designators; descriptions are context-dependent)
3. **Attenuation**: phonological reduction (more reduced → higher accessibility)

## Non-Equivalence with `DefinitenessLevel`

The 5-level `DefinitenessLevel` scale (used for DOM/DSM in `Features.Prominence`)
is a many-to-one coarsening of the 18-level scale, but the coarsening is
**not monotone**: proper names are less accessible than definite descriptions
on Ariel's scale (names are more informative, lower accessibility), but more
prominent on Aissen's scale (names outrank definites for DOM).

## Competing Theories

Ariel argues accessibility theory subsumes [gundel-hedberg-zacharski-1993]'s
Givenness Hierarchy (a 6-level coarsening with weaker predictions) and is
more comprehensive than Centering Theory (which handles only the pronoun/full-NP
distinction, not the full range of referring expressions).
-/

namespace Ariel2001

open Features.Prominence (DefinitenessLevel)
open Features (GivennessStatus)
open Discourse

-- ════════════════════════════════════════════════════
-- § 1. Form-Function Criteria
-- ════════════════════════════════════════════════════

/-- The highest-accessibility forms have the lowest informativity. -/
theorem zero_least_informative :
    AccessibilityLevel.zero.informativity = 0 ∧
    AccessibilityLevel.verbalAgreement.informativity = 0 ∧
    AccessibilityLevel.cliticizedPron.informativity = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The highest-accessibility forms have the highest attenuation. -/
theorem zero_most_attenuated :
    AccessibilityLevel.zero.attenuation = 5 := rfl

/-- The three form-function criteria all correlate with accessibility
    in the predicted direction at the extremes of the scale:
    - Least accessible (fullNameMod): max informativity, max rigidity, min attenuation
    - Most accessible (zero): min informativity, min rigidity, max attenuation -/
theorem criteria_correlate_at_extremes :
    AccessibilityLevel.fullNameMod.informativity = 4 ∧
    AccessibilityLevel.fullNameMod.rigidity = 2 ∧
    AccessibilityLevel.fullNameMod.attenuation = 0 ∧
    AccessibilityLevel.zero.informativity = 0 ∧
    AccessibilityLevel.zero.rigidity = 0 ∧
    AccessibilityLevel.zero.attenuation = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Names are rigid but low-accessibility; pronouns are non-rigid but
    high-accessibility. This is the rigidity–accessibility anti-correlation. -/
theorem names_rigid_pronouns_not :
    AccessibilityLevel.fullName.rigidity > AccessibilityLevel.unstressedPron.rigidity ∧
    AccessibilityLevel.fullName.rank < AccessibilityLevel.unstressedPron.rank := by
  decide

-- ════════════════════════════════════════════════════
-- § 2. Accessibility Factors
-- ════════════════════════════════════════════════════

/-- Factors contributing to degree of accessibility of a discourse referent.
    Accessibility is a composite of all four; no single factor suffices. -/
structure AccessibilityAssessment where
  /-- Clauses since last mention (0 = same clause). Lower → higher accessibility. -/
  distance : Nat
  /-- Discourse salience. 0=non-topic, 1=local topic, 2=global topic. -/
  topicality : Fin 3
  /-- Number of competing potential antecedents. Fewer → higher accessibility. -/
  competition : Nat
  /-- Syntactic/semantic cohesion. 0=loose (coordination), 1=moderate
      (subordination), 2=tight (complement). -/
  unity : Fin 3
  deriving Repr

/-- Composite accessibility score (simplified additive model).
    Higher score → higher accessibility → more reduced form predicted. -/
def AccessibilityAssessment.score (a : AccessibilityAssessment) : Nat :=
  (a.topicality : Nat) + (a.unity : Nat) + (5 - min a.distance 5) + (3 - min a.competition 3)

def maximallyAccessible : AccessibilityAssessment := ⟨0, 2, 0, 2⟩
def minimallyAccessible : AccessibilityAssessment := ⟨5, 0, 3, 0⟩

theorem maximal_gt_minimal :
    maximallyAccessible.score > minimallyAccessible.score := by decide

-- ════════════════════════════════════════════════════
-- § 3. Non-Equivalence with DefinitenessLevel
-- ════════════════════════════════════════════════════

/-- The coarsening is NOT monotone: "full name" (accessibility rank 1) maps
    to properName (definiteness rank 3), but "long definite description"
    (accessibility rank 2) maps to definite (definiteness rank 2).
    Higher accessibility maps to LOWER definiteness rank here.

    This proves that Ariel's accessibility scale and Aissen's definiteness
    scale capture genuinely different orderings: names are less accessible
    (more informative) but more prominent (higher on the DOM hierarchy). -/
theorem coarsening_not_monotone :
    AccessibilityLevel.fullName.rank < AccessibilityLevel.longDefDescription.rank ∧
    AccessibilityLevel.fullName.toDefinitenessLevel.rank >
      AccessibilityLevel.longDefDescription.toDefinitenessLevel.rank := by
  decide

-- ════════════════════════════════════════════════════
-- § 4. Strength Bridge
-- ════════════════════════════════════════════════════

open Pronoun (Strength)

/-- [cardinaletti-starke-1999]'s three-way pronoun strength maps to
    positions on the accessibility scale.
    strong → stressedPron, weak → unstressedPron, clitic → cliticizedPron. -/
def strengthToAccessibility : Strength → AccessibilityLevel
  | .strong => .stressedPron
  | .weak   => .unstressedPron
  | .clitic => .cliticizedPron

/-- `strengthToAccessibility` is antitone in structural strength: a more
    deficient pronoun (lower in the deficiency order) marks higher
    accessibility, so the clitic > weak > strong accessibility ordering
    follows from the intrinsic deficiency order rather than being restated. -/
theorem strengthToAccessibility_antitone {a b : Strength}
    (h : a < b) :
    (strengthToAccessibility b).rank < (strengthToAccessibility a).rank := by
  cases a <;> cases b <;> revert h <;> decide

/-- All three pronoun strengths coarsen to the same definiteness level. -/
theorem strength_coarsening_agrees :
    (strengthToAccessibility .strong).toDefinitenessLevel = DefinitenessLevel.personalPronoun ∧
    (strengthToAccessibility .weak).toDefinitenessLevel = DefinitenessLevel.personalPronoun ∧
    (strengthToAccessibility .clitic).toDefinitenessLevel = DefinitenessLevel.personalPronoun :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Givenness Hierarchy ([gundel-hedberg-zacharski-1993])
-- ════════════════════════════════════════════════════

-- `GivennessStatus`, `GivennessStatus.rank`, and the
-- `GivennessStatus.toAccessibility` projection live in the substrate
-- layer (`Features/Givenness.lean`, `Discourse/Accessibility.lean`);
-- the theorems below consume the substrate projection.

/-- The Givenness→Accessibility mapping IS monotone: higher givenness
    status maps to higher or equal accessibility rank. The Givenness
    Hierarchy is a well-behaved (but lossy) coarsening of Ariel's scale. -/
theorem givenness_coarsening_monotone :
    let all := [GivennessStatus.inFocus, .activated, .familiar,
                .uniquelyIdentifiable, .referential, .typeIdentifiable]
    all.all (λ a => all.all (λ b =>
      if a.rank > b.rank then
        a.toAccessibility.rank ≥ b.toAccessibility.rank
      else true)) = true := by decide

-- ════════════════════════════════════════════════════
-- § 6. Ariel's Critique: Coarsening Loses Distinctions
-- ════════════════════════════════════════════════════

/-- Four accessibility levels that the Givenness Hierarchy collapses into
    "in focus" have genuinely different accessibility ranks and different
    discourse distributions (p. 64). The 6-level hierarchy asks: "How can
    we distinguish between zeroes and pronouns in a language which uses
    both as very high accessibility markers... Both must be classified as
    'in focus' markers, but they each have a distinct distributional
    pattern." -/
theorem givenness_collapses_pronominal_distinctions :
    -- All four are "in focus" on the Givenness Hierarchy (all pronominal)
    AccessibilityLevel.unstressedPron.toDefinitenessLevel = .personalPronoun ∧
    AccessibilityLevel.cliticizedPron.toDefinitenessLevel = .personalPronoun ∧
    AccessibilityLevel.verbalAgreement.toDefinitenessLevel = .personalPronoun ∧
    AccessibilityLevel.zero.toDefinitenessLevel = .personalPronoun ∧
    -- Yet they have four distinct accessibility ranks
    AccessibilityLevel.zero.rank > AccessibilityLevel.verbalAgreement.rank ∧
    AccessibilityLevel.verbalAgreement.rank > AccessibilityLevel.cliticizedPron.rank ∧
    AccessibilityLevel.cliticizedPron.rank > AccessibilityLevel.unstressedPron.rank := by
  decide

/-- Proximate demonstratives code higher accessibility than distal ones.
    Both are "activated" in the Givenness Hierarchy — the 6-level system
    cannot capture this contrast. -/
theorem proximate_more_accessible_than_distal :
    AccessibilityLevel.proxDem.rank > AccessibilityLevel.distalDem.rank ∧
    AccessibilityLevel.proxDemNP.rank > AccessibilityLevel.distalDemNP.rank := by
  decide

-- ════════════════════════════════════════════════════
-- § 7. Integration: Accessibility ↔ NextMentionBias
-- ════════════════════════════════════════════════════

/-- The `NextMentionBias` prediction directly uses accessibility levels:
    high bias → unstressed pronoun (high accessibility),
    low bias → full name (low accessibility). This is the core of
    [ariel-2001]'s theory: more accessible → more reduced form.

    The predicted forms are the RIGHT forms, not a coarsened approximation
    through `DefinitenessLevel`. -/
theorem predictedForm_uses_accessibility :
    NextMentionBias.high.predictedForm = .unstressedPron ∧
    NextMentionBias.low.predictedForm = .fullName :=
  ⟨rfl, rfl⟩

end Ariel2001
