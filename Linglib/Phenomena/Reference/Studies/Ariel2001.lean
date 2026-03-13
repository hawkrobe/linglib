import Linglib.Core.Discourse.ReferentialForm
import Linglib.Phenomena.Anaphora.Typology

/-!
# @cite{ariel-2001}
@cite{gundel-hedberg-zacharski-1993} @cite{cardinaletti-starke-1999}

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

The 18-level `AccessibilityLevel` type (defined in `Core/Discourse/ReferentialForm.lean`)
encodes Ariel's ordering. This study file adds the three form-function criteria
(informativity, rigidity, attenuation), the multi-factor accessibility assessment,
and comparisons with competing theories.

## Form-Function Criteria

The ordering is motivated by three partially overlapping criteria, all
anti-correlated with accessibility degree:

1. **Informativity**: amount of lexical content (more → lower accessibility)
2. **Rigidity**: ability to uniquely pick out a referent from form alone
   (proper names are rigid designators; descriptions are context-dependent)
3. **Attenuation**: phonological reduction (more reduced → higher accessibility)

## Non-Equivalence with `DefinitenessLevel`

The 5-level `DefinitenessLevel` scale (used for DOM/DSM in `Core.Prominence`)
is a many-to-one coarsening of the 18-level scale, but the coarsening is
**not monotone**: proper names are less accessible than definite descriptions
on Ariel's scale (names are more informative, lower accessibility), but more
prominent on Aissen's scale (names outrank definites for DOM).

## Competing Theories

Ariel argues accessibility theory subsumes @cite{gundel-hedberg-zacharski-1993}'s
Givenness Hierarchy (a 6-level coarsening with weaker predictions) and is
more comprehensive than Centering Theory (which handles only the pronoun/full-NP
distinction, not the full range of referring expressions).
-/

set_option autoImplicit false

-- Extend the Core namespace with study-specific form-function criteria.
-- This enables dot notation (e.g., AccessibilityLevel.zero.informativity).
namespace Core.Discourse.ReferentialForm

/-- Informativity: approximate lexical content, encoded as an ordinal
    ranking (0–4). Anti-correlated with accessibility (more informative
    → lower rank). Values are illustrative, encoding the relative ordering
    described in @cite{ariel-2001} (p. 32), not exact content-word counts. -/
def AccessibilityLevel.informativity : AccessibilityLevel → Nat
  | .fullNameMod                              => 4
  | .fullName | .longDefDescription           => 3
  | .shortDefDescription | .distalDemMod
  | .proxDemMod                               => 2
  | .lastName | .firstName | .distalDemNP
  | .proxDemNP | .distalDem | .proxDem
  | .stressedPronGesture | .stressedPron
  | .unstressedPron                           => 1
  | .cliticizedPron | .verbalAgreement | .zero => 0

/-- Rigidity: the ability to uniquely pick out a referent from
    form alone, independent of context. Anti-correlated with
    accessibility (more rigid → lower accessibility).

    Proper names are rigid designators (Kripke): they pick out
    the same individual regardless of context. Definite descriptions
    are descriptive but context-dependent. Pronouns and zeros
    carry only person/number/gender features and are maximally
    non-rigid. -/
def AccessibilityLevel.rigidity : AccessibilityLevel → Nat
  | .fullNameMod | .fullName | .lastName | .firstName  => 2
  | .longDefDescription | .shortDefDescription
  | .distalDemMod | .proxDemMod
  | .distalDemNP | .proxDemNP                          => 1
  | .distalDem | .proxDem
  | .stressedPronGesture | .stressedPron | .unstressedPron
  | .cliticizedPron | .verbalAgreement | .zero          => 0

/-- Attenuation: degree of phonological reduction.
    Positively correlated with accessibility. 0 = full, 5 = zero.
    Cliticized pronouns are shortened free pronouns (@cite{ariel-2001} note 6);
    verbal agreement inflections are bound morphemes, more reduced
    still; zero has no phonological material. -/
def AccessibilityLevel.attenuation : AccessibilityLevel → Nat
  | .fullNameMod | .fullName | .longDefDescription
  | .shortDefDescription | .lastName | .firstName
  | .distalDemMod | .proxDemMod                     => 0
  | .distalDemNP | .proxDemNP | .distalDem | .proxDem
  | .stressedPronGesture | .stressedPron              => 1
  | .unstressedPron                                   => 2
  | .cliticizedPron                                   => 3
  | .verbalAgreement                                  => 4
  | .zero                                             => 5

def AccessibilityLevel.all : List AccessibilityLevel :=
  [.fullNameMod, .fullName, .longDefDescription, .shortDefDescription,
   .lastName, .firstName, .distalDemMod, .proxDemMod,
   .distalDemNP, .proxDemNP, .distalDem, .proxDem,
   .stressedPronGesture, .stressedPron, .unstressedPron,
   .cliticizedPron, .verbalAgreement, .zero]

end Core.Discourse.ReferentialForm

namespace Phenomena.Reference.Studies.Ariel2001

open Core.Prominence (DefinitenessLevel)
open Core.Discourse.ReferentialForm

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
    maximallyAccessible.score > minimallyAccessible.score := by native_decide

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
    AccessibilityLevel.fullName.toDefLevel.rank >
      AccessibilityLevel.longDefDescription.toDefLevel.rank := by
  decide

-- ════════════════════════════════════════════════════
-- § 4. PronounStrength Bridge
-- ════════════════════════════════════════════════════

open Phenomena.Anaphora.Typology (PronounStrength)

/-- @cite{cardinaletti-starke-1999}'s three-way pronoun strength maps to
    positions on the accessibility scale.
    strong → stressedPron, weak → unstressedPron, clitic → cliticizedPron. -/
def strengthToAccessibility : PronounStrength → AccessibilityLevel
  | .strong => .stressedPron
  | .weak   => .unstressedPron
  | .clitic => .cliticizedPron

/-- Pronoun strength ordering matches accessibility ordering:
    clitic > weak > strong in accessibility. -/
theorem strength_matches_accessibility :
    (strengthToAccessibility .clitic).rank >
    (strengthToAccessibility .weak).rank ∧
    (strengthToAccessibility .weak).rank >
    (strengthToAccessibility .strong).rank := by decide

/-- All three pronoun strengths coarsen to the same definiteness level. -/
theorem strength_coarsening_agrees :
    (strengthToAccessibility .strong).toDefLevel = DefinitenessLevel.personalPronoun ∧
    (strengthToAccessibility .weak).toDefLevel = DefinitenessLevel.personalPronoun ∧
    (strengthToAccessibility .clitic).toDefLevel = DefinitenessLevel.personalPronoun :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Givenness Hierarchy (@cite{gundel-hedberg-zacharski-1993})
-- ════════════════════════════════════════════════════

/-- Gundel, Hedberg & Zacharski (1993): six cognitive statuses organized
    as an implicational hierarchy. Each status implies all lower ones.

    in focus > activated > familiar > uniquely identifiable >
    referential > type identifiable -/
inductive GivennessStatus where
  | inFocus              -- unstressed pronoun
  | activated            -- that, this, this N
  | familiar             -- that N
  | uniquelyIdentifiable -- the N
  | referential          -- indefinite this N
  | typeIdentifiable     -- a N
  deriving DecidableEq, BEq, Repr

def GivennessStatus.rank : GivennessStatus → Nat
  | .inFocus              => 5
  | .activated            => 4
  | .familiar             => 3
  | .uniquelyIdentifiable => 2
  | .referential          => 1
  | .typeIdentifiable     => 0

/-- Prototypical accessibility level for each givenness status.

    **Caveat**: Gundel et al.'s lower statuses (`referential` = "indefinite
    this N", `typeIdentifiable` = "a N") correspond to **indefinite**
    expressions, which do not appear on Ariel's accessibility marking
    scale (which covers Given/definite referential forms). The mapping
    for these two is by approximate accessibility degree, not by form
    identity. Ariel herself notes (p. 63) that the Givenness Hierarchy's
    coverage is "suspiciously compatible with the distribution of just
    those referring expressions linguists have tended to focus on." -/
def GivennessStatus.toAccessibility : GivennessStatus → AccessibilityLevel
  | .inFocus              => .unstressedPron
  | .activated            => .proxDem
  | .familiar             => .distalDemNP
  | .uniquelyIdentifiable => .shortDefDescription
  | .referential          => .longDefDescription
  | .typeIdentifiable     => .fullNameMod

/-- The Givenness→Accessibility mapping IS monotone: higher givenness
    status maps to higher or equal accessibility rank. The Givenness
    Hierarchy is a well-behaved (but lossy) coarsening of Ariel's scale. -/
theorem givenness_coarsening_monotone :
    let all := [GivennessStatus.inFocus, .activated, .familiar,
                .uniquelyIdentifiable, .referential, .typeIdentifiable]
    all.all (λ a => all.all (λ b =>
      if a.rank > b.rank then
        a.toAccessibility.rank ≥ b.toAccessibility.rank
      else true)) = true := by native_decide

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
    AccessibilityLevel.unstressedPron.toDefLevel = .personalPronoun ∧
    AccessibilityLevel.cliticizedPron.toDefLevel = .personalPronoun ∧
    AccessibilityLevel.verbalAgreement.toDefLevel = .personalPronoun ∧
    AccessibilityLevel.zero.toDefLevel = .personalPronoun ∧
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
    @cite{ariel-2001}'s theory: more accessible → more reduced form.

    The predicted forms are the RIGHT forms, not a coarsened approximation
    through `DefinitenessLevel`. -/
theorem predictedForm_uses_accessibility :
    NextMentionBias.high.predictedForm = .unstressedPron ∧
    NextMentionBias.low.predictedForm = .fullName :=
  ⟨rfl, rfl⟩

end Phenomena.Reference.Studies.Ariel2001
