import Linglib.Features.Givenness
import Linglib.Features.Prominence
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Accessibility Marking Scale — Referential Form Taxonomy
[ariel-2001] [arnold-wasow-losongco-ginstrom-2000]

Per-entry feature taxonomy classifying referring expressions by
**accessibility** — the degree to which the referent's mental
representation is available to the addressee. Speakers choose between
reduced (pronoun) and full (name, description) forms based on this
accessibility ([ariel-2001]).

## The Accessibility Marking Scale

`AccessibilityLevel` is [ariel-2001]'s 18-level ordering from
least accessible (full name + modifier) to most accessible (zero /
pro-drop). This replaces the earlier conflation with `DefinitenessLevel`
— the accessibility and definiteness scales are **non-monotonically**
related (names are less accessible than definite descriptions but more
prominent for DOM), so they must be separate types. A coarsening
function `toDefLevel` bridges to the DOM/DSM scale when needed.

## Layer position

`Features/`. Sibling of `Features/Givenness.lean` (the GHZ-6
hierarchy). Both are per-entry feature taxonomies for cognitive
status: `AccessibilityLevel` classifies *forms* by their
accessibility-marking behavior; `GivennessStatus` classifies *entities*
by cognitive status. Ariel argues (her chapter pp. 62-65) that
`AccessibilityLevel`'s 18 tiers are better empirically supported than
GHZ-6's 6 tiers; both retained as substrate because they serve
different consumer profiles. The `GivennessStatus.toAccessibility`
projection (in `Studies/Ariel2001.lean`) bridges
them.

This module connects referential form choice to word-order position
choice via the shared dimension of NP weight/reduction.
-/

set_option autoImplicit false

namespace Features

open Features.Prominence

-- ════════════════════════════════════════════════════
-- § 1. Accessibility Marking Scale
-- ════════════════════════════════════════════════════

/-- [ariel-2001]'s Accessibility Marking Scale: a fine-grained ordering
    of referential form types from least to most accessible.

    Each constructor represents a class of referring expressions.
    Speakers use more reduced forms for more accessible referents. -/
inductive AccessibilityLevel where
  | fullNameMod          -- "the former governor of Alaska, Sarah Palin"
  | fullName             -- "Sarah Palin"
  | longDefDescription   -- "the former governor of Alaska"
  | shortDefDescription  -- "the governor"
  | lastName             -- "Palin"
  | firstName            -- "Sarah"
  | distalDemMod         -- "that tall woman over there"
  | proxDemMod           -- "this tall woman"
  | distalDemNP          -- "that woman"
  | proxDemNP            -- "this woman"
  | distalDem            -- "that"
  | proxDem              -- "this"
  | stressedPronGesture  -- "SHE" [+pointing]
  | stressedPron         -- "SHE"
  | unstressedPron       -- "she"
  | cliticizedPron       -- "'er", "-la"
  | verbalAgreement      -- person inflection on the verb
  | zero                 -- ∅ (pro-drop)
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Numeric rank: 0 (lowest accessibility) to 17 (highest).
    Higher rank = higher accessibility = more reduced form. -/
def AccessibilityLevel.rank : AccessibilityLevel → Nat
  | .fullNameMod         => 0
  | .fullName            => 1
  | .longDefDescription  => 2
  | .shortDefDescription => 3
  | .lastName            => 4
  | .firstName           => 5
  | .distalDemMod        => 6
  | .proxDemMod          => 7
  | .distalDemNP         => 8
  | .proxDemNP           => 9
  | .distalDem           => 10
  | .proxDem             => 11
  | .stressedPronGesture => 12
  | .stressedPron        => 13
  | .unstressedPron      => 14
  | .cliticizedPron      => 15
  | .verbalAgreement     => 16
  | .zero                => 17

/-- Distinct accessibility levels have distinct ranks. -/
theorem AccessibilityLevel.rank_injective :
    Function.Injective AccessibilityLevel.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [AccessibilityLevel.rank]

/-- Total order on `AccessibilityLevel` via the rank pullback. -/
instance : LinearOrder AccessibilityLevel :=
  LinearOrder.lift' AccessibilityLevel.rank AccessibilityLevel.rank_injective

/-- Coarsening: each accessibility level maps to one of the 5
    `DefinitenessLevel` categories used for differential argument marking.
    This is a many-to-one, **non-monotone** mapping — names are less
    accessible than definite descriptions but more prominent for DOM. -/
def AccessibilityLevel.toDefLevel : AccessibilityLevel → DefinitenessLevel
  | .fullNameMod | .fullName | .lastName | .firstName  => .properName
  | .longDefDescription | .shortDefDescription
  | .distalDemMod | .proxDemMod | .distalDemNP
  | .proxDemNP | .distalDem | .proxDem                 => .definite
  | .stressedPronGesture | .stressedPron | .unstressedPron
  | .cliticizedPron | .verbalAgreement | .zero          => .personalPronoun

-- ════════════════════════════════════════════════════
-- § 2. Referential Form
-- ════════════════════════════════════════════════════

/-- Referential form options for referring to a discourse entity.
    Uses [ariel-2001]'s 18-level accessibility marking scale. -/
abbrev ReferentialForm := AccessibilityLevel

/-- An unstressed pronoun is more reduced than a full name. -/
theorem pronoun_more_reduced_than_name :
    AccessibilityLevel.unstressedPron.rank > AccessibilityLevel.fullName.rank := by
  decide

-- ════════════════════════════════════════════════════
-- § 3. Next-Mention Bias
-- ════════════════════════════════════════════════════

/-- Next-mention bias: how likely a discourse referent is to be
    mentioned again in the subsequent utterance. Driven by thematic
    roles, coherence relations, and discourse structure. -/
inductive NextMentionBias where
  | high     -- referent is expected to be mentioned next
  | low      -- referent is not expected to be mentioned next
  deriving DecidableEq, Repr

/-- Accessibility prediction: high next-mention bias licenses reduced
    referential form (unstressed pronoun); low bias requires full form
    (full name).

    This is the monotone link at the heart of [ariel-2001]'s
    Accessibility Marking Scale: more accessible referents → more
    reduced forms. The same relationship underlies the Probabilistic
    Reduction Hypothesis (more predictable → shorter/more reduced). -/
def NextMentionBias.predictedForm : NextMentionBias → ReferentialForm
  | .high => .unstressedPron
  | .low  => .fullName

/-- The predicted form for high-bias referents is more reduced than
    for low-bias referents. -/
theorem high_bias_more_reduced :
    (NextMentionBias.high.predictedForm).rank >
    (NextMentionBias.low.predictedForm).rank := by
  decide

-- ════════════════════════════════════════════════════
-- § 4. Weight Bridge
-- ════════════════════════════════════════════════════

/-- NP weight correlate: reduced referential forms are lighter.
    Approximate number of words in a typical instance of each form.
    This connects form selection to constituent ordering (heavy NP
    shift, DLM).

    The same choice that makes a referent "more reduced" also makes
    it "lighter", linking [ariel-2001]'s accessibility hierarchy
    to [arnold-wasow-losongco-ginstrom-2000]'s heaviness effects. -/
def ReferentialForm.typicalWeight : ReferentialForm → Nat
  | .fullNameMod                              => 4  -- "the former governor of Alaska, Sarah Palin"
  | .longDefDescription                       => 4  -- "the former governor of Alaska"
  | .distalDemMod | .proxDemMod               => 3  -- "that tall woman over there"
  | .fullName                                 => 2  -- "Sarah Palin"
  | .shortDefDescription                      => 2  -- "the governor"
  | .distalDemNP | .proxDemNP                 => 2  -- "that woman"
  | .lastName | .firstName                    => 1  -- "Palin", "Sarah"
  | .distalDem | .proxDem                     => 1  -- "that", "this"
  | .stressedPronGesture | .stressedPron
  | .unstressedPron | .cliticizedPron         => 1  -- "SHE", "she", "'er"
  | .verbalAgreement                          => 0  -- bound morpheme
  | .zero                                     => 0  -- ∅

/-- Pronouns are at most as heavy as definite descriptions. -/
theorem pronoun_lightest :
    ReferentialForm.typicalWeight .unstressedPron ≤
    ReferentialForm.typicalWeight .shortDefDescription := by
  decide

-- ════════════════════════════════════════════════════
-- § 5. Discourse Elaboration
-- ════════════════════════════════════════════════════

/-- How elaborated a referent's discourse representation is.

    [arnold-2026] §2: the key criterion for underspecified singular
    *they* is "discourse specificity" — whether the speaker intends to
    evoke a detailed mental representation for the addressee.

    This extends [newman-1992]'s "solidity" (existence of a specific
    concrete referent) and [newman-1998]'s "individuation" (referents
    treated as individuals with identity-relevant details).

    The scale runs from `underspecified` (the referent is barely sketched
    in the discourse model — quantified, indefinite, or mentioned only in
    passing) to `elaborated` (the referent has a rich, detailed
    representation — named, described, central to the narrative). -/
inductive DiscourseElaboration where
  /-- The referent's discourse representation is minimal: quantified,
      indefinite, epicene, or not developed. Identity is unknown or
      unimportant. "Everyone should make their bed." -/
  | underspecified
  /-- The referent has a rich, detailed discourse representation:
      named, described, topical, with known personal attributes.
      "Asia Kate Dillon (born November 15, 1984) is an American actor.
      They are known for their roles as…" -/
  | elaborated
  deriving DecidableEq, Repr, BEq

/-- Bridge from Ariel's accessibility scale to discourse elaboration.

    [ariel-2001]'s Accessibility Marking Scale describes which
    referential form is appropriate given how accessible a referent is.
    Arnold's discourse elaboration is related but distinct: low
    accessibility *tends to co-occur with* underspecified elaboration
    (a referent you haven't mentioned much is both less accessible and
    less elaborated), but they are not identical.

    This coarsening maps high-accessibility forms (pronouns, agreement,
    zero) to elaborated (these forms require a well-established referent)
    and low-accessibility forms (full names, descriptions) to underspecified
    (these forms are used when the referent is being newly introduced or
    is not yet established). The boundary is approximate. -/
def AccessibilityLevel.toElaboration (a : AccessibilityLevel) : DiscourseElaboration :=
  if a.rank ≥ 13 then .elaborated    -- stressed pronoun and above
  else .underspecified                -- demonstrations, descriptions, names

/-- Pronouns (high accessibility) correlate with elaborated discourse
    representations — you use a pronoun for a referent that is already
    well-established in the discourse. -/
theorem pronoun_implies_elaborated :
    AccessibilityLevel.unstressedPron.toElaboration = .elaborated := rfl

/-- Full names (low accessibility) correlate with underspecified discourse
    representations — the referent is being (re-)introduced. -/
theorem fullName_implies_underspecified :
    AccessibilityLevel.fullName.toElaboration = .underspecified := rfl

/-- Ariel's GHZ→AccessibilityLevel projection ([ariel-2001]): the
    prototypical accessibility level for each givenness status.

    Caveat: GHZ's lower statuses (`referential` = "indefinite this N",
    `typeIdentifiable` = "a N") are **indefinite**, which do not appear
    on Ariel's accessibility-marking scale (Given/definite forms); the
    mapping for these two is by approximate accessibility degree, not
    by form identity. -/
def GivennessStatus.toAccessibility : GivennessStatus → AccessibilityLevel
  | .inFocus              => .unstressedPron
  | .activated            => .proxDem
  | .familiar             => .distalDemNP
  | .uniquelyIdentifiable => .shortDefDescription
  | .referential          => .longDefDescription
  | .typeIdentifiable     => .fullNameMod

end Features
