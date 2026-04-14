import Linglib.Core.Prominence

/-!
# Referential Form in Production
@cite{ariel-2001} @cite{arnold-wasow-losongco-ginstrom-2000}

Speakers choose between reduced (pronoun) and full (name, description) forms
when referring to discourse entities. This choice is governed by the
**accessibility** of the referent: more accessible/predictable referents
license more reduced forms (@cite{ariel-2001}).

## The Accessibility Marking Scale

The canonical referential form type is `AccessibilityLevel`, @cite{ariel-2001}'s
18-level ordering from least accessible (full name + modifier) to most
accessible (zero/pro-drop). This replaces the earlier conflation with
`DefinitenessLevel` — the accessibility and definiteness scales are
**non-monotonically** related (names are less accessible than definite
descriptions but more prominent for DOM), so they must be separate types.
A coarsening function `toDefLevel` bridges to the DOM/DSM scale when needed.

This module provides the link between accessibility/predictability and
referential form, connecting `Phenomena/Reference/` (form choice) to
`Phenomena/WordOrder/` (position choice) via the shared dimension of
NP weight/reduction.
-/

set_option autoImplicit false

namespace Core.Discourse.ReferentialForm

open Core.Prominence

-- ════════════════════════════════════════════════════
-- § 1. Accessibility Marking Scale
-- ════════════════════════════════════════════════════

/-- @cite{ariel-2001}'s Accessibility Marking Scale: a fine-grained ordering
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
  deriving DecidableEq, Repr

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
    Uses @cite{ariel-2001}'s 18-level accessibility marking scale. -/
abbrev ReferentialForm := AccessibilityLevel

/-- An unstressed pronoun is more reduced than a full name. -/
theorem pronoun_more_reduced_than_name :
    AccessibilityLevel.unstressedPron.rank > AccessibilityLevel.fullName.rank := by
  native_decide

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

    This is the monotone link at the heart of @cite{ariel-2001}'s
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
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. Weight Bridge
-- ════════════════════════════════════════════════════

/-- NP weight correlate: reduced referential forms are lighter.
    Approximate number of words in a typical instance of each form.
    This connects form selection to constituent ordering (heavy NP
    shift, DLM).

    The same choice that makes a referent "more reduced" also makes
    it "lighter", linking @cite{ariel-2001}'s accessibility hierarchy
    to @cite{arnold-wasow-losongco-ginstrom-2000}'s heaviness effects. -/
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
  native_decide

-- ════════════════════════════════════════════════════
-- § 5. Discourse Elaboration
-- ════════════════════════════════════════════════════

/-- How elaborated a referent's discourse representation is.

    @cite{arnold-2026} §2: the key criterion for underspecified singular
    *they* is "discourse specificity" — whether the speaker intends to
    evoke a detailed mental representation for the addressee.

    This extends @cite{newman-1992}'s "solidity" (existence of a specific
    concrete referent) and @cite{newman-1998}'s "individuation" (referents
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

    @cite{ariel-2001}'s Accessibility Marking Scale describes which
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

end Core.Discourse.ReferentialForm
