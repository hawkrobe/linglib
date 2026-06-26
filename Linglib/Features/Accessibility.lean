import Linglib.Features.Givenness
import Linglib.Features.Prominence
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

`AccessibilityLevel` is a fine-grained (18-tier) reconstruction of
[ariel-2001]'s Accessibility Marking Scale, from least accessible (full
name + modifier) to most accessible (zero / pro-drop). The relative
order of the tiers follows Ariel; the `verbalAgreement` / `zero` split
at the top refines Ariel's single "Extremely High Accessibility Markers"
category. This replaces the earlier conflation with `DefinitenessLevel`
— the scales are **non-monotonically** related (full names are less
accessible than definite descriptions, yet first/last names are more
accessible, so the name band straddles the description band; names are
also more prominent for DOM), so they must be separate types. A
coarsening function `toDefLevel` bridges to the DOM/DSM scale when needed.

## Layer position

`Features/`. Sibling of `Features/Givenness.lean` (the GHZ-6
hierarchy). Both are per-entry feature taxonomies for cognitive
status: `AccessibilityLevel` classifies *forms* by their
accessibility-marking behavior; `GivennessStatus` classifies *entities*
by cognitive status. Ariel argues `AccessibilityLevel`'s tiers are
better empirically supported than GHZ-6's 6 tiers; both retained as
substrate because they serve different consumer profiles. The
`GivennessStatus.toAccessibility` projection (defined below) bridges them.

This module connects referential form choice to word-order position
choice via the shared dimension of NP weight/reduction.
-/

set_option autoImplicit false

namespace Features

open Features.Prominence (DefinitenessLevel)

/-! ### Accessibility marking scale -/

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

/-! ### Referential form -/

/-- Referential form options for referring to a discourse entity.
    Uses [ariel-2001]'s 18-level accessibility marking scale. -/
abbrev ReferentialForm := AccessibilityLevel

/-- An unstressed pronoun is more reduced than a full name. -/
theorem pronoun_more_reduced_than_name :
    AccessibilityLevel.unstressedPron.rank > AccessibilityLevel.fullName.rank := by
  decide

/-! ### Next-mention bias -/

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

/-! ### Weight bridge -/

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

/-! ### Givenness projection -/

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
