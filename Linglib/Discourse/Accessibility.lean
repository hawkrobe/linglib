import Linglib.Features.Givenness
import Mathlib.Tactic.DeriveFintype

/-!
# Accessibility — Ariel's referential-form scale

`AccessibilityLevel`: the 18-tier Accessibility Marking Scale of [ariel-1990],
reproduced in [ariel-2001]'s overview (least accessible `fullNameMod` to most
accessible `zero`), with `rank` (and the `LinearOrder` it induces) and the
three form-function criteria (`informativity`, `rigidity`, `attenuation`).

Sibling of `Features/Givenness.lean` (GHZ-6): this classifies *forms*,
`GivennessStatus` classifies *entities*. Also here: `NextMentionBias`.
-/

namespace Discourse

/-! ### Accessibility marking scale -/

/-- The Accessibility Marking Scale of [ariel-1990], as printed in
    [ariel-2001]: classes of referring expressions ordered from least to
    most accessible. Speakers use more reduced forms for more accessible
    referents. -/
inductive AccessibilityLevel where
  /-- "the former governor of Alaska, Sarah Palin" -/
  | fullNameMod
  /-- "Sarah Palin" -/
  | fullName
  /-- "the former governor of Alaska" -/
  | longDefDescription
  /-- "the governor" -/
  | shortDefDescription
  /-- "Palin" -/
  | lastName
  /-- "Sarah" -/
  | firstName
  /-- "that tall woman over there" -/
  | distalDemMod
  /-- "this tall woman" -/
  | proxDemMod
  /-- "that woman" -/
  | distalDemNP
  /-- "this woman" -/
  | proxDemNP
  /-- "that" -/
  | distalDem
  /-- "this" -/
  | proxDem
  /-- "SHE" with a pointing gesture -/
  | stressedPronGesture
  /-- "SHE" -/
  | stressedPron
  /-- "she" -/
  | unstressedPron
  /-- "'er", "-la" -/
  | cliticizedPron
  /-- person inflection on the verb -/
  | verbalAgreement
  /-- ∅ (pro-drop) -/
  | zero
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

/-- `fullNameMod < ⋯ < zero` (ordered by accessibility rank). -/
instance : LinearOrder AccessibilityLevel :=
  LinearOrder.lift' AccessibilityLevel.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [AccessibilityLevel.rank])

/-! ### Form-function criteria -/

/-- Informativity: approximate lexical content, encoded as an ordinal
    ranking (0–4). Anti-correlated with accessibility (more informative
    → lower rank). Values are illustrative, encoding the relative ordering
    described in [ariel-2001], not exact content-word counts. -/
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
    accessibility. Proper names are rigid designators; definite
    descriptions are descriptive but context-dependent; pronouns and
    zeros carry only person/number/gender features and are maximally
    non-rigid. -/
def AccessibilityLevel.rigidity : AccessibilityLevel → Nat
  | .fullNameMod | .fullName | .lastName | .firstName  => 2
  | .longDefDescription | .shortDefDescription
  | .distalDemMod | .proxDemMod
  | .distalDemNP | .proxDemNP                          => 1
  | .distalDem | .proxDem
  | .stressedPronGesture | .stressedPron | .unstressedPron
  | .cliticizedPron | .verbalAgreement | .zero          => 0

/-- Attenuation: degree of phonological reduction, positively correlated
    with accessibility (0 = full, 5 = zero). Cliticized pronouns are
    shortened free pronouns; verbal agreement inflections are bound
    morphemes, more reduced still; zero has no phonological material
    ([ariel-2001]). -/
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

/-! ### Next-mention bias -/

/-- Next-mention bias: how likely a discourse referent is to be
    mentioned again in the subsequent utterance. Driven by thematic
    roles, coherence relations, and discourse structure. -/
inductive NextMentionBias where
  /-- Referent is expected to be mentioned next. -/
  | high
  /-- Referent is not expected to be mentioned next. -/
  | low
  deriving DecidableEq, Repr

/-- Prototype form choice for a next-mention bias: high bias → unstressed
    pronoun; low bias → full name.

    This encodes the expectancy hypothesis — next-mention predictability
    drives form reduction — which [rosa-arnold-2017] defends and
    [kehler-rohde-2013] rejects (production there tracks topichood, with
    next-mention probability affecting interpretation only). -/
def NextMentionBias.predictedForm : NextMentionBias → AccessibilityLevel
  | .high => .unstressedPron
  | .low  => .fullName

end Discourse
