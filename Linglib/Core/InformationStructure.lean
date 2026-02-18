/-
# Core.InformationStructure

Abstract interface for Information Structure (theme/rheme, focus/background,
IS features).

## Overview

Information Structure partitions utterances along two orthogonal dimensions:
1. Theme/Rheme (topic/comment): What's being talked about vs. what's said about it
2. Focus/Background: What's contrasted vs. what's given

Kratzer & Selkirk (2020) decompose the traditional [F]-feature into two
privative morphosyntactic features:
- **[FoC]** (FoCus): Introduces alternatives, signals contrast via ~ operator
- **[G]** (Givenness): Presupposes discourse salience, signals match

There is NO feature for newness: apparent prosodic effects of new material
are the result of default prosody.

## References

- Steedman (2000). The Syntactic Process, Chapter 5.
- Rooth (1992). A theory of focus interpretation.
- Kratzer, A. & Selkirk, E. (2020). Deconstructing Information Structure.
- Roberts (1996/2012). Information structure in discourse.
- Beaver & Clark (2008). Sense and Sensitivity.
-/

import Linglib.Core.Alternatives

open Core.Alternatives

namespace Core.InformationStructure

-- Theme and Rheme

/--
Theme: what the utterance is about (the "topic" or "given" part).

The theme:
- Presupposes a QUD (set of alternatives)
- Is often prosodically marked (L+H* LH% in English)
- Corresponds to the λ-abstract in structured meanings

Example: In "FRED ate the beans" (answering "Who ate the beans?"),
the theme is "λx. ate(x, beans)" or informally "_ ate the beans".
-/
structure Theme (P : Type) where
  /-- The thematic content (often a property/λ-abstract) -/
  content : P
  /-- Whether the theme is prosodically marked -/
  marked : Bool := false

/--
Rheme: what's asserted about the theme (the "comment" or "new" part).

The rheme:
- Restricts the QUD alternatives to one
- Is often prosodically marked (H* LL% in English)
- Provides the "answer" to the implicit question

Example: In "FRED ate the beans", the rheme is "Fred".
-/
structure Rheme (P : Type) where
  /-- The rhematic content -/
  content : P
  /-- Whether the rheme is prosodically marked -/
  marked : Bool := true

-- Focus and Background

/--
Focus: the contrasted element(s) within theme or rheme.

Focus is marked by pitch accent and:
- Evokes alternatives (Rooth)
- Associates with focus-sensitive particles (only, even)
- Determines the "question" being answered

Focus is orthogonal to theme/rheme: both can contain focused elements.
-/
structure Focus (α : Type) where
  /-- The focused element -/
  focused : α
  /-- Alternatives evoked by focus -/
  alternatives : Alternatives α

/--
Background: the non-focused, given material.

Background material is:
- Not pitch-accented
- Presupposed to be salient in context
- Often recoverable/predictable
-/
structure Background (α : Type) where
  /-- The background elements -/
  elements : List α

-- Information Structure Partition

/--
A complete Information Structure analysis of an utterance.

Partitions the utterance into:
- Theme vs. Rheme (what's talked about vs. what's said)
- Focus vs. Background (within each)
-/
structure InfoStructure (P : Type) where
  /-- The theme (topic, λ-abstract, presupposed QUD) -/
  theme : Theme P
  /-- The rheme (comment, answer, assertion) -/
  rheme : Rheme P
  /-- Focused elements (evoking alternatives) -/
  foci : List P := []
  /-- Background elements (given) -/
  background : List P := []

-- Information Structure Interface (Typeclass)

/--
Typeclass for theories that provide Information Structure.

Implementations:
- CCG/Intonation: prosodic realization
- (Future) Syntactic approaches, discourse models

The key insight: different surface forms (derivations, prosody) can
map to the same propositional content but different Information Structures.
-/
class HasInfoStructure (D : Type) (P : Type) where
  /-- Extract Information Structure from a derivation/form -/
  infoStructure : D → InfoStructure P

/-! ## IS Features (Kratzer & Selkirk 2020) -/

/-- The two privative morphosyntactic features of K&S 2020.

[FoC] and [G] are genuinely syntactic features: crosslinguistically they
trigger displacement, agreement, and ellipsis (§2). They happen to be
spelled out prosodically in Standard American and British English, but
this is not their defining property. -/
inductive ISFeature where
  /-- FoCus: introduces alternatives, signals contrast.
      Resembles [wh] — comes with obligatory ~ operator. -/
  | FoC
  /-- Givenness: presupposes discourse salience, signals match.
      Contributes meaning directly (no operator needed). -/
  | G
  deriving DecidableEq, Repr, BEq

/-- The three-way partition of discourse status in K&S.
    Note: only [FoC] and [G] are features; new is the unmarked default. -/
inductive DiscourseStatus where
  /-- [FoC]-marked: contrasted with discourse referent -/
  | focused
  /-- [G]-marked: Given, matching discourse referent -/
  | given
  /-- Unmarked: merely new information (no feature) -/
  | new
  deriving DecidableEq, Repr, BEq

/-- Newness is NOT a grammatical feature.
    New material is simply unmarked — no [FoC], no [G]. -/
def isNew (hasFoC : Bool) (hasG : Bool) : Bool :=
  !hasFoC && !hasG

/-! ## §8 (45). The Contribution of [FoC]

[FoC] does NOT change the O-value. Its A-value is the full domain D_τ
(all possible entities of the relevant semantic type). This is standard
Roothian focus semantics.

  ⟦[α]_{FoC}⟧_{O,C} = ⟦α⟧_{O,C}
  ⟦[α]_{FoC}⟧_{A,C} = D_τ
-/

/-- Apply [FoC] to a meaning: O-value unchanged, A-value becomes full domain.
    K&S (45): The A-value of [α]_{FoC} is D_τ. -/
def applyFoC {α : Type} (m : AltMeaning α) (domain : List α) : AltMeaning α :=
  { oValue := m.oValue, aValue := domain }

/-- [FoC] preserves O-value. K&S (45) first clause. -/
theorem foc_preserves_oValue {α : Type} (m : AltMeaning α) (domain : List α) :
    (applyFoC m domain).oValue = m.oValue := rfl

/-! ## §8 (46-47). The Contribution of [G]

[G] introduces a Givenness requirement: the expression must match a salient
discourse referent. Technically:

  ⟦[α]_{G_a}⟧_{O,C} is defined iff a is a discourse referent in C,
    and α is Given with respect to a.
  If defined, ⟦[α]_{G_a}⟧_{O,C} = ⟦α⟧_{O,C}
  ⟦[α]_{G_a}⟧_{A,C} = ⟦α⟧_{A,C}

[G] contributes purely use-conditional / expressive meaning (like discourse
particles German "ja", "doch"). It places a condition on the discourse context,
not on truth conditions.
-/

/-- An expression α is Given with respect to discourse referent a iff
    its A-value is {a} (a singleton containing just the referent).

    K&S (46): α is Given w.r.t. a in C iff ⟦α⟧_{A,C} = {a}.

    Intuitively: the alternatives set has collapsed to a single salient entity,
    meaning there's nothing to contrast — the content is already "in the air". -/
def isGiven {α : Type} [BEq α] (aValue : List α) (referent : α) : Bool :=
  match aValue with
  | [a] => a == referent
  | _ => false

/-- Apply [G] to a meaning: both values unchanged, but adds a definedness
    condition (the expression must be Given w.r.t. some discourse referent).

    Unlike [FoC], [G] does NOT change the A-value. Its contribution is
    purely a presupposition on the discourse context. -/
def applyG {α : Type} (m : AltMeaning α) : AltMeaning α := m

/-- [G] preserves O-value. K&S (47): if defined, O-value unchanged. -/
theorem g_preserves_oValue {α : Type} (m : AltMeaning α) :
    (applyG m).oValue = m.oValue := rfl

/-- [G] preserves A-value. K&S (47): A-value unchanged. -/
theorem g_preserves_aValue {α : Type} (m : AltMeaning α) :
    (applyG m).aValue = m.aValue := rfl

/-! ## §8 (58). [FoC] and [G] are Mutually Exclusive

A single constituent CANNOT bear both [FoC] and [G]. The proof follows from
the A-value conditions:
- [FoC] requires A-value = D_τ (the full domain, maximally large)
- [G] requires A-value = {a} (a singleton)
No semantic domain is both maximal and a singleton (assuming |D_τ| > 1). -/

/-- [FoC] and [G] are mutually exclusive: no constituent can satisfy both
    the [FoC] A-value condition (full domain) and the [G] A-value condition
    (singleton) simultaneously, when the domain has more than one element.

    K&S (58, first part): follows from the incompatibility of A-value conditions. -/
theorem foc_g_exclusion {α : Type} [BEq α] (domain : List α) (referent : α)
    (h_domain : domain.length > 1) :
    ¬(isGiven domain referent = true) := by
  simp only [isGiven]
  match domain, h_domain with
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _, _ => simp

/-! ## Polarity-Switch Contexts

Turco, Braun & Dimroth (2014) distinguish two discourse contexts for polarity
switches (negation → affirmation). The distinction is theory-neutral: it
characterizes the discourse relation between the antecedent and the target
utterance, independent of how languages mark the switch.

- Klein (2008): contrast = different topic situations, compatible claims
- Umbach (2004): correction = same topic situation, mutually exclusive claims -/

/-- The discourse context in which a polarity switch (neg → affirm) occurs.
    Crosslinguistically relevant: Dutch and German mark both contexts but with
    different strategies (Turco, Braun & Dimroth 2014). -/
inductive PolaritySwitchContext where
  /-- Different topic situations, compatible claims (Klein 2008) -/
  | contrast
  /-- Same topic situation, mutually exclusive claims (Umbach 2004) -/
  | correction
  deriving DecidableEq, Repr, BEq

/-- How a language marks polarity switches (neg → affirm).
    Theory-neutral inventory: individual languages select a subset. -/
inductive PolarityMarkingStrategy where
  /-- Sentence-internal affirmative particle (e.g., Dutch *wel*) -/
  | particle
  /-- Pitch accent on the finite verb (Höhle 1992 Verum focus) -/
  | verumFocus
  /-- Other strategy (e.g., pre-utterance particle, intonation pattern) -/
  | other
  /-- No overt polarity marking -/
  | unmarked
  deriving DecidableEq, Repr, BEq

/-- A cross-linguistic polarity-marking entry.

    Unified structure for all strategies — particles (Dutch *wel*),
    prosodic (German VF), or other. Language-specific Fragment files
    instantiate this with appropriate optional fields. -/
structure PolarityMarkingEntry where
  /-- Descriptive label (e.g., "wel", "Verum focus", "doch (pre-utterance)") -/
  label : String
  /-- Surface form, if the strategy is a particle -/
  form : Option String := none
  /-- What bears prosodic prominence, if the strategy is prosodic -/
  prosodicTarget : Option String := none
  /-- Whether the marker appears sentence-internally (vs. pre-utterance) -/
  sentenceInternal : Bool
  /-- Available in contrast contexts (Klein 2008) -/
  contrastOk : Bool
  /-- Available in correction contexts (Umbach 2004) -/
  correctionOk : Bool
  /-- The polarity-marking strategy category -/
  strategy : PolarityMarkingStrategy
  deriving Repr, DecidableEq, BEq

/-! ## Focus Interpretation Principle Applications (Rooth 1992 §2)

Four domains in which focus alternatives interact with context.
Defined here (rather than in `Theories/Semantics/Focus/` or
`Phenomena/Focus/`) because it is a theory-neutral classification
used by both layers. -/

/-- Application type for the Focus Interpretation Principle.
    Rooth (1992) §2 identifies four domains where focus semantic
    values constrain interpretation. -/
inductive FIPApplication where
  /-- Focusing adverbs: only, even, also -/
  | focusingAdverb
  /-- Contrast/parallelism in discourse -/
  | contrast
  /-- Scalar implicature computation -/
  | scalarImplicature
  /-- Question-answer congruence -/
  | qaCongruence
  deriving DecidableEq, Repr, BEq

end Core.InformationStructure
