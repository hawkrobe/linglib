import Linglib.Core.UD

/-!
# Core.InformationStructure

Theory-neutral types for Information Structure, alternative semantics,
and discourse status.

## Overview

Information Structure partitions utterances along two orthogonal dimensions:
1. Theme/Rheme (topic/comment): What's being talked about vs. what's said about it
2. Focus/Background: What's contrasted vs. what's given

This module provides descriptive types and basic data structures.
Theory-specific operations (K&S's [FoC]/[G] features, their semantic effects)
live in `Theories/Semantics/Focus/KratzerSelkirk2020.lean`.

## References

- Steedman (2000). The Syntactic Process, Chapter 5.
- Rooth (1992). A theory of focus interpretation.
- Fox, D. & Katzir, R. (2011). On the characterization of alternatives.
- Roberts (1996/2012). Information structure in discourse.
-/

namespace Core.InformationStructure

-- ════════════════════════════════════════════════════
-- § Alternative Semantics (Rooth 1992, Kratzer & Selkirk 2020)
-- ════════════════════════════════════════════════════

/-- Two-dimensional meaning in Alternatives Semantics.
    Every expression has an O-value and an A-value.

    Kratzer & Selkirk (2020) §3, §8. -/
structure AltMeaning (α : Type) where
  /-- O(rdinary)-value: the actual denotation -/
  oValue : α
  /-- A(lternatives)-value: the set of alternatives (including oValue) -/
  aValue : List α

/-- The O-value of a non-featured expression equals its ordinary denotation.
    The A-value of a non-featured expression is a singleton containing
    its O-value (no alternatives evoked). -/
def AltMeaning.unfeatured {α : Type} (x : α) : AltMeaning α :=
  { oValue := x, aValue := [x] }

-- Category-Gated Alternatives (Fox & Katzir 2011)

/-- A denotation tagged with its UPOS category.
    Pairs a semantic value with a UD part-of-speech tag, enabling
    category-gated alternative computation (Fox & Katzir 2011).

    Fox & Katzir argue that Rooth's (1985/1992) type-theoretic
    alternative computation (D_τ) over-generates: any expression of the
    same semantic type counts as an alternative. Category match restricts
    alternatives to expressions sharing the same UPOS tag. -/
structure CatItem (α : Type) where
  /-- The UPOS category of this lexical item -/
  cat : UD.UPOS
  /-- The semantic denotation -/
  den : α
  deriving Repr

/-- Category-match alternatives: only denotations with the same UPOS tag
    count as alternatives (Fox & Katzir 2011).

    This is strictly more restrictive than Rooth's D_τ computation. -/
def categoryMatchAlts {α : Type} (target : UD.UPOS) (lexicon : List (CatItem α)) : List α :=
  (lexicon.filter (·.cat == target)).map (·.den)

/-- Type-theoretic alternatives: all denotations regardless of category
    (Rooth 1985/1992 D_τ computation). -/
def typeTheoAlts {α : Type} (lexicon : List (CatItem α)) : List α :=
  lexicon.map (·.den)

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
  /-- Alternatives evoked by focus (including the focused element) -/
  alternatives : List α

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

/-- The three-way partition of discourse status.
    Descriptive type used across multiple theories (K&S 2020, Arnold et al. 2000,
    backgrounded islands). -/
inductive DiscourseStatus where
  /-- Contrasted with discourse referent -/
  | focused
  /-- Given, matching discourse referent -/
  | given
  /-- Unmarked: merely new information -/
  | new
  deriving DecidableEq, Repr, BEq

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
