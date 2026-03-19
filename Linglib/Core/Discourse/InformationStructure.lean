import Linglib.Core.Lexical.UD
import Linglib.Core.Discourse.AtIssueness
import Linglib.Core.Discourse.CoherenceRelation

/-!
# Core.InformationStructure
@cite{fox-katzir-2011} @cite{rooth-1992} @cite{steedman-2000} @cite{roberts-2012}

Theory-neutral types for Information Structure, alternative semantics,
and discourse status.

## Overview

Information Structure partitions utterances along two orthogonal dimensions:
1. Theme/Rheme (topic/comment): What's being talked about vs. what's said about it
2. Focus/Background: What's contrasted vs. what's given

This module provides descriptive types and basic data structures.
Theory-specific operations (K&S's [FoC]/[G] features, their semantic effects)
live in `Theories/Semantics/Focus/KratzerSelkirk2020.lean`.

-/

namespace Core.InformationStructure

-- ════════════════════════════════════════════════════
-- § Alternative Semantics (@cite{rooth-1992}, @cite{kratzer-selkirk-2020})
-- ════════════════════════════════════════════════════

/-- Two-dimensional meaning in Alternatives Semantics.
    Every expression has an O-value and an A-value.

    @cite{kratzer-selkirk-2020} §3, §8. -/
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

-- Category-Gated Alternatives (@cite{fox-katzir-2011})

/-- A denotation tagged with its UPOS category.
    Pairs a semantic value with a UD part-of-speech tag, enabling
    category-gated alternative computation.

    Fox & Katzir argue that @cite{rooth-1985} type-theoretic
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
    count as alternatives.

    This is strictly more restrictive than Rooth's D_τ computation. -/
def categoryMatchAlts {α : Type} (target : UD.UPOS) (lexicon : List (CatItem α)) : List α :=
  (lexicon.filter (·.cat == target)).map (·.den)

/-- Type-theoretic alternatives: all denotations regardless of category
    (@cite{rooth-1985}/1992 D_τ computation). -/
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
    Descriptive type used across multiple theories (@cite{kratzer-selkirk-2020}, @cite{arnold-wasow-losongco-ginstrom-2000},
    backgrounded islands). -/
inductive DiscourseStatus where
  /-- Contrasted with discourse referent -/
  | focused
  /-- Given, matching discourse referent -/
  | given
  /-- Unmarked: merely new information -/
  | new
  deriving DecidableEq, Repr, BEq

/-- Ordinal rank: given < new < focused.
    Used by extraction-acceptability theories (@cite{lu-degen-2025}) and
    focus-comparison constraints (@cite{winckel-et-al-2025}). -/
def DiscourseStatus.rank : DiscourseStatus → Fin 3
  | .given   => 0
  | .new     => 1
  | .focused => 2

/-- Map gradient at-issueness to discourse status.

    High at-issueness content is foregrounded (new or focused);
    low at-issueness content is backgrounded (given). This connects
    the at-issue/not-at-issue distinction to the Focus/Background partition.

    - At-issue → `.new` (unmarked foreground; `.focused` requires
      additional evidence of contrast)
    - Not-at-issue → `.given` (backgrounded) -/
def DiscourseStatus.ofAtIssueness (d : Core.Discourse.AtIssueness.AtIssuenessDegree)
    (θ : Core.Discourse.AtIssueness.AtIssuenessThreshold :=
      Core.Discourse.AtIssueness.defaultThreshold) : DiscourseStatus :=
  if Core.Discourse.AtIssueness.isAtIssue d θ then .new else .given

/-! ## Polarity-Switch Contexts

@cite{turco-braun-dimroth-2014} distinguish two discourse contexts for polarity
switches (negation → affirmation). The distinction is theory-neutral: it
characterizes the discourse relation between the antecedent and the target
utterance, independent of how languages mark the switch.

- @cite{klein-2008}: contrast = different topic situations, compatible claims
- @cite{umbach-2004}: correction = same topic situation, mutually exclusive claims -/

/-- The discourse context in which a polarity switch (neg → affirm) occurs.
    Crosslinguistically relevant: Dutch and German mark both contexts but with
    different strategies.

    This is the information-structural reflex of the discourse-structural
    distinction between `CoherenceRelation.contrast` and
    `CoherenceRelation.correction` (@cite{umbach-2004} §3). -/
inductive PolaritySwitchContext where
  /-- Different topic situations, compatible claims -/
  | contrast
  /-- Same topic situation, mutually exclusive claims -/
  | correction
  deriving DecidableEq, Repr, BEq

open Core.Discourse.CoherenceRelation in
/-- Bridge from polarity-switch contexts to discourse coherence relations.
    @cite{umbach-2004} §3: the contrast/correction distinction in information
    structure corresponds directly to two distinct resemblance relations
    at the discourse level. -/
def PolaritySwitchContext.toCoherenceRelation : PolaritySwitchContext → CoherenceRelation
  | .contrast   => .contrast
  | .correction => .correction

/-- How a language marks polarity switches (neg → affirm).
    Theory-neutral inventory: individual languages select a subset. -/
inductive PolarityMarkingStrategy where
  /-- Sentence-internal affirmative particle (e.g., Dutch *wel*) -/
  | particle
  /-- Pitch accent on the finite verb (@cite{hohle-1992} Verum focus) -/
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
  /-- Available in contrast contexts -/
  contrastOk : Bool
  /-- Available in correction contexts -/
  correctionOk : Bool
  /-- The polarity-marking strategy category -/
  strategy : PolarityMarkingStrategy
  deriving Repr, DecidableEq, BEq

/-! ## Alternative Set Well-Formedness (@cite{umbach-2004} §2.2)

@cite{umbach-2004} identifies two constraints that jointly determine when
elements can serve as alternatives (in focus, coordination, or discourse):

1. **Semantic independence**: neither alternative entails the other
   (dissimilarity). Explains why *#John had a drink and Mary had a martini*
   is odd — "drink" subsumes "martini".

2. **Common integrator**: a concept subsuming all alternatives (similarity).
   Explains why alternatives must be of a comparable type.

Together these define *comparability* = similarity + dissimilarity, which
is the prerequisite for any type of contrast. -/

/-- Two propositions are semantically independent iff neither entails the other.
    @cite{umbach-2004} §2.2: required for alternatives in focus, coordination,
    and discourse relations. Violation explains the oddness of
    *#John had a drink and Mary had a martini*. -/
def semanticallyIndependent {W : Type} (a b : W → Bool) : Prop :=
  ¬(∀ w : W, a w = true → b w = true) ∧ ¬(∀ w : W, b w = true → a w = true)

/-- A common integrator subsumes all alternatives.
    @cite{umbach-2004} §2.2, following @cite{lang-1984}: coordinated elements
    and focus alternatives must share a common superordinate concept.
    For example, in "beer and martini", "drink" is the common integrator. -/
def commonIntegrator {W : Type} (alts : List (W → Bool)) (integ : W → Bool) : Prop :=
  ∀ a ∈ alts, ∀ w : W, a w = true → integ w = true

/-- A well-formed alternative set satisfies both constraints.
    @cite{umbach-2004} §2.2: alternatives must be comparable, i.e.,
    similar (common integrator) and dissimilar (pairwise independent). -/
def wellFormedAlts {W : Type} (alts : List (W → Bool)) (integ : W → Bool) : Prop :=
  commonIntegrator alts integ ∧
  ∀ a ∈ alts, ∀ b ∈ alts, a ≠ b → semanticallyIndependent a b

/-! ## Exclusion Variety (@cite{umbach-2004} §2.3, §3.2)

@cite{umbach-2004} distinguishes two varieties of exclusion that cross-cut
information structure and discourse structure:

- **Additional**: the excluded alternative would hold *in addition to* the
  asserted item. Instantiated by *only*-phrases (§2.3: "only RONALD went
  shopping" excludes anyone *in addition to* Ronald) and the discourse
  relation CONTRAST (§3.2: "Did John go to Berlin, and *also* to Paris?").
- **Substitution**: the excluded alternative would hold *instead of* the
  asserted item. Instantiated by contrastive focus (§2.3: "RONALD went
  shopping" excludes anyone *instead of* Ronald) and the discourse
  relation CORRECTION (§3.2: German *sondern*).

This distinction explains why contrastive focus and *only*-phrases have
different presuppositions (§2.3), and why CONTRAST and CORRECTION respond
to different implicit questions (§3.2). -/

/-- Two varieties of exclusion that distinguish *only*-phrases from
    contrastive focus, and CONTRAST from CORRECTION.

    @cite{umbach-2004} §2.3: An *only*-phrase excludes the possibility
    that someone *in addition to* the focused item satisfies the predicate.
    A contrastive focus excludes the possibility that someone *instead of*
    the focused item satisfies the predicate. -/
inductive ExclusionVariety where
  /-- Excludes additional alternatives: the excluded item would hold
      *in addition to* the asserted one. *Only*-phrases / CONTRAST. -/
  | additional
  /-- Excludes by substitution: the excluded item would hold
      *instead of* the asserted one. Contrastive focus / CORRECTION. -/
  | substitution
  deriving DecidableEq, Repr, BEq

open Core.Discourse.CoherenceRelation in
/-- Bridge from exclusion variety to discourse coherence relation.
    @cite{umbach-2004} §3.2: the information-structural exclusion type
    determines which discourse relation holds. -/
def ExclusionVariety.toCoherenceRelation : ExclusionVariety → CoherenceRelation
  | .additional    => .contrast
  | .substitution  => .correction

/-! ## Focus Interpretation Principle Applications (@cite{rooth-1992} §2)

Four domains in which focus alternatives interact with context.
Defined here (rather than in `Theories/Semantics/Focus/` or
`Phenomena/Focus/`) because it is a theory-neutral classification
used by both layers. -/

/-- Application type for the Focus Interpretation Principle.
    @cite{rooth-1992} §2 identifies four domains where focus semantic
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

/-! ## Discourse Context

A composite type bundling the dimensions that most commonly co-occur
at discourse analysis sites: the current QUD, the expression's discourse
status, and the coherence relation to prior discourse.

Motivated by co-occurrence analysis: `DiscourseStatus` appears in 5 of 7
multi-import sites across `Phenomena/` and `Theories/`. -/

/-- A discourse-structural context for an expression under analysis.

    Bundles three dimensions:
    - **QUD**: what question is currently at issue (@cite{roberts-2012})
    - **Status**: how foregrounded the expression is (given/new/focused)
    - **Coherence**: how the current unit relates to prior discourse (@cite{kehler-2002})

    The `M` parameter is the meaning type for the QUD partition. -/
structure Core.Discourse.DiscourseContext (M : Type*) where
  /-- The current Question Under Discussion -/
  qud : QUD M
  /-- Discourse status of the current expression -/
  status : Core.InformationStructure.DiscourseStatus
  /-- Coherence relation to the preceding discourse unit, if any -/
  coherence : Option Core.Discourse.CoherenceRelation.CoherenceRelation := none
