import Linglib.Core.Lexical.UD
import Linglib.Core.Discourse.AtIssueness
import Linglib.Core.Discourse.Coherence

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

/-! ## Migrated content

The Rooth/K&S `AltMeaning` structure now lives in
`Theories/Semantics/Alternatives/AltMeaning.lean`; the @cite{fox-katzir-2011}
`CatItem` / `typeTheoAlts` / `categoryMatchAlts` machinery now lives in
`Theories/Semantics/Alternatives/Categorical.lean`. Consumers should
import those modules directly. -/

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
  deriving DecidableEq, Repr

/-- Ordinal rank: given < new < focused.
    Used by extraction-acceptability theories (@cite{lu-pan-degen-2025}) and
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
  deriving DecidableEq, Repr

open Core.Discourse.Coherence in
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
  /-- Polarity-reversing particle: affirms [+Pol] while contradicting a
      negative context (e.g., German *doch*, Swedish *jo*, French *si*;
      @cite{holmberg-2016}) -/
  | polarityReversal
  /-- Other strategy (e.g., pre-utterance particle, intonation pattern) -/
  | other
  /-- No overt polarity marking -/
  | unmarked
  deriving DecidableEq, Repr

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
  deriving Repr, DecidableEq

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
  deriving DecidableEq, Repr

open Core.Discourse.Coherence in
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
  deriving DecidableEq, Repr

/-! ## Extraction and Information-Structural Clash
@cite{erteschik-shir-1973} @cite{abeille-et-al-2020}

Wh-extraction foregrounds ([FoC]) the moved element. Extracting from a
backgrounded ([G]) domain creates an information-structural clash: the
element is supposed to address the QUD (as [FoC]) but belongs to a
dimension the QUD ignores (as [G]).

This is the constraint underlying both @cite{erteschik-shir-1973}'s
Dominance Condition on Extraction and @cite{abeille-et-al-2020}'s Focus
Background Constraint (FBC): "a focused element should not be part of
a backgrounded constituent." -/

/-- **Information-structural extraction clash** (@cite{erteschik-shir-1973},
@cite{abeille-et-al-2020}): a focused filler extracted from a backgrounded
domain creates an incompatibility between the filler's discourse function
(addressing the QUD) and the domain's discourse status (QUD-invisible).

Both parameters are free, enabling use in:
- MoS islands: `extractionISClash .focused domainStatus` (filler always focused)
- Subject islands: `extractionISClash (fillerIS c) (subjectIS c)` (filler varies by construction)
- General FBC: `extractionISClash extractedStatus governorStatus` -/
def extractionISClash (fillerStatus domainStatus : DiscourseStatus) : Prop :=
  fillerStatus = .focused ∧ domainStatus = .given

instance (fillerStatus domainStatus : DiscourseStatus) :
    Decidable (extractionISClash fillerStatus domainStatus) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Extraction of a focused element from a backgrounded domain clashes. -/
theorem extractionISClash_focused_given :
    extractionISClash .focused .given := ⟨rfl, rfl⟩

/-- Extraction from an at-issue domain does not clash. -/
theorem extractionISClash_focused_new :
    ¬ extractionISClash .focused .new := by decide

/-- Non-focused extraction from a backgrounded domain does not clash
(e.g., relative clause heads, topics). -/
theorem extractionISClash_given_given :
    ¬ extractionISClash .given .given := by decide

/-! ## Categorical vs Thetic Judgment (@cite{kuroda-1972})

@cite{kuroda-1972} distinguishes two types of judgment that correspond to
different information structures:

- **Categorical** judgment: a subject-predicate structure where the subject
  (ψ-subject) is the topic of predication, yielding a Theme + Rheme partition.
- **Thetic** judgment: presents an event or situation as a whole, without
  a subject of predication, yielding an all-Rheme (no Theme) structure.

Cross-linguistically attested in Japanese (wa/ga), Romance (subject
inversion), and Mayan (ψ-subject constructions, @cite{aissen-polian-2025}). -/

/-- Judgment type following @cite{kuroda-1972}.
    Categorical judgments have a subject of predication (ψ-subject);
    thetic judgments present an event without one. -/
inductive JudgmentType where
  | categorical  -- subject-predicate; ψ-subject is Topic
  | thetic       -- event-presenting; no subject of predication
  deriving DecidableEq, Repr

/-- Does this judgment type place a subject of predication (ψ-subject)
    in a dedicated syntactic position (e.g., Spec,TP)? -/
def JudgmentType.HasψSubject (j : JudgmentType) : Prop :=
  j = .categorical

instance : DecidablePred JudgmentType.HasψSubject :=
  fun _ => inferInstanceAs (Decidable (_ = _))

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
  coherence : Option Core.Discourse.Coherence.CoherenceRelation := none
