import Linglib.Core.Discourse.AtIssueness
import Linglib.Core.Discourse.Coherence

/-!
# Features.InformationStructure

@cite{rooth-1992} @cite{steedman-2000} @cite{kuroda-1972}
@cite{umbach-2004} @cite{turco-braun-dimroth-2014}

Theory-neutral substance taxonomies for Information Structure: theme/
rheme partitions, focus/background, discourse status, polarity-switch
contexts, focus-marking strategies, exclusion variety, judgment type.

Theory-level predicates over these taxonomies (Umbach's alt-set
well-formedness, Erteschik-Shir/Abeillé extraction-IS clash) live in
`Theories/Semantics/Focus/Comparability.lean`. Focus-specific compositional
operations (`AltMeaning`, `CatItem`, `typeTheoAlts`) live in
`Theories/Semantics/Alternatives/`.
-/

namespace Features.InformationStructure

-- Theme and Rheme

/-- Theme: what the utterance is about (the "topic" or "given" part).

    The theme:
    - Presupposes a QUD (set of alternatives)
    - Is often prosodically marked (L+H* LH% in English)
    - Corresponds to the λ-abstract in structured meanings

    Example: in "FRED ate the beans" (answering "Who ate the beans?"),
    the theme is "λx. ate(x, beans)" or informally "_ ate the beans". -/
structure Theme (P : Type) where
  /-- The thematic content (often a property/λ-abstract) -/
  content : P
  /-- Whether the theme is prosodically marked -/
  marked : Bool := false

/-- Rheme: what's asserted about the theme (the "comment" or "new" part).

    The rheme:
    - Restricts the QUD alternatives to one
    - Is often prosodically marked (H* LL% in English)
    - Provides the "answer" to the implicit question

    Example: in "FRED ate the beans", the rheme is "Fred". -/
structure Rheme (P : Type) where
  /-- The rhematic content -/
  content : P
  /-- Whether the rheme is prosodically marked -/
  marked : Bool := true

-- Focus and Background

/-- Focus: the contrasted element(s) within theme or rheme.

    Focus is marked by pitch accent and:
    - Evokes alternatives (Rooth)
    - Associates with focus-sensitive particles (only, even)
    - Determines the "question" being answered

    Focus is orthogonal to theme/rheme: both can contain focused elements. -/
structure Focus (α : Type) where
  /-- The focused element -/
  focused : α
  /-- Alternatives evoked by focus (including the focused element) -/
  alternatives : List α

/-- Background: the non-focused, given material.

    Background material is:
    - Not pitch-accented
    - Presupposed to be salient in context
    - Often recoverable/predictable -/
structure Background (α : Type) where
  /-- The background elements -/
  elements : List α

-- Information Structure Partition

/-- A complete Information Structure analysis of an utterance.

    Partitions the utterance into:
    - Theme vs. Rheme (what's talked about vs. what's said)
    - Focus vs. Background (within each) -/
structure InfoStructure (P : Type) where
  /-- The theme (topic, λ-abstract, presupposed QUD) -/
  theme : Theme P
  /-- The rheme (comment, answer, assertion) -/
  rheme : Rheme P
  /-- Focused elements (evoking alternatives) -/
  foci : List P := []
  /-- Background elements (given) -/
  background : List P := []

-- Information Structure Interface (typeclass)

/-- Typeclass for theories that provide Information Structure.

    Implementations:
    - CCG/Intonation: prosodic realization
    - (Future) Syntactic approaches, discourse models

    The key insight: different surface forms (derivations, prosody) can
    map to the same propositional content but different Information
    Structures. -/
class HasInfoStructure (D : Type) (P : Type) where
  /-- Extract Information Structure from a derivation/form -/
  infoStructure : D → InfoStructure P

-- Discourse Status

/-- The three-way partition of discourse status.

    Descriptive type used across multiple theories
    (@cite{kratzer-selkirk-2020}, @cite{arnold-wasow-losongco-ginstrom-2000},
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

-- Polarity-Switch Contexts

/-! @cite{turco-braun-dimroth-2014} distinguish two discourse contexts for
    polarity switches (negation → affirmation). The distinction is
    theory-neutral: it characterizes the discourse relation between the
    antecedent and the target utterance, independent of how languages mark
    the switch.

    - @cite{klein-2008}: contrast = different topic situations, compatible claims
    - @cite{umbach-2004}: correction = same topic situation, mutually exclusive claims -/

/-- The discourse context in which a polarity switch (neg → affirm) occurs.

    Crosslinguistically relevant: Dutch and German mark both contexts but
    with different strategies. The information-structural reflex of the
    discourse-structural distinction between `CoherenceRelation.contrast`
    and `CoherenceRelation.correction` (@cite{umbach-2004} §3). -/
inductive PolaritySwitchContext where
  /-- Different topic situations, compatible claims -/
  | contrast
  /-- Same topic situation, mutually exclusive claims -/
  | correction
  deriving DecidableEq, Repr

open Core.Discourse.Coherence in
/-- Bridge from polarity-switch contexts to discourse coherence relations.

    @cite{umbach-2004} §3: the contrast/correction distinction in
    information structure corresponds directly to two distinct resemblance
    relations at the discourse level. -/
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

-- Exclusion Variety

/-! @cite{umbach-2004} §2.3, §3.2 distinguishes two varieties of exclusion
    that cross-cut information structure and discourse structure:

    - **Additional**: the excluded alternative would hold *in addition to*
      the asserted item. Instantiated by *only*-phrases and the discourse
      relation CONTRAST.
    - **Substitution**: the excluded alternative would hold *instead of*
      the asserted item. Instantiated by contrastive focus and the
      discourse relation CORRECTION (German *sondern*).

    This distinction explains why contrastive focus and *only*-phrases have
    different presuppositions, and why CONTRAST and CORRECTION respond to
    different implicit questions. -/

/-- Two varieties of exclusion that distinguish *only*-phrases from
    contrastive focus, and CONTRAST from CORRECTION (@cite{umbach-2004}). -/
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

-- Focus Interpretation Principle (Rooth 1992)

/-- Application type for the Focus Interpretation Principle (@cite{rooth-1992}
    §2 identifies four domains where focus semantic values constrain
    interpretation). -/
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

-- Categorical vs Thetic Judgment (Kuroda 1972)

/-! @cite{kuroda-1972} distinguishes two types of judgment that correspond
    to different information structures:

    - **Categorical** judgment: a subject-predicate structure where the
      subject (ψ-subject) is the topic of predication, yielding a
      Theme + Rheme partition.
    - **Thetic** judgment: presents an event or situation as a whole,
      without a subject of predication, yielding an all-Rheme (no Theme)
      structure.

    Cross-linguistically attested in Japanese (wa/ga), Romance (subject
    inversion), and Mayan (ψ-subject constructions,
    @cite{aissen-polian-2025}). -/

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

end Features.InformationStructure
