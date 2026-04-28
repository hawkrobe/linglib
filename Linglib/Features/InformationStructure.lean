import Linglib.Core.Discourse.AtIssueness
import Linglib.Typology.Profile
import Mathlib.Tactic.DeriveFintype

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
operations (`AltMeaning`) live in `Theories/Semantics/Alternatives/`.
-/

namespace Features.InformationStructure

-- Theme and Rheme

/-- Theme: what the utterance is about (the "topic" or "given" part).

    The theme:
    - Presupposes a QUD (set of alternatives)
    - Is often prosodically marked (L+H* LH% in English per
      @cite{pierrehumbert-hirschberg-1990}; attributed by
      @cite{steedman-2000} to the Theme tune)
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
    - Is often prosodically marked (H* LL% in English per
      @cite{pierrehumbert-hirschberg-1990})
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
    - Evokes alternatives (@cite{rooth-1992} alternative semantics — note
      that Schwarzschild 1999, Wagner 2012 contest the alt-set primitive;
      the field `alternatives : List α` here commits to the Roothian view)
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
    - Focus vs. Background (within each)

    Note: `foci : List P` and `background : List P` are flat lists of
    `P`-values, not `List (Focus P)` / `List (Background P)`. The
    `Focus`/`Background` structs are reusable pieces for theories that
    want to bundle alternatives explicitly, but `InfoStructure`'s own
    fields use the underlying `P` type. -/
structure InfoStructure (P : Type) where
  /-- The theme (topic, λ-abstract, presupposed QUD) -/
  theme : Theme P
  /-- The rheme (comment, answer, assertion) -/
  rheme : Rheme P
  /-- Focused elements (evoking alternatives) -/
  foci : List P := []
  /-- Background elements (given) -/
  background : List P := []

-- Note: a `class HasInfoStructure (D P : Type) where infoStructure : D
-- → InfoStructure P` typeclass was deleted in the 0.230.489 cleanup.
-- It had 2 instances (Rooth1992 + CCG/Intonation) and 0 polymorphic
-- consumers (no `[HasInfoStructure D P]`-parameterized declarations
-- anywhere); both call sites were inside Rooth1992.lean testing its
-- own instance. Per mathlib discipline (single-method classes with
-- no laws are anti-pattern when no caller dispatches on them) the
-- typeclass was replaced with regular `def`s exposed by each consumer.

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

/-- How a language marks polarity switches (neg → affirm).

    **Framework alignment.** This taxonomy treats polarity-marking strategies
    as form-class properties (a particle either *is* or *is not*
    `polarityReversal`), aligned with the @cite{bluhdorn-lohnstein-2012} /
    @cite{sudhoff-2012} / @cite{turco-braun-dimroth-2014} tradition that
    pairs polarity contrast with specific lexical or prosodic devices.
    See `Phenomena/Polarity/Studies/TurcoBraunDimroth2014.lean` for the
    canonical consumer.

    **This framework is contested.** @cite{matic-nikolaeva-2018} (in
    @cite{dimroth-sudhoff-2018}) explicitly reject the form-class encoding,
    arguing that "polarity focus" is not a fixed form-meaning association
    but a pragmatic interpretation arising from context — they propose
    *salient polarity* as the correct construct.
    @cite{garassino-jacob-2018} (same volume, fn 13) endorse the M&N view:
    "PF (or salient polarity as they prefer to name this specific type of
    emphasis) is not directly encoded by certain linguistic forms in a
    given language but can be pragmatically conveyed by different
    structures under appropriate (contextual) conditions." So the very
    chapter that anchors `Fragments/Italian/PolarityMarking.lean::siChe`
    disagrees with the encoding choice this enum makes.

    The non-equivalence between form-class encoding and M&N's pragmatic
    salient-polarity property is stated as a Lean theorem in
    `Phenomena/Polarity/Studies/MaticNikolaeva2018.lean`. The substrate
    keeps the form-class enum because (a) it has 8 cross-language
    consumers via TBD2014, (b) M&N's framework is one alternative among
    several — alongside @cite{hohle-1992}'s verum-as-illocutionary-operator
    (`Phenomena/Polarity/Studies/Hohle1992.lean`),
    @cite{romero-han-2004}'s epistemic-CONJ FOR-SURE-CG
    (`Phenomena/Questions/Studies/RomeroHan2004.lean`), and
    @cite{gutzmann-2015}'s use-conditional sentence-mood operators
    (`Theories/Semantics/Mood/Gutzmann.lean` +
    `Phenomena/SentenceMood/Studies/Gutzmann2015.lean`, where verum
    composes via DEONT/EPIS/HKNOW dimensions orthogonal to truth-
    conditional polarity). All three sibling frameworks are in tension
    with the form-class encoding for different reasons; the
    incompatibilities are recorded, not silently resolved. -/
inductive PolarityMarkingStrategy where
  /-- Sentence-internal affirmative particle (e.g., Dutch *wel*) -/
  | particle
  /-- Pitch accent on the finite verb (@cite{hohle-1992} Verum focus) -/
  | verumFocus
  /-- Polarity-reversing particle: affirms [+Pol] while contradicting a
      negative context (e.g., German *doch*, Swedish *jo*, French *si*;
      @cite{holmberg-2016}). The cross-linguistic lumping under this
      constructor records a shared functional role only — the surface
      categories vary (response particle vs. clause-initial construction
      vs. discourse particle); see @cite{garassino-jacob-2018} fn 11. -/
  | polarityReversal
  /-- Other strategy (e.g., pre-utterance particle, intonation pattern) -/
  | other
  /-- No overt polarity marking -/
  | unmarked
  deriving DecidableEq, Repr

/-- Environments / contexts a polarity-marking strategy may be available
    in. Bundles the structural-position dimension (`sentenceInternal`
    vs. pre-utterance) with the discourse-context dimensions (`contrast`,
    `correction`) so per-language entries record one set rather than
    three parallel Bools. -/
inductive PolarityMarkingEnv where
  /-- Position: marker appears sentence-internally (vs. pre-utterance). -/
  | sentenceInternal
  /-- Discourse: marker is available in contrast contexts. -/
  | contrast
  /-- Discourse: marker is available in correction contexts. -/
  | correction
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A cross-linguistic polarity-marking entry.

    Unified structure for all strategies — particles (Dutch *wel*),
    prosodic (German VF), or other. Language-specific Fragment files
    instantiate this with appropriate optional fields. The
    `environments` field records the set of `PolarityMarkingEnv`
    positions/contexts the marker is available in.

    See `PolarityMarkingStrategy` docstring for the framework-commitment
    note: this schema records form-class properties in the
    Blühdorn/Sudhoff/TBD2014 tradition, an encoding contested by
    @cite{matic-nikolaeva-2018} (formalized in
    `Phenomena/Polarity/Studies/MaticNikolaeva2018.lean`). The schema
    is intentionally thin — syntactic position (clause-initial
    construction vs. response particle vs. sentence-medial discourse
    marker) is *not* encoded; cross-linguistic entries grouped under
    the same `strategy` constructor may differ on this dimension. -/
structure PolarityMarkingEntry where
  /-- Descriptive label (e.g., "wel", "Verum focus", "doch (pre-utterance)") -/
  label : String
  /-- Surface form, if the strategy is a particle -/
  form : Option String := none
  /-- What bears prosodic prominence, if the strategy is prosodic -/
  prosodicTarget : Option String := none
  /-- Set of positions/contexts in which this marker is available. -/
  environments : Typology.Profile PolarityMarkingEnv
  /-- The polarity-marking strategy category -/
  strategy : PolarityMarkingStrategy

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
