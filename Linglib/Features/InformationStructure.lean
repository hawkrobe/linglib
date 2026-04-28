import Linglib.Core.Discourse.AtIssueness

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

/-! ## Theme and Rheme -/

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

/-! ## Focus and Background -/

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

/-! ## Information Structure Partition -/

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

/-! ## Discourse Status -/

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

/-! ## Focus Interpretation Principle (Rooth 1992) -/

/-- Application type for the Focus Interpretation Principle. The four
    constructors below pick out the families of focus uses Rooth surveys
    (focusing adverbs, contrast/parallelism, scalar implicature,
    question–answer congruence). UNVERIFIED whether the paper specifies
    exactly these four under a single header — earlier prose claimed
    `@cite{rooth-1992} §2`, removed pending PDF check. -/
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

/-! ## Categorical vs Thetic Judgment (Kuroda 1972)

@cite{kuroda-1972} distinguishes two types of judgment that correspond
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
  /-- Subject-predicate; ψ-subject is Topic -/
  | categorical
  /-- Event-presenting; no subject of predication -/
  | thetic
  deriving DecidableEq, Repr

/-- Does this judgment type place a subject of predication (ψ-subject)
    in a dedicated syntactic position (e.g., Spec,TP)? -/
def JudgmentType.HasψSubject (j : JudgmentType) : Prop :=
  j = .categorical

instance (j : JudgmentType) : Decidable j.HasψSubject :=
  inferInstanceAs (Decidable (j = .categorical))

end Features.InformationStructure
