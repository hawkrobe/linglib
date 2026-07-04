/-!
# Features.InformationStructure

[rooth-1992] [steedman-2000] [kuroda-1972]
[umbach-2004] [turco-braun-dimroth-2014]

Theory-neutral substance taxonomies for Information Structure: theme/
rheme partitions, focus/background (binary `FocusMark` + structured
Roothian `Focus α`), focus-marking strategies, judgment type.

[krifka-2008] enumerates four IS notions — focus, givenness,
topic, and **delimitation** (frame-setting); [fery-ishihara-2016]
(Oxford Handbook of Information Structure) adopts Krifka's
definitions as the unifying baseline. At-issueness (the QUD-tradition
axis from Roberts / Tonhauser-Beaver-Roberts-Simons / Tonhauser-Beaver-Degen)
is treated as orthogonal to Krifka's four. Substrate for each:
- Focus: `FocusMark` + `Focus α` (this file).
- Givenness: `Features/Givenness.lean` (`GivennessStatus` + `BinaryGivenness`).
- Topic: no substrate yet — deferred.
- At-issueness: `Discourse/QUD/AtIssueness.lean` (gradient `AtIssuenessDegree`).
- Delimitation: no substrate yet — deferred.

Theme/Rheme and `JudgmentType` (Kuroda 1972) live here too — they
predate Krifka's decomposition and target distinct phenomena
(Prague-school packaging, categorical-vs-thetic judgments).

Theory-level predicates over these taxonomies (the Erteschik-Shir/Abeillé
extraction-IS clash) live in `Semantics/Focus/ExtractionClash.lean`.
Focus-specific compositional operations (`AltMeaning`) live in
`Semantics/Alternatives/`.
-/

namespace Features.InformationStructure

/-! ## Theme and Rheme -/

/-- Theme: what the utterance is about (the "topic" or "given" part).

    The theme:
    - Presupposes a QUD (set of alternatives)
    - Is often prosodically marked (L+H* LH% in English per
      [pierrehumbert-hirschberg-1990]; attributed by
      [steedman-2000] to the Theme tune)
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
      [pierrehumbert-hirschberg-1990])
    - Provides the "answer" to the implicit question

    Example: in "FRED ate the beans", the rheme is "Fred". -/
structure Rheme (P : Type) where
  /-- The rhematic content -/
  content : P

/-! ## Focus and Background -/

/-- Binary focus marking — whether a constituent bears focus or not.
    The simplest categorical encoding of the focus axis (Krifka 2008
    one of four IS notions). Use `FocusMark` when a study only needs the binary
    focus-vs-not distinction; use `Focus α` (below) when the
    Roothian alternative-set structure is needed. -/
inductive FocusMark where
  /-- Constituent is focus-marked (pitch accent / contrast). -/
  | focused
  /-- Constituent is not focus-marked. -/
  | nonFocused
  deriving DecidableEq, Repr, Inhabited

/-- Focus: the contrasted element(s) within theme or rheme.

    Focus is marked by pitch accent and:
    - Evokes alternatives ([rooth-1992] alternative semantics — note
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

/-! ## Categorical vs Thetic Judgment (Kuroda 1972)

[kuroda-1972] distinguishes two types of judgment that correspond
to different information structures:

- **Categorical** judgment: a subject-predicate structure where the
  subject (ψ-subject) is the topic of predication, yielding a
  Theme + Rheme partition.
- **Thetic** judgment: presents an event or situation as a whole,
  without a subject of predication, yielding an all-Rheme (no Theme)
  structure.

Cross-linguistically attested in Japanese (wa/ga), Romance (subject
inversion), and Mayan (ψ-subject constructions,
[aissen-polian-2025]). -/

/-- Judgment type following [kuroda-1972].
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
