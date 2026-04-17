import Linglib.Theories.Semantics.Events.Basic
import Linglib.Theories.Semantics.Events.EventRelations

/-!
# Demonstration Semantics for Quotative Complements
@cite{rudin-2025b} @cite{davidson-2015} @cite{eckardt-2014} @cite{maier-2017}

A double-Davidsonian analysis of quotative complements to verbs of
speech, following @cite{rudin-2025b}'s "Embedded Intonation and
Quotative Complements to Verbs of Speech" (Linguistic Inquiry).

## The Core Shift

Standard analysis of *Sara said "Aaron likes apples"*:
- *say* is a 2-place predicate of events and propositions
- The quote denotes a proposition (or content individual)
- *say* introduces a CONTENT relation between the event and the
  proposition

@cite{rudin-2025b}'s proposal: verbs of speech are *uniformly* 1-place event
predicates. The complementizer — overt *that* or covert QUOTE — supplies
the relation:

  ⟦say⟧   = λe. SAY(e)
  ⟦that⟧  introduces CONTENT(e, p)   for propositional δ
  ⟦QUOTE⟧ introduces REENACT(e, u)   for a paratactic performance u

A quotative complement is a covert demonstrative *pthat* whose referent
is the cotemporaneous performance *u* itself. Composition is via
predicate modification, not function application.

## Architecture

We split the formalization in two layers:

1. **`PerformanceOntology Perf`** — properties of utterance-events
   (LINGMAT, Loud, Whispered, RisingDecl, Commits, RaisesIssue) and
   the cross-property axioms that drive verb-class postulates.
2. **`SpeechVerbs Time SemObj Perf [Ω]`** — verb predicates (SAY, ASK,
   ASSERT, YELL, WHISPER), event relations (CONTENT, REENACT), and
   meaning postulates that connect verbs to performances via the
   ontology.

This split mirrors mathlib practice: a small "data" structure exposing
properties + axioms, separated from the larger structure that consumes
them. It also makes the Farkas-Bruce bridge possible: a discourse-state
adapter can supply a `PerformanceOntology` instance whose `Commits` and
`RaisesIssue` are *derived* from F&B dcS / table operations rather than
stipulated (see `Theories/Pragmatics/Assertion/QuotationFBOntology.lean`).

## Meaning Postulates

The verb-class differences are captured by *meaning postulates*
constraining the relation between verbal predicates and properties of
performances:

  SAY(e)     ↔ ∀u. REENACT(e,u) → LINGMAT(u)        (Rudin §3.3.4)
  ASK(e)     ↔ ∀u. REENACT(e,u) → RESP(u)           (Rudin §4.4.1)
  ASSERT(e)  ↔ SAY(e) ∧ ∀u. REENACT(e,u) → Commits(u)   [extrapolation]
  YELL(e)    ↔ SAY(e) ∧ ∀u. REENACT(e,u) → Loud(u)      [extrapolation]
  WHISPER(e) ↔ SAY(e) ∧ ∀u. REENACT(e,u) → Whispered(u) [extrapolation]

where `RESP(u) := RaisesIssue(u) ∧ ¬ Commits(u)` is the
"response-eliciting" property characterized by @cite{rudin-2025b}.

These postulates derive @cite{rudin-2025b}'s empirical generalizations:

- *yell* is consistent with quotative complements requiring loud
  performances; *whisper* is not (incompatible with loud quotation).
- *assert* requires the speaker to commit to the content; rising
  declaratives don't commit; therefore *assert "p?"* is infelicitous
  while *say "p?"* is fine.
- *ask* requires the absence of commitment AND issue-raising; rising
  declaratives are exactly that; therefore *ask "p?"* is fine even
  though propositional *ask that p* is not.

The ASSERT/YELL/WHISPER postulates are formal *extrapolations* of the
informal generalizations in @cite{rudin-2025b} (the paper states the
empirical generalization but does not provide a formal postulate for
each verb). The SAY and ASK postulates are explicit in the paper.

## Anchoring

Performances are *events* in their own right — utterance-events
paratactically associated with the speech-event. We model `Performance`
as a type synonym `Ev Time`, following @cite{rudin-2025b}'s remark that
performances are special-purpose events. But the `SpeechVerbs` structure
is parameterized over an arbitrary `Perf` type, so alternative
ontologies (e.g., a Farkas-Bruce-derived discourse adapter) can supply
their own performance type.
-/

namespace Semantics.Quotation.Demonstration

open Semantics.Events
open Core.Time

-- ════════════════════════════════════════════════════
-- § 1. Performance Ontology
-- ════════════════════════════════════════════════════

/-- Default performance type: an `Ev Time`, since performances have
    temporal extent and ontological status as events
    (per @cite{rudin-2025b}, fn 21). The `SpeechVerbs` structure is
    parameterized over `Perf`, so users may instantiate `Perf` with
    other types (e.g., a discourse-state-derived performance type). -/
abbrev Performance (Time : Type*) [LE Time] := Ev Time

/-- The ontology of performance properties.

    Bundles the basic properties of utterance-events that the verb-class
    meaning postulates appeal to, plus the cross-property axioms that
    @cite{rudin-2025b} relies on (loud/whispered exclusion, rising
    declaratives' non-commitment, etc.).

    Parameterized over `Perf` so that downstream modules can supply
    alternative performance ontologies (e.g., one whose `Commits` is
    derived from a Farkas-Bruce discourse-state update). -/
structure PerformanceOntology (Perf : Type*) where
  /-- LINGMAT: the performance is linguistic material
      (@cite{rudin-2025b} §3.3.4). -/
  LINGMAT : Perf → Prop
  /-- Loud: the performance is loud. -/
  Loud : Perf → Prop
  /-- Whispered: the performance is whispered (sub-vocal). -/
  Whispered : Perf → Prop
  /-- RisingDecl: the performance has rising declarative intonation
      (@cite{rudin-2025b} §4.1, the empirical engine of the paper). -/
  RisingDecl : Perf → Prop
  /-- Commits: the performance commits its speaker to its content
      (Farkas-Bruce dcS update; @cite{farkas-bruce-2010}). -/
  Commits : Perf → Prop
  /-- RaisesIssue: the performance raises an issue
      (Farkas-Bruce table push; @cite{farkas-bruce-2010}). -/
  RaisesIssue : Perf → Prop
  /-- Loud and whispered performances are mutually exclusive. -/
  loud_not_whispered : ∀ u, Loud u → ¬ Whispered u
  /-- Rising declaratives don't commit
      (@cite{rudin-2025b} §4.1, §4.4.1: the load-bearing fact). -/
  rd_not_commits : ∀ u, RisingDecl u → ¬ Commits u
  /-- Rising declaratives raise issues (rising intonation flags
      openness; the issue-raising side of the RESP property). -/
  rd_raises_issue : ∀ u, RisingDecl u → RaisesIssue u
  /-- Rising declaratives are linguistic material. -/
  rd_is_lingmat : ∀ u, RisingDecl u → LINGMAT u

namespace PerformanceOntology

variable {Perf : Type*}

/-- RESP (response-eliciting): the performance raises an issue without
    committing to its resolution. (@cite{rudin-2025b} §4.4.1, eq. for
    the property characterizing ASK-quotative performances.) -/
def RESP (Ω : PerformanceOntology Perf) (u : Perf) : Prop :=
  Ω.RaisesIssue u ∧ ¬ Ω.Commits u

/-- Rising declaratives are RESP. Follows from `rd_raises_issue` and
    `rd_not_commits`. -/
theorem rd_is_resp (Ω : PerformanceOntology Perf) (u : Perf) :
    Ω.RisingDecl u → Ω.RESP u :=
  fun hrd => ⟨Ω.rd_raises_issue u hrd, Ω.rd_not_commits u hrd⟩

end PerformanceOntology

-- ════════════════════════════════════════════════════
-- § 2. SpeechVerbs
-- ════════════════════════════════════════════════════

/-- A model of verbs of speech and their thematic complements,
    parameterized over a performance ontology `Ω`.

    Bundles:
    - **Verb predicates** (1-place predicates of events): SAY, ASSERT,
      ASK, YELL, WHISPER
    - **Event relations**: CONTENT (event to semantic object) and
      REENACT (event to performance)
    - **Sortal predicates** on semantic objects: isProposition, isQuestion
    - **Meaning postulates** as fields, connecting the verbs to `Ω`

    Each meaning postulate carries an annotation indicating whether it
    is *explicit* in @cite{rudin-2025b} or an *extrapolation* (formal
    rendering of an informal generalization in the paper). -/
structure SpeechVerbs (Time SemObj Perf : Type*) [LE Time]
    (Ω : PerformanceOntology Perf) where
  /-- *say*: linguistic-material producing event -/
  SAY : Ev Time → Prop
  /-- *assert*: SAY + commitment -/
  ASSERT : Ev Time → Prop
  /-- *ask*: REENACT pole forces RESP performances -/
  ASK : Ev Time → Prop
  /-- *yell*: SAY + loud performance -/
  YELL : Ev Time → Prop
  /-- *whisper*: SAY + whispered performance -/
  WHISPER : Ev Time → Prop
  /-- CONTENT: event-to-content (proposition or question denotation) -/
  CONTENT : EventRel Time SemObj
  /-- REENACT: event-to-performance (@cite{rudin-2025b} §3.2). -/
  REENACT : EventRel Time Perf
  /-- The semantic object is a proposition. -/
  isProposition : SemObj → Prop
  /-- The semantic object is a question denotation. -/
  isQuestion : SemObj → Prop
  /-- **Explicit in @cite{rudin-2025b} (§3.3.4)**: SAY-events ↔ all
      reenacted performances are linguistic material. -/
  say_iff_lingmat : ∀ e, SAY e ↔ ∀ u, REENACT e u → Ω.LINGMAT u
  /-- **Explicit in @cite{rudin-2025b} (§4.4.1)**: ASK-events ↔ all
      reenacted performances are response-eliciting (raise an issue
      without committing). Crucial: this is *not* merely the absence of
      commitment — it also requires issue-raising, which is what makes
      rising declaratives (a RESP performance) a felicitous ASK
      complement while a silent grunt (no issue raised) would not be. -/
  ask_iff_resp : ∀ e, ASK e ↔ ∀ u, REENACT e u → Ω.RESP u
  /-- **Extrapolation** of the informal generalization in
      @cite{rudin-2025b} (§4.5: *assert* requires speaker commitment).
      The paper does not provide a formal postulate; this is the
      natural rendering. -/
  assert_iff_say_and_commits :
    ∀ e, ASSERT e ↔ SAY e ∧ ∀ u, REENACT e u → Ω.Commits u
  /-- **Extrapolation** of the informal generalization in
      @cite{rudin-2025b} (§3.3.6, §4.7: *yell* requires loud
      performances). -/
  yell_iff_say_and_loud :
    ∀ e, YELL e ↔ SAY e ∧ ∀ u, REENACT e u → Ω.Loud u
  /-- **Extrapolation** dual to `yell_iff_say_and_loud`. -/
  whisper_iff_say_and_whispered :
    ∀ e, WHISPER e ↔ SAY e ∧ ∀ u, REENACT e u → Ω.Whispered u
  /-- **Explicit in @cite{rudin-2025b} (§3.3.4)**: sortal restriction
      on SAY's CONTENT — propositional content of a SAY-event must be
      a proposition. -/
  content_say_propositional :
    ∀ e δ, SAY e → CONTENT e δ → isProposition δ
  /-- **Explicit in @cite{rudin-2025b} (§4.3)**: sortal restriction
      on ASK's CONTENT — propositional content of an ASK-event must
      be a question. -/
  content_ask_question :
    ∀ e δ, ASK e → CONTENT e δ → isQuestion δ
  /-- Sortal disjointness: a semantic object is not simultaneously a
      proposition and a question. Used to derive `*say that <question>*`
      infelicity from the SAY/ASK content sortal restrictions. -/
  prop_not_question : ∀ δ, isProposition δ → ¬ isQuestion δ

namespace SpeechVerbs

variable {Time SemObj Perf : Type*} [LE Time] {Ω : PerformanceOntology Perf}

-- ════════════════════════════════════════════════════
-- § 3. Composition: Quotative vs Propositional Complements
-- ════════════════════════════════════════════════════

/-- *Propositional* complement composition: *V that p* asserts a CONTENT
    relation between the verb-event and the propositional denotation. -/
def thatComp (M : SpeechVerbs Time SemObj Perf Ω) (V : Ev Time → Prop)
    (p : SemObj) (e : Ev Time) : Prop :=
  V e ∧ M.CONTENT e p

/-- *Quotative* complement composition: *V "u"* asserts a REENACT relation
    between the verb-event and the cotemporaneous performance *u*
    (the referent of covert *pthat*; @cite{rudin-2025b} §3). -/
def quoteComp (M : SpeechVerbs Time SemObj Perf Ω) (V : Ev Time → Prop)
    (u : Perf) (e : Ev Time) : Prop :=
  V e ∧ M.REENACT e u

/-- Quotative composition existentially closed over the performance.
    This is what shows up in actual sentence meanings: at the sentence
    level the performance is introduced as an existential when QUOTE
    attaches, then constrained by descriptive content (a proposition
    over performances, e.g., "this rising-declarative tokening of
    *Aaron likes apples?*"). -/
def quoteCompEx (M : SpeechVerbs Time SemObj Perf Ω) (V : Ev Time → Prop)
    (P : Perf → Prop) (e : Ev Time) : Prop :=
  V e ∧ ∃ u, M.REENACT e u ∧ P u

-- ════════════════════════════════════════════════════
-- § 4. Per-verb predictions
-- ════════════════════════════════════════════════════

/-- Prediction: a *say* event with REENACT to *u* requires *u* to be
    linguistic material. (Rules out *#Sara said {grunt}* in the absence
    of LINGMAT.) -/
theorem say_quote_lingmat (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) (u : Perf) :
    quoteComp M M.SAY u e → Ω.LINGMAT u := by
  rintro ⟨hsay, hreen⟩
  exact (M.say_iff_lingmat e).mp hsay u hreen

/-- Prediction: an *assert* event with a rising-declarative performance
    is impossible (@cite{rudin-2025b} §4.5: *#Sara asserted "Aaron
    likes apples?"* with rising intonation). -/
theorem assert_quote_rd_empty (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) (u : Perf) :
    Ω.RisingDecl u → ¬ quoteComp M M.ASSERT u e := by
  intro hrd ⟨hass, hreen⟩
  obtain ⟨_, hcom⟩ := (M.assert_iff_say_and_commits e).mp hass
  exact Ω.rd_not_commits u hrd (hcom u hreen)

/-- Prediction: an *ask* event with a rising-declarative performance is
    consistent. The reenacted performance is RESP (rising declaratives
    raise an issue and don't commit), satisfying ASK's postulate.
    (@cite{rudin-2025b} §4.4.1: derives the felicity of *Sara asked
    "Aaron likes apples?"*.) -/
theorem ask_quote_rd_consistent (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) (u : Perf) :
    M.ASK e → M.REENACT e u → Ω.RisingDecl u → Ω.RESP u := by
  intro hask hreen _
  exact (M.ask_iff_resp e).mp hask u hreen

/-- Prediction: an *ask* event quoting a non-issue-raising performance
    is impossible. The ASK postulate requires `RESP`, which requires
    `RaisesIssue`. (Rules out e.g. *#Sara asked "Aaron likes apples"*
    with falling, declarative intonation that commits the original
    speaker rather than raising an open question.) -/
theorem ask_quote_no_issue_empty (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) (u : Perf) :
    ¬ Ω.RaisesIssue u → ¬ quoteComp M M.ASK u e := by
  intro hni ⟨hask, hreen⟩
  exact hni ((M.ask_iff_resp e).mp hask u hreen).1

/-- Prediction: a *yell* event with REENACT to *u* makes *u* loud. -/
theorem yell_quote_loud (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) (u : Perf) :
    quoteComp M M.YELL u e → Ω.Loud u := by
  rintro ⟨hyell, hreen⟩
  exact ((M.yell_iff_say_and_loud e).mp hyell).2 u hreen

/-- Prediction: a *whisper* event with a loud performance is impossible.
    Loud and whispered are mutually exclusive, but `whisper` requires
    whispered performances. -/
theorem whisper_quote_loud_empty (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) (u : Perf) :
    Ω.Loud u → ¬ quoteComp M M.WHISPER u e := by
  intro hloud ⟨hwhis, hreen⟩
  obtain ⟨_, hwh⟩ := (M.whisper_iff_say_and_whispered e).mp hwhis
  exact Ω.loud_not_whispered u hloud (hwh u hreen)

/-- Sortal prediction: an *ask*-event with propositional CONTENT requires
    that CONTENT be a question. Combined with disjointness of
    `isProposition` and `isQuestion` in concrete models, this rules out
    *#ask that p* with declarative *p*. -/
theorem ask_that_question (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) (δ : SemObj) :
    thatComp M M.ASK δ e → M.isQuestion δ := by
  rintro ⟨hask, hcont⟩
  exact M.content_ask_question e δ hask hcont

-- ════════════════════════════════════════════════════
-- § 5. Verb subsumption corollaries
-- ════════════════════════════════════════════════════

/-- ASSERT ⊆ SAY: an assertion is a saying. Direct from the postulate. -/
theorem assert_implies_say (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) : M.ASSERT e → M.SAY e := fun h =>
  ((M.assert_iff_say_and_commits e).mp h).1

/-- YELL ⊆ SAY: yelling is a manner-of-saying. -/
theorem yell_implies_say (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) : M.YELL e → M.SAY e := fun h =>
  ((M.yell_iff_say_and_loud e).mp h).1

/-- WHISPER ⊆ SAY: whispering is a manner-of-saying. -/
theorem whisper_implies_say (M : SpeechVerbs Time SemObj Perf Ω)
    (e : Ev Time) : M.WHISPER e → M.SAY e := fun h =>
  ((M.whisper_iff_say_and_whispered e).mp h).1

/-- ASSERT and ASK are incompatible at a single performance: ASSERT
    forces commitment, ASK forces non-commitment. (Captures the
    *say*/*ask* polar split — *Sara said "p"* may overlap with *Sara
    asked "p?"* via different performances, but a single performance
    can satisfy at most one.) -/
theorem assert_ask_incompatible_at_perf
    (M : SpeechVerbs Time SemObj Perf Ω) (e e' : Ev Time) (u : Perf) :
    M.ASSERT e → M.REENACT e u → M.ASK e' → M.REENACT e' u → False := by
  intro hass hreen hask hreen'
  obtain ⟨_, hcom⟩ := (M.assert_iff_say_and_commits e).mp hass
  obtain ⟨_, hnc⟩ := (M.ask_iff_resp e').mp hask u hreen'
  exact hnc (hcom u hreen)

/-- *karate gestures* contradiction (motivation for LINGMAT in
    @cite{rudin-2025b}): a SAY-event whose REENACTed performance is
    not linguistic material is impossible. The postulate enforces
    LINGMAT, so a non-LINGMAT witness gives an immediate contradiction. -/
theorem say_non_lingmat_impossible
    (M : SpeechVerbs Time SemObj Perf Ω) (e : Ev Time) (u : Perf) :
    M.SAY e → M.REENACT e u → ¬ Ω.LINGMAT u → False := fun hsay hreen hnl =>
  hnl ((M.say_iff_lingmat e).mp hsay u hreen)

end SpeechVerbs

end Semantics.Quotation.Demonstration
