import Linglib.Core.Discourse.QUD
import Linglib.Core.InformationStructure
import Linglib.Core.Discourse.AtIssueness
import Linglib.Theories.Semantics.Focus.Interpretation

/-!
# Backgrounded Constituents Are Islands
@cite{kratzer-selkirk-2020} @cite{lu-pan-degen-2025} @cite{roberts-2012} @cite{goldberg-2006}

Formalization of the discourse-backgroundedness account of manner-of-speaking
(MoS) island effects, following @cite{lu-pan-degen-2025}.

## Core Argument

MoS verbs (whisper, shout, etc.) decompose into SAY + MANNER. The manner component activates a salient alternative set that addresses
the QUD, foregrounding the verb and — by the single-QUD-at-a-time constraint — backgrounding the complement. Backgrounded constituents
resist wh-extraction, producing the
island effect.

## Formal Strategy

Communication events have two semantic dimensions: manner and content. The
active QUD (from `Core/QUD.lean`) partitions events along one dimension,
foregrounding it and backgrounding the other. We derive:

1. Manner QUD → content is invisible to the partition → content is backgrounded
2. Content QUD → manner is invisible → content is foregrounded
3. Verb with manner weight → manner QUD is default → island effect
4. Prosodic focus on embedded object → overrides to content QUD → amelioration
5. Adding manner adverb to bridge verb → acquires manner weight → replicates island

## Grounding

- Paper def (3) "foregrounded" = QUD projection (`Core/QUD.lean : QUD.ofDecEq`)
- Paper "backgrounded" = K&S `DiscourseStatus.given` (`Core/InformationStructure.lean`)
- Rooth FIP / Q-A congruence (imported from `Focus/Interpretation.lean`) = QUD cell membership;
  `qaCongruentWeak` derives that extracted fillers are focused (§4 Route 2)

-/

open Core.InformationStructure
open Core.Discourse.AtIssueness

namespace Semantics.Focus.BackgroundedIslands

/-! ## §1. Verb Decomposition

MoS verbs are lexically composed of a light verb SAY and a manner component:

    whisper = SAY + [whispering manner]
    shout = SAY + [shouting manner]
    say = SAY (no manner — bridge verb)

The manner component is what makes MoS verbs lexically "heavier" and activates
manner alternatives that can address the QUD. Bridge verbs like *say* lack this
component and so do not activate manner alternatives by default.
-/

/-- A manner-of-speaking component. The specific manner (whispering, shouting,
etc.) is what generates the alternative set: {say in manner m₁, say in manner
m₂,...}. -/
structure MannerComponent where
  name : String
  deriving DecidableEq, Repr

/-- Lexical decomposition of a communication verb.

MoS verbs have `manner = some _`; bridge verbs have `manner = none`.
The `mannerAdverb` field captures the "say + adverb" construction from
Experiment 3: adding a manner adverb to *say* gives it manner weight. -/
structure VerbDecomp where
  /-- The light verb component (always SAY for communication verbs) -/
  lightVerb : String := "say"
  /-- Lexical manner component — present for MoS verbs, absent for bridge verbs -/
  manner : Option MannerComponent := none
  /-- Manner adverb (for "say softly" constructions) -/
  mannerAdverb : Option String := none
  deriving Repr

/-- A verb has **manner weight** if it has either a lexical manner component
(MoS verbs) or a manner adverb ("say softly"). This is the property that
determines default QUD selection and therefore backgroundedness. -/
def VerbDecomp.hasMannerWeight (v : VerbDecomp) : Bool :=
  v.manner.isSome || v.mannerAdverb.isSome

-- Canonical decompositions

def whisperDecomp : VerbDecomp := { manner := some ⟨"whispering"⟩ }
def shoutDecomp : VerbDecomp := { manner := some ⟨"shouting"⟩ }
def sayDecomp : VerbDecomp := {}
def saySoftlyDecomp : VerbDecomp := { mannerAdverb := some "softly" }

/-! ## §2. Two-Dimensional Communication Events and QUD Projections

A communication event has two semantic dimensions: the **manner** of
communication (how it was said) and the propositional **content** (what
was said). The QUD determines which dimension is "at issue."

The paper's definition (3) — FOREGROUNDED iff the alternative set relative
to C is a subset of Q-alternatives determined by the QUD — corresponds
formally to whether the QUD *projects onto* that dimension: if the QUD
partitions events by manner, then manner is foregrounded (it distinguishes
Q-alternatives) and content is backgrounded (it doesn't).
-/

/-- Dimension of a communication utterance that the QUD can target. -/
inductive CommDimension where
  /-- QUD asks about manner: "How/In what way did John say it?" -/
  | manner
  /-- QUD asks about content: "What did John say?" -/
  | content
  deriving DecidableEq, Repr

/-- A communication event has two semantic dimensions.
This mirrors the verb decomposition: MoS verbs make both dimensions
available, while bridge verbs foreground only content. -/
structure CommEvent (Manner Content : Type) where
  manner : Manner
  content : Content

variable {Manner Content : Type} [DecidableEq Manner] [DecidableEq Content]

instance [BEq Manner] [BEq Content] : BEq (CommEvent Manner Content) where
  beq e1 e2 := e1.manner == e2.manner && e1.content == e2.content

/-- The **manner QUD**: partitions communication events by HOW something was said.
"In what manner did John say that Mary was in the courtyard?"

Under this QUD, events with the same manner are equivalent regardless of
content — content variation is invisible, hence content is backgrounded.

Built using `QUD.ofDecEq` from `Core/QUD.lean`. -/
def mannerQUD : QUD (CommEvent Manner Content) :=
  QUD.ofDecEq (·.manner) "manner"

/-- The **content QUD**: partitions communication events by WHAT was said.
"What did John say?"

Under this QUD, events with the same content are equivalent regardless of
manner — manner variation is invisible, hence manner is backgrounded.

Built using `QUD.ofDecEq` from `Core/QUD.lean`. -/
def contentQUD : QUD (CommEvent Manner Content) :=
  QUD.ofDecEq (·.content) "content"

/-! ## §3. Core Theorems: QUD Determines Backgroundedness

These theorems formalize the paper's central claim: the QUD determines which
dimension of a communication event is foregrounded (participates in the QUD
partition) and which is backgrounded (invisible to the partition).
-/

/-- **Manner QUD ignores content**: Under the manner QUD, events with the same
manner are equivalent regardless of their content.

This is the formal heart of the paper: content is invisible to the manner QUD
partition, which is exactly what "backgrounded" means — the content doesn't
participate in distinguishing Q-alternatives. -/
theorem manner_qud_ignores_content (e1 e2 : CommEvent Manner Content)
    (h : e1.manner = e2.manner) :
    mannerQUD.sameAnswer e1 e2 = true := by
  simp only [mannerQUD, QUD.ofDecEq]
  exact decide_eq_true_eq.mpr h

/-- **Content QUD ignores manner**: Under the content QUD, events with the same
content are equivalent regardless of manner. -/
theorem content_qud_ignores_manner (e1 e2 : CommEvent Manner Content)
    (h : e1.content = e2.content) :
    contentQUD.sameAnswer e1 e2 = true := by
  simp only [contentQUD, QUD.ofDecEq]
  exact decide_eq_true_eq.mpr h

/-- **Backgroundedness = QUD invisibility**: Varying the content of a communication
event does not change its QUD cell under the manner QUD.

Formally: for any event `e` and any alternative content `c'`, the event
`⟨e.manner, c'⟩` is in the same manner-QUD cell as `e`. This means the
content dimension is "invisible" to the partition — it is backgrounded.

This directly formalizes the paper's claim that elements in MoS verb
complements are discourse-backgrounded. -/
theorem backgroundedness_means_qud_invisible
    (e : CommEvent Manner Content) (c' : Content) :
    (mannerQUD (Manner := Manner) (Content := Content)).sameAnswer
      e ⟨e.manner, c'⟩ = true :=
  manner_qud_ignores_content e ⟨e.manner, c'⟩ rfl

/-- Backgrounded content is in the same QUD cell (set-membership version). -/
theorem backgrounded_content_same_cell
    [BEq Manner] [BEq Content]
    (e : CommEvent Manner Content) (c' : Content) :
    (⟨e.manner, c'⟩ : CommEvent Manner Content) ∈
      (mannerQUD (Manner := Manner) (Content := Content)).cell e := by
  rw [QUD.mem_cell_iff]
  exact backgroundedness_means_qud_invisible e c'

/-- **Foregrounding is QUD projection (manner direction)**: events in the same
manner-QUD cell must agree on manner. That is, manner **distinguishes**
Q-alternatives — it is foregrounded.

This is the converse of `manner_qud_ignores_content`: while content is
invisible to the manner QUD, manner is NOT invisible — it's what the
partition is about. -/
theorem foregrounding_is_qud_projection_manner
    (e1 e2 : CommEvent Manner Content)
    (h : (mannerQUD (Manner := Manner) (Content := Content)).sameAnswer e1 e2 = true) :
    e1.manner = e2.manner := by
  simp only [mannerQUD, QUD.ofDecEq] at h
  exact decide_eq_true_eq.mp h

/-- **Foregrounding is QUD projection (content direction)**: events in the same
content-QUD cell must agree on content. -/
theorem foregrounding_is_qud_projection_content
    (e1 e2 : CommEvent Manner Content)
    (h : (contentQUD (Manner := Manner) (Content := Content)).sameAnswer e1 e2 = true) :
    e1.content = e2.content := by
  simp only [contentQUD, QUD.ofDecEq] at h
  exact decide_eq_true_eq.mp h

/-- **Manner QUD and content QUD are genuinely distinct partitions.**
Events can be equivalent under one QUD but not the other. This is what makes
the foregrounding/backgrounding complementarity non-trivial: you can't
foreground both dimensions under a single QUD.

Formally: if two events share manner but differ in content, they are
equivalent under the manner QUD but NOT under the content QUD. -/
theorem manner_content_qud_distinct
    (e1 e2 : CommEvent Manner Content)
    (h_same_manner : e1.manner = e2.manner)
    (h_diff_content : e1.content ≠ e2.content) :
    (mannerQUD (Manner := Manner) (Content := Content)).sameAnswer e1 e2 = true ∧
    ¬((contentQUD (Manner := Manner) (Content := Content)).sameAnswer e1 e2 = true) := by
  constructor
  · exact manner_qud_ignores_content e1 e2 h_same_manner
  · simp only [contentQUD, QUD.ofDecEq, decide_eq_true_eq]
    exact h_diff_content

/-! ## §4. Deriving the Extraction Constraint
@cite{erteschik-shir-1973} @cite{roberts-1996} @cite{goldberg-2006}

The backgroundedness constraint on extraction — that backgrounded constituents
resist wh-extraction — is not stipulated but **derived** from the QUD partition
via two converging routes.

### Route 1: Question relevance (@cite{roberts-1996})

Extraction creates a wh-question about the gap:

    "What₁ did John whisper that Mary gave t₁ to Bill?"

Under the manner QUD, content variation is invisible (§3): all fillers produce
events in the same QUD cell. The extraction question cannot be answered
informatively — it is QUD-irrelevant, hence infelicitous.

### Route 2: Information-structural clash (@cite{erteschik-shir-1973})

Wh-extraction creates a **content QUD**: "What₁ did John whisper t₁?"
partitions events by the filler's value. By @cite{rooth-1992}'s Q-A
congruence constraint (26d) — formalized as `qaCongruentWeak` in
`Focus/Interpretation.lean` — the question's Hamblin denotation (the set
of propositions obtained by varying the filler) must be ⊆ the answer's
focus alternatives. Since focus alternatives are generated by substitution
at the focused position, the filler position IS the focused position.
So the extracted filler is [FoC].

But the extraction site is inside a backgrounded clause ([G]-marked under
the verb's default manner QUD). A [FoC] element inside a [G] clause
creates a clash: the filler addresses the extraction QUD but belongs to
a dimension the verb's QUD ignores.

The underlying mechanism is **QUD conflict**: the extraction QUD (content)
and the verb's default QUD (manner) assign incompatible statuses to the
complement. The extraction QUD needs the filler to be focused; the verb's
QUD backgrounds the entire complement.

Both routes derive the same prediction from the same QUD property
(`manner_qud_ignores_content`): extraction from backgrounded clauses is
degraded, and the degradation disappears when the QUD shifts to target
content (prosodic amelioration). -/

-- ── Route 1: Question relevance ─────────────────────────────────────

/-- Whether a wh-question about the content of a communication event is
**relevant** to a given QUD (@cite{roberts-1996}): different content values
must produce events in different QUD cells. If not, the extraction question
is vacuous — every filler gives the same QUD-level answer. -/
def contentQuestionRelevant (qud : QUD (CommEvent Manner Content)) : Prop :=
  ∃ (m : Manner) (c₁ c₂ : Content),
    qud.sameAnswer ⟨m, c₁⟩ ⟨m, c₂⟩ = false

/-- Under the manner QUD, content extraction questions are QUD-irrelevant:
varying content never changes the QUD cell. -/
theorem content_question_irrelevant_under_manner :
    ¬ contentQuestionRelevant (mannerQUD (Manner := Manner) (Content := Content)) := by
  intro ⟨_, _, _, h⟩
  simp [mannerQUD, QUD.ofDecEq] at h

/-- Under the content QUD, content extraction questions ARE QUD-relevant:
different content values produce events in different QUD cells. -/
theorem content_question_relevant_under_content
    (m : Manner) (c₁ c₂ : Content) (hne : c₁ ≠ c₂) :
    contentQuestionRelevant (contentQUD (Manner := Manner) (Content := Content)) :=
  ⟨m, c₁, c₂, by simp [contentQUD, QUD.ofDecEq, hne]⟩

-- ── Route 2: Information-structural clash ────────────────────────────

/-- The QUD established by wh-extraction from a communication verb's
complement. "What₁ did John whisper t₁?" partitions events by the filler
(= content dimension). (@cite{roberts-2012}: wh-questions establish QUDs.) -/
def extractionQUD : QUD (CommEvent Manner Content) := contentQUD

/-- The extraction QUD partitions by content: different fillers produce
different QUD cells. This is what makes the filler the focused element —
it is the variable that distinguishes alternatives.

Combined with `qaCongruentWeak` from `Focus/Interpretation.lean`
(@cite{rooth-1992} (26d): [ψ]° ⊆ [α]^f), this **derives** that extracted
elements are [FoC]-marked: the question's alternatives (varying the filler)
must be focus alternatives of the answer (varying the focused position),
so filler position = focused position. -/
theorem extraction_filler_varies
    (m : Manner) (c₁ c₂ : Content) (hne : c₁ ≠ c₂) :
    (extractionQUD (Manner := Manner) (Content := Content)).sameAnswer
      ⟨m, c₁⟩ ⟨m, c₂⟩ = false := by
  simp [extractionQUD, contentQUD, QUD.ofDecEq, hne]

open Semantics.FocusInterpretation Semantics.Questions.Hamblin in
/-- **Q-A congruence applied to extraction** (@cite{rooth-1992} (26d)):
if Q-A congruence holds between the extraction question and the answer's
focus value, then every filler produces a focus alternative of the answer.

This is the formal content of "the filler position = the focused position":
the Hamblin question's alternatives (obtained by varying the filler) must be
focus alternatives of the answer (obtained by varying the focused position),
so these two positions coincide.

The theorem directly uses `qaCongruentWeak` from `Focus/Interpretation.lean`.
Combined with `extraction_filler_varies` (different fillers → different QUD
cells → non-trivial Hamblin alternatives), this derives that extraction
foregrounds the filler. -/
theorem extraction_filler_is_focus_alternative
    {W : Type*}
    (den : CommEvent Manner Content → W → Bool)
    (m : Manner)
    (answerFocus : PropFocusValue W)
    (extractionQ : QuestionDen W)
    -- The extraction question includes all filler propositions
    (hq : ∀ c : Content, extractionQ (den ⟨m, c⟩) = true)
    -- Q-A congruence holds (Rooth 1992, (26d))
    (hqa : qaCongruentWeak answerFocus extractionQ) :
    -- Then: every filler value produces a focus alternative
    ∀ c : Content, answerFocus (den ⟨m, c⟩) = true :=
  fun c => hqa _ (hq c)

/-- The discourse status of the extracted filler: **focused**.

**Derived** from QUD structure + Q-A congruence, not stipulated:
1. Wh-extraction creates a content-QUD (`extractionQUD`, @cite{roberts-2012})
2. The filler distinguishes the extraction QUD's cells (`extraction_filler_varies`)
3. `extraction_filler_is_focus_alternative` (above) uses `qaCongruentWeak`
   (@cite{rooth-1992} (26d)) to show: if the extraction question's alternatives
   ⊆ the answer's focus value, then every filler is a focus alternative.
   Focus alternatives are generated at the focused position, so filler = focused.
4. Foreground = [FoC] in @cite{kratzer-selkirk-2020}'s two-feature system -/
def extractedFillerStatus : DiscourseStatus := .focused

/-- **Extraction from a backgrounded clause creates an IS clash**:
the extracted filler is [FoC] (derived from `extractedFillerStatus`) but
the clause is [G] (derived from the verb's default QUD).

Uses `extractionISClash` from `Core/InformationStructure.lean`, which
unifies @cite{abeille-et-al-2020}'s FBC with @cite{erteschik-shir-1973}'s
Dominance Condition. -/
theorem backgrounded_extraction_clashes :
    extractionISClash extractedFillerStatus .given = true := rfl

/-- Extraction from an at-issue clause does NOT create a clash. -/
theorem atissue_extraction_compatible :
    extractionISClash extractedFillerStatus .new = false := rfl


/-! ## §5. Default QUD Selection: From Verbs to Backgroundedness

MoS verbs, due to their manner component, activate manner alternatives and
make the manner QUD salient by default. Bridge verbs like *say*, lacking a
manner component, default to the content QUD.

This follows from @cite{roberts-1996}: the QUD is determined by what
alternatives are salient, and manner components activate manner alternatives.
-/

/-- Default QUD dimension based on verb properties.
Verbs with manner weight activate the manner QUD (backgrounding content);
verbs without manner weight activate the content QUD (foregrounding content). -/
def defaultDimension (v : VerbDecomp) : CommDimension :=
  if v.hasMannerWeight then .manner else .content

/-- Discourse status of the complement content under a given QUD.

Under manner QUD: content is backgrounded (K&S `DiscourseStatus.given`).
Under content QUD: content is foregrounded (K&S `DiscourseStatus.new`). -/
def complementStatus (dim : CommDimension) : DiscourseStatus :=
  match dim with
  | .manner  => .given   -- backgrounded: invisible to QUD
  | .content => .new     -- discourse-new: at issue

/-- Discourse status of the matrix verb under a given QUD. -/
def verbStatus (dim : CommDimension) : DiscourseStatus :=
  match dim with
  | .manner  => .focused  -- foregrounded: FoC-marked, addresses QUD
  | .content => .given    -- backgrounded

/-! ## §6. The MoS Island Effect: Main Derivation

The full derivation chain:

1. MoS verb has manner weight (lexical decomposition, §1)
2. Manner weight → default QUD dimension is manner (§5 `defaultDimension`)
3. Manner QUD → complement is backgrounded (§5 `complementStatus`)
4. Backgrounded → extraction question QUD-irrelevant (§4 Route 1)
5. Backgrounded → extraction creates information-structural clash (§4 Route 2)

Steps 4 and 5 are derived in §4 from `manner_qud_ignores_content`.
`DiscourseStatus.rank` from `Core/InformationStructure.lean` provides the
ordinal ranking consistent with this derivation.
-/

/-- **MoS Island Effect**: MoS verbs default-background their complements. -/
theorem mos_island_effect (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    complementStatus (defaultDimension v) = .given := by
  simp only [defaultDimension, h, ite_true, complementStatus]

/-- **Bridge Verb Transparency**: Bridge verbs default to the content QUD. -/
theorem bridge_verb_transparent (v : VerbDecomp) (h : v.hasMannerWeight = false) :
    complementStatus (defaultDimension v) = .new := by
  simp only [defaultDimension, h, Bool.false_eq_true, ite_false, complementStatus]

/-- **QUD conflict** (§4 Route 2): the extraction QUD and the verb's default
QUD assign incompatible statuses to the complement content.
- Extraction QUD (content) → content is at-issue, filler is focused
- Verb's default QUD (manner) → content is backgrounded

The IS clash arises because the verb's manner QUD backgrounds the entire
complement, but extraction needs the filler to be focused within it. -/
theorem qud_conflict (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    -- Under the verb's default QUD: complement is backgrounded
    complementStatus (defaultDimension v) = .given ∧
    -- Under the extraction QUD: complement content is at-issue
    complementStatus .content = .new :=
  ⟨by simp [defaultDimension, h, complementStatus], rfl⟩

/-- MoS verbs trigger the information-structural clash (§4 Route 2):
filler is [FoC] (derived via `extractedFillerStatus`), complement is [G]. -/
theorem mos_extraction_clashes (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    extractionISClash extractedFillerStatus (complementStatus (defaultDimension v)) = true := by
  simp only [defaultDimension, h, ite_true, complementStatus, extractedFillerStatus]; rfl

/-- Bridge verbs do NOT trigger the clash: complement is [new], not [G]. -/
theorem bridge_no_extraction_clash (v : VerbDecomp) (h : v.hasMannerWeight = false) :
    extractionISClash extractedFillerStatus (complementStatus (defaultDimension v)) = false := by
  simp only [defaultDimension, h, Bool.false_eq_true, ite_false, complementStatus,
             extractedFillerStatus]; rfl

/-- `DiscourseStatus.rank` is injective: distinct statuses have distinct ranks.
Subsumes the pairwise chain `backgrounded_lt_new` / `new_lt_focused`. -/
theorem DiscourseStatus.rank_injective (a b : DiscourseStatus)
    (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [DiscourseStatus.rank]


/-! ## §7. Prosodic Amelioration (Experiments 1 & 3b)

Prosodic focus ([FoC]) on the embedded object overrides the default manner
QUD, forcing the content QUD. Under the content QUD, content extraction
questions are QUD-relevant (§4 `content_question_relevant_under_content`),
restoring extraction felicity.

This is predicted by the backgroundedness account and NOT by the subjacency
or frequency accounts: prosody changes information structure without changing
syntactic structure or verb-frame frequency.
-/

/-- Active QUD dimension after prosodic manipulation.

Prosodic [FoC] on the embedded object makes the content dimension salient,
overriding the default manner QUD. This models the capitalization/bolding
manipulation in Experiments 1 and 3b. -/
def activeDimension (v : VerbDecomp) (embeddedObjectFocused : Bool) : CommDimension :=
  if embeddedObjectFocused then .content
  else defaultDimension v

/-- **Prosodic Amelioration Theorem**: Focusing the embedded object always
results in the content QUD, regardless of verb type.

This captures Experiments 1 and 3b: prosodic focus on the embedded object
ameliorates the island effect for both MoS verbs and say+adverb. -/
theorem prosodic_focus_ameliorates (v : VerbDecomp) :
    activeDimension v true = .content := by
  simp [activeDimension]

/-- Under prosodic focus, complement is not backgrounded. -/
theorem focused_complement_not_backgrounded (v : VerbDecomp) :
    complementStatus (activeDimension v true) = .new := by
  simp [activeDimension, complementStatus]

/-- **Prosodic focus resolves the information-structural clash**: under
embedded focus, the complement is [new] (not [G]), so the filler's [FoC]
status no longer clashes. This is why prosodic amelioration works. -/
theorem prosodic_focus_resolves_clash (v : VerbDecomp) :
    extractionISClash extractedFillerStatus (complementStatus (activeDimension v true)) = false := by
  simp only [activeDimension, ite_true, complementStatus, extractedFillerStatus]; rfl

/-- Without prosodic focus, MoS verb complements ARE backgrounded. -/
theorem unfocused_mos_complement_backgrounded
    (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    complementStatus (activeDimension v false) = .given := by
  simp [activeDimension, defaultDimension, h, complementStatus]

/-- **Amelioration improves extraction**: Extraction from prosodically focused
complement is better than extraction from default-backgrounded complement. -/
theorem amelioration_improves_extraction :
    (complementStatus .content).rank >
    (complementStatus .manner).rank := by
  native_decide

/-- **Focus sensitivity for MoS verbs**: Prosodic focus changes the extraction
prediction for MoS verbs from degraded (backgrounded) to acceptable (new). -/
theorem mos_focus_sensitivity (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    (complementStatus (activeDimension v true)).rank >
    (complementStatus (activeDimension v false)).rank := by
  simp [activeDimension, defaultDimension, h, complementStatus]
  native_decide

/-! ## §8. Say + Adverb Replication (Experiment 3)

**The paper's key novel prediction**: adding a manner adverb to *say* gives
it manner weight, shifting the default QUD to manner and replicating the
MoS island effect.

    "say softly" = say + manner adverb → manner weight → manner QUD → island
    "say" = say (no modifier) → no manner weight → content QUD → no island

This uniquely distinguishes the backgroundedness account:
- Subjacency: same CP structure ± adverb → no contrast predicted
- Frequency: would need to check corpus counts; n.s. in the data
- Backgroundedness: manner adverb adds manner weight → predicts contrast ✓
-/

/-- *say* has no manner weight. -/
theorem say_no_manner_weight : sayDecomp.hasMannerWeight = false := rfl

/-- *say softly* has manner weight (from the adverb). -/
theorem say_softly_has_manner_weight : saySoftlyDecomp.hasMannerWeight = true := rfl

/-- *whisper* has manner weight (from lexical decomposition). -/
theorem whisper_has_manner_weight : whisperDecomp.hasMannerWeight = true := rfl

/-- *shout* has manner weight (from lexical decomposition). -/
theorem shout_has_manner_weight : shoutDecomp.hasMannerWeight = true := rfl

/-- **Say+Adverb Replication Theorem**: Adding a manner adverb to *say*
produces the same complement backgroundedness as MoS verbs.

*say softly* and *whisper* both have manner weight, so they both default
to the manner QUD, backgrounding their complements identically. -/
theorem say_adverb_replicates_mos :
    complementStatus (defaultDimension saySoftlyDecomp) =
    complementStatus (defaultDimension whisperDecomp) := rfl

/-- *say* and *say softly* differ in complement backgroundedness. -/
theorem say_vs_say_softly_status :
    complementStatus (defaultDimension sayDecomp) ≠
    complementStatus (defaultDimension saySoftlyDecomp) := by
  simp [defaultDimension, VerbDecomp.hasMannerWeight, sayDecomp, saySoftlyDecomp,
        complementStatus]

/-- *say* extraction is better than *say softly* extraction. -/
theorem say_vs_say_softly_acceptability :
    (complementStatus (defaultDimension sayDecomp)).rank >
    (complementStatus (defaultDimension saySoftlyDecomp)).rank := by
  native_decide

/-- The say+adverb island is also focus-sensitive (like the MoS island). -/
theorem say_adverb_focus_sensitive :
    (complementStatus (activeDimension saySoftlyDecomp true)).rank >
    (complementStatus (activeDimension saySoftlyDecomp false)).rank := by
  simp [activeDimension, defaultDimension, VerbDecomp.hasMannerWeight,
        saySoftlyDecomp, complementStatus]
  native_decide

/-! ## §9. Theory Comparison

Three accounts of the MoS island effect make different predictions. Only the
backgroundedness account correctly predicts all five experiments' results.
-/

/-- Accounts of the MoS island effect. -/
inductive MoSAccount where
  /-- Structural: MoS verbs select complex-NP complements. -/
  | subjacency
  /-- Processing: low verb-frame frequency → high surprisal. -/
  | verbFrameFrequency
  /-- Discourse: backgrounded complements resist extraction. -/
  | backgroundedness
  deriving DecidableEq, Repr

/-- Testable predictions of each account.

The three accounts make divergent predictions for three key manipulations,
allowing empirical discrimination. -/
structure Prediction where
  /-- Does prosodic focus affect extraction acceptability?
  (Tested in Experiments 1, 2a, 3b) -/
  focusSensitive : Bool
  /-- Does say + manner adverb create an island?
  (Tested in Experiment 3a) -/
  sayAdverbCreatesIsland : Bool
  /-- Does verb-frame frequency correlate with acceptability?
  (Tested in all experiments) -/
  frequencyCorrelation : Bool
  deriving DecidableEq, Repr

/-- Predictions of each account. -/
def accountPredictions : MoSAccount → Prediction
  | .subjacency => {
      focusSensitive := false          -- syntax doesn't change with prosody
      sayAdverbCreatesIsland := false   -- same CP structure ± adverb
      frequencyCorrelation := false     -- irrelevant to structure
    }
  | .verbFrameFrequency => {
      focusSensitive := false          -- frequency doesn't change with prosody
      sayAdverbCreatesIsland := false   -- would need frequency data
      frequencyCorrelation := true      -- by definition
    }
  | .backgroundedness => {
      focusSensitive := true           -- focus changes backgroundedness
      sayAdverbCreatesIsland := true   -- manner adverb adds manner weight
      frequencyCorrelation := false    -- backgroundedness, not frequency, is causal
    }

/-- Empirical results from @cite{lu-pan-degen-2025}. -/
def empiricalResults : Prediction := {
  focusSensitive := true             -- Experiments 1, 2a, 3b: all significant
  sayAdverbCreatesIsland := true     -- Experiment 3a: p < 0.001
  frequencyCorrelation := false      -- All experiments: p > 0.05
}

/-- Score: number of correct predictions. -/
def accountScore (a : MoSAccount) : Nat :=
  let p := accountPredictions a
  let e := empiricalResults
  (if p.focusSensitive == e.focusSensitive then 1 else 0) +
  (if p.sayAdverbCreatesIsland == e.sayAdverbCreatesIsland then 1 else 0) +
  (if p.frequencyCorrelation == e.frequencyCorrelation then 1 else 0)

/-- **The backgroundedness account matches all empirical results (3/3).** -/
theorem backgroundedness_perfect_score :
    accountScore .backgroundedness = 3 := by native_decide

/-- **The subjacency account scores 1/3** (only no-frequency-correlation). -/
theorem subjacency_score :
    accountScore .subjacency = 1 := by native_decide

/-- **The frequency account scores 0/3** (all predictions wrong). -/
theorem frequency_score :
    accountScore .verbFrameFrequency = 0 := by native_decide

/-- **The backgroundedness account strictly dominates both alternatives.** -/
theorem backgroundedness_dominates :
    accountScore .backgroundedness > accountScore .subjacency ∧
    accountScore .backgroundedness > accountScore .verbFrameFrequency := by
  constructor <;> native_decide

/-! ## §10. Grounding in Linglib Infrastructure

These theorems connect the paper's theoretical definitions to existing
linglib formalization, establishing that this is not an isolated theory
but a natural extension of the QUD and information-structure framework.
-/

/-- **Foregrounding = QUD cell membership (biconditional, manner direction).**

The paper defines (def 3): "C is foregrounded iff Alt(C) ⊆ Q-alternatives."

In our formalization: a dimension is foregrounded under a QUD iff the QUD
projects onto it — same-cell events agree on that dimension, and conversely,
agreeing on that dimension suffices for same-cell membership.

This biconditional shows that our QUD.ofDecEq model exactly captures the
paper's notion of foregrounding. -/
theorem foregrounding_iff_qud_manner
    (e1 e2 : CommEvent Manner Content) :
    (mannerQUD (Manner := Manner) (Content := Content)).sameAnswer e1 e2 = true ↔
    e1.manner = e2.manner := by
  constructor
  · exact foregrounding_is_qud_projection_manner e1 e2
  · exact manner_qud_ignores_content e1 e2

/-- **Foregrounding = QUD cell membership (biconditional, content direction).** -/
theorem foregrounding_iff_qud_content
    (e1 e2 : CommEvent Manner Content) :
    (contentQUD (Manner := Manner) (Content := Content)).sameAnswer e1 e2 = true ↔
    e1.content = e2.content := by
  constructor
  · exact foregrounding_is_qud_projection_content e1 e2
  · exact content_qud_ignores_manner e1 e2

/-- **QUD complementarity**: Under manner QUD, manner is foregrounded ([FoC])
and content is backgrounded ([G]). Under content QUD, vice versa.

This connects to @cite{kratzer-selkirk-2020}'s insight that [FoC] and [G] are
mutually exclusive features — you can't foreground and background the same
dimension simultaneously. Extended here to cross-dimensional complementarity:
foregrounding one dimension of a communication event necessarily backgrounds
the other, given the single-QUD-at-a-time constraint. -/
theorem qud_complementarity :
    (verbStatus .manner = .focused ∧ complementStatus .manner = .given) ∧
    (verbStatus .content = .given ∧ complementStatus .content = .new) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- **Backgroundedness = DiscourseStatus.given**: The paper's notion of
"backgrounded" maps directly to Kratzer & Selkirk's [G]-marked status
in the existing @cite{kratzer-selkirk-2020} formalization.

This grounds the paper's informal notion of backgroundedness in the
formal two-feature system already in the codebase. -/
theorem backgroundedness_is_given :
    complementStatus .manner = DiscourseStatus.given := rfl

/-- **Foregrounding = DiscourseStatus.focused**: The paper's notion of
"foregrounded" maps to Kratzer & Selkirk's [FoC]-marked status. -/
theorem foregrounding_is_focused :
    verbStatus .manner = DiscourseStatus.focused := rfl

/-! ## §11. Gradient Manner Weight: Lexical vs. Compositional

@cite{lu-pan-degen-2025} Experiment 2a shows a residual difference between MoS
verbs and *say* even under identical prosodic manipulation: MoS verb complements
are more opaque to extraction than *say* complements (β = −0.08, p < 0.001),
and this holds even when both are prosodically foregrounded.

We extend the binary model to distinguish the **source** of manner weight.
Lexical manner (inherent to the verb root) produces stronger default
backgroundedness than compositional manner (added by adverbial modification).
This is a theoretical extension, not directly stated in the paper, but it
accounts for the residual MoS > say+adverb difference the paper leaves
as an open question (Experiment 2a discussion, p. 641). -/

/-- Source of manner weight in a communication verb.

Lexical manner weight (MoS verbs) is stronger than compositional manner weight
(say+adverb) because lexical manner is part of the verb's root meaning and
therefore more reliably activates manner alternatives. -/
inductive MannerWeightSource where
  /-- Manner encoded in the verb root (MoS verbs: whisper, shout, ...).
  Automatically activates manner alternatives in all contexts. -/
  | lexical
  /-- Manner added by adverbial modification (say softly, say loudly).
  Activates manner alternatives only when the adverb is salient. -/
  | compositional
  /-- No manner component (bridge verbs: say, tell). -/
  | none
  deriving DecidableEq, Repr

/-- Derive manner weight source from verb decomposition. -/
def VerbDecomp.mannerWeightSource (v : VerbDecomp) : MannerWeightSource :=
  if v.manner.isSome then .lexical
  else if v.mannerAdverb.isSome then .compositional
  else .none

/-- Ordinal ranking of manner weight strength.
Captures the prediction that lexical > compositional > none
in default backgrounding of complements. -/
def MannerWeightSource.rank : MannerWeightSource → Fin 3
  | .none          => 0
  | .compositional => 1
  | .lexical       => 2

theorem whisper_lexical : whisperDecomp.mannerWeightSource = .lexical := rfl
theorem shout_lexical : shoutDecomp.mannerWeightSource = .lexical := rfl
theorem say_softly_compositional : saySoftlyDecomp.mannerWeightSource = .compositional := rfl
theorem say_none_source : sayDecomp.mannerWeightSource = .none := rfl

/-- `MannerWeightSource.rank` is injective: distinct sources have distinct ranks.
Subsumes the pairwise chain `lexical_rank_gt_compositional` /
`compositional_rank_gt_none`. -/
theorem MannerWeightSource.rank_injective (a b : MannerWeightSource)
    (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [MannerWeightSource.rank]

/-- Any manner weight (lexical or compositional) yields `hasMannerWeight = true`.
The binary and gradient models are consistent. -/
theorem manner_weight_source_consistent (v : VerbDecomp) :
    (v.mannerWeightSource ≠ .none) ↔ (v.hasMannerWeight = true) := by
  simp only [VerbDecomp.mannerWeightSource, VerbDecomp.hasMannerWeight]
  cases v.manner.isSome <;> cases v.mannerAdverb.isSome <;> simp

/-! ## §12. Backgroundedness–Projectivity Dissociation

@cite{tonhauser-beaver-degen-2018} show that projectivity and at-issueness are
anti-correlated (r = .85–.99): content that is not at-issue tends to project.
Backgroundedness, in the sense of @cite{lu-pan-degen-2025}, implies low
at-issueness and therefore predicts projectivity.

But the converse fails: **projectivity does not imply backgroundedness.**
The complements of factive verbs like *notice* and *discover* are projective
(presupposed) but NOT discourse-backgrounded — they can be at-issue and
are extractable. This dissociation is what makes backgroundedness, not
projectivity, the correct predictor of extraction resistance. -/

/-- The three properties relevant to extraction: backgroundedness, projectivity,
and extraction resistance. Backgroundedness determines extraction resistance;
projectivity is independent. Consistency with the §16 prediction API is
verified per-profile by `mos_profile_consistent`, `factive_profile_consistent`,
and `bridge_profile_consistent` below §15. -/
structure ExtractionProfile where
  /-- Content is discourse-backgrounded (not at-issue per QUD) -/
  backgrounded : Bool
  /-- Content projects under operators (negation, modals, conditionals) -/
  projective : Bool
  /-- Extraction from the clause is degraded -/
  resistsExtraction : Bool
  deriving DecidableEq, Repr

/-- MoS verb complement: backgrounded → projective → resists extraction.

Backgroundedness is derived from the formal model (§6 `mos_island_effect`).
Projectivity follows from the anti-correlation with at-issueness
(@cite{tonhauser-beaver-degen-2018}): backgrounded content is not at-issue,
and not-at-issue content projects. Extraction resistance follows from
backgroundedness (§6 `DiscourseStatus.rank_injective`). -/
def mosComplementProfile : ExtractionProfile := ⟨true, true, true⟩

/-- Factive verb complement (*notice*, *discover*): projective but NOT
backgrounded → does NOT resist extraction.

This is the key dissociation: *notice* and *annoy* have similar projectivity
levels but very different backgroundedness levels
(@cite{tonhauser-beaver-degen-2018}): *annoy* complements are backgrounded,
*notice* complements are not. Backgroundedness, not projectivity,
determines extraction resistance. -/
def factiveComplementProfile : ExtractionProfile := ⟨false, true, false⟩

/-- Bridge verb complement (*say*): not projective, not backgrounded,
does not resist extraction. Derived: `bridge_verb_transparent` gives
complementStatus = .new → not backgrounded → no extraction resistance. -/
def bridgeComplementProfile : ExtractionProfile := ⟨false, false, false⟩

/-- **Projectivity does not determine extraction resistance.**
MoS and factive complements are both projective, but only MoS
complements resist extraction. -/
theorem projectivity_does_not_determine_extraction :
    mosComplementProfile.projective = factiveComplementProfile.projective ∧
    mosComplementProfile.resistsExtraction ≠ factiveComplementProfile.resistsExtraction := by
  exact ⟨rfl, by simp [mosComplementProfile, factiveComplementProfile]⟩

/-- MoS: backgrounded ↔ resists extraction. -/
theorem mos_backgrounded_iff_resists :
    mosComplementProfile.backgrounded = mosComplementProfile.resistsExtraction := rfl

/-- Factive: not backgrounded ↔ does not resist extraction. -/
theorem factive_backgrounded_iff_resists :
    factiveComplementProfile.backgrounded = factiveComplementProfile.resistsExtraction := rfl

/-- Bridge: not backgrounded ↔ does not resist extraction. -/
theorem bridge_backgrounded_iff_resists :
    bridgeComplementProfile.backgrounded = bridgeComplementProfile.resistsExtraction := rfl

/-! ## §13. Negation Test (Diagnostic for Backgroundedness)

The negation test (@cite{erteschik-shir-1973}, @cite{ambridge-goldberg-2008},
@cite{lu-pan-degen-2025} p. 630):
backgrounded content is unaffected by matrix sentential negation.

  (7a) John didn't whisper that Mary was in the courtyard.
       → Mary was in the courtyard (complement PROJECTS under negation)

  (7b) John didn't say that Mary was in the courtyard.
       → Mary may or may not have been in the courtyard (complement IN SCOPE)

Under the manner QUD, complement content is backgrounded and projects out of
negation scope. Under the content QUD, complement content is at-issue and
falls within negation scope. The negation test is thus a consequence of
the QUD-determined backgroundedness, not an independent diagnostic. -/

/-- Whether content projects under sentential negation, based on discourse status. -/
def projectsUnderNegation : DiscourseStatus → Bool
  | .given   => true   -- backgrounded: negation targets the verb, not the complement
  | .new     => false  -- at-issue: negation can target the complement
  | .focused => false  -- focused: negation directly targets this constituent

/-- MoS verb complements project under negation. -/
theorem mos_complement_projects_under_negation (v : VerbDecomp)
    (h : v.hasMannerWeight = true) :
    projectsUnderNegation (complementStatus (defaultDimension v)) = true := by
  simp only [defaultDimension, h, ite_true, complementStatus, projectsUnderNegation]

/-- Bridge verb complements do NOT project under negation. -/
theorem bridge_complement_in_negation_scope (v : VerbDecomp)
    (h : v.hasMannerWeight = false) :
    projectsUnderNegation (complementStatus (defaultDimension v)) = false := by
  simp only [defaultDimension, h, Bool.false_eq_true, ite_false, complementStatus,
             projectsUnderNegation]

/-- Prosodic focus overrides: with embedded focus, even MoS verb complements
fall within negation scope (complement becomes at-issue). -/
theorem prosodic_focus_overrides_negation (v : VerbDecomp) :
    projectsUnderNegation (complementStatus (activeDimension v true)) = false := by
  simp [activeDimension, complementStatus, projectsUnderNegation]


/-! ## §14. Complementizer Restriction (Open Problem)

MoS verbs require an overt complementizer *that*; bridge verbs allow null *that*:

    (22a) John said (that) Mary is in the courtyard.       ✓
    (22b) John whispered *(that) Mary is in the courtyard.  ✗

@cite{lu-pan-degen-2025} (§5) explicitly note that the backgroundedness
account **does not explain** this contrast: "the backgroundedness account
does not make any prediction about the overtness of the complementizer."

The subjacency account handles it naturally: if MoS verbs select an
appositive CP (not directly syntactically selected), a null complementizer
is unavailable because null complementizers require syntactic selection.

This remains an open problem and a genuine empirical advantage of the
structural account that the discourse account does not currently capture. -/

/-! ## §15. Gradient At-Issueness: From Binary to Continuous
@cite{tonhauser-beaver-degen-2018} @cite{lu-pan-degen-2025}

The binary model (§5) treats backgroundedness as all-or-nothing: complement
status is either `.given` or `.new`. But @cite{lu-pan-degen-2025} Experiment 2a
shows a residual difference: MoS verbs (50–58) are more degraded than
say+adverb (53), which is more degraded than say (73–80), even under identical
prosodic conditions. The binary model predicts MoS = say+adverb (both `.given`)
and cannot express this gradient.

We lift the model to **gradient at-issueness** using `Rat01` from
`Core/Discourse/AtIssueness.lean`. `MannerWeightSource` determines not just
whether the complement is backgrounded, but *how* backgrounded. Lexical manner
(inherent to verb root) produces stronger backgroundedness than compositional
manner (from adverb modification).

This connects to @cite{tonhauser-beaver-degen-2018}'s Gradient Projection
Principle: at-issueness and projectivity are anti-correlated (r = .85–.99)
and both are gradient, not binary. The three-way ordering derived here
(lexical < compositional < none in at-issueness) is a strictly finer
prediction than the binary model's two-way split. -/

/-- Gradient complement at-issueness based on manner weight source.

- Lexical manner weight (MoS verbs) → 0 (maximally backgrounded)
- Compositional manner weight (say+adverb) → 1/3 (partially backgrounded)
- No manner weight (bridge verbs) → 1 (fully at-issue)

The intermediate value 1/3 is below `defaultThreshold` (1/2), ensuring the
binary model is recoverable: both lexical and compositional map to "not at-issue"
under threshold semantics. -/
def complementAtIssueness : MannerWeightSource → AtIssuenessDegree
  | .lexical       => ⟨0, le_refl 0, by norm_num⟩
  | .compositional => ⟨1/3, by norm_num, by norm_num⟩
  | .none          => ⟨1, by norm_num, le_refl 1⟩

/-- Lexical manner weight yields strictly lower complement at-issueness than
compositional. Matches Exp 2a's residual MoS > say+adverb difference
(β = −0.08, p < 0.001). -/
theorem lexical_lt_compositional_atissueness :
    (complementAtIssueness .lexical).val < (complementAtIssueness .compositional).val := by
  simp only [complementAtIssueness]; norm_num

/-- Compositional manner weight yields strictly lower complement at-issueness
than no manner weight. -/
theorem compositional_lt_none_atissueness :
    (complementAtIssueness .compositional).val < (complementAtIssueness .none).val := by
  simp only [complementAtIssueness]; norm_num

/-- Bridge verbs (at-issueness = 1) are above the default threshold (1/2). -/
theorem bridge_above_threshold :
    (complementAtIssueness .none).val > (1/2 : ℚ) := by
  simp only [complementAtIssueness]; norm_num

/-- Say+adverb (at-issueness = 1/3) is below the default threshold (1/2). -/
theorem compositional_below_threshold :
    (complementAtIssueness .compositional).val < (1/2 : ℚ) := by
  simp only [complementAtIssueness]; norm_num

/-- MoS verbs (at-issueness = 0) are below the default threshold (1/2). -/
theorem lexical_below_threshold :
    (complementAtIssueness .lexical).val < (1/2 : ℚ) := by
  simp only [complementAtIssueness]; norm_num

/-- **Gradient distinguishes what binary cannot**: The binary model predicts
identical complement status for MoS verbs and say+adverb (both `.given`), but
the gradient model assigns strictly different at-issueness degrees.
This accounts for the residual difference in Exp 2a (β = −0.08, p < 0.001)
and the per-verb correlation in Exp 2b (β = −0.44, p = 0.014, across 13
verbs including *say*; MoS-only β = −0.38, p = 0.076). -/
theorem gradient_distinguishes_lexical_compositional :
    -- Binary: same prediction (both .given)
    complementStatus (defaultDimension whisperDecomp) =
    complementStatus (defaultDimension saySoftlyDecomp) ∧
    -- Gradient: different predictions (lexical has strictly lower at-issueness)
    (complementAtIssueness whisperDecomp.mannerWeightSource).val <
    (complementAtIssueness saySoftlyDecomp.mannerWeightSource).val := by
  constructor
  · rfl
  · simp only [VerbDecomp.mannerWeightSource, whisperDecomp, saySoftlyDecomp,
               complementAtIssueness]; norm_num


/-! ## §16. General Island Prediction API

Given an at-issueness degree for any complement type, derive extraction
predictions automatically. This decouples island prediction from manner-of-
speaking specifically: *any* complement whose at-issueness can be estimated
(factive, relative clause, purpose clause, etc.) gets predictions for free.

The key result is `predictIsland_monotone`: extraction rank is monotone in
at-issueness, making at-issueness a **sufficient statistic** for extraction
acceptability. -/

/-- Bundled extraction prediction for an arbitrary complement type. -/
structure IslandPrediction where
  /-- Whether the complement constitutes an island (extraction degraded). -/
  isIsland : Bool
  /-- Discourse status: `.given` (backgrounded) or `.new` (at-issue). -/
  status : DiscourseStatus
  /-- Ordinal extraction acceptability (0 = most degraded, 2 = best). -/
  rank : Fin 3
  deriving DecidableEq, Repr

/-- Derive island predictions from at-issueness degree and threshold.
Complements below threshold are backgrounded (islands); those above are
at-issue (transparent to extraction). -/
def predictIsland (d : AtIssuenessDegree)
    (θ : AtIssuenessThreshold := defaultThreshold) : IslandPrediction where
  isIsland := !isAtIssue d θ
  status := if isAtIssue d θ then .new else .given
  rank := (if isAtIssue d θ then DiscourseStatus.new else DiscourseStatus.given).rank

/-- Factive complement at-issueness: above threshold (presupposed content is
backgrounded qua presupposition, but the *propositional content* is at-issue
— the complement of "know" addresses the QUD). -/
def factiveComplementAI : AtIssuenessDegree := ⟨3/4, by norm_num, by norm_num⟩

-- ── Known-case recovery ──────────────────────────────────────────────

/-- MoS verbs (lexical manner weight) predict islands. -/
theorem predict_mos :
    (predictIsland (complementAtIssueness .lexical)).isIsland = true := by
  native_decide

/-- Bridge verbs (no manner weight) predict no island. -/
theorem predict_bridge :
    (predictIsland (complementAtIssueness .none)).isIsland = false := by
  native_decide

/-- Factive complements (at-issueness 3/4 > threshold 1/2) predict no island. -/
theorem predict_factive :
    (predictIsland factiveComplementAI).isIsland = false := by
  native_decide

-- ── Cross-domain ordering ────────────────────────────────────────────

/-- MoS extraction rank ≤ factive extraction rank. -/
theorem mos_rank_le_factive :
    (predictIsland (complementAtIssueness .lexical)).rank ≤
    (predictIsland factiveComplementAI).rank := by native_decide

/-- Factive extraction rank ≤ bridge extraction rank. -/
theorem factive_rank_le_bridge :
    (predictIsland factiveComplementAI).rank ≤
    (predictIsland (complementAtIssueness .none)).rank := by native_decide

-- ── Monotonicity ─────────────────────────────────────────────────────

/-- **Sufficient statistic theorem**: extraction rank is monotone in
at-issueness. If complement A has at-issueness ≤ complement B, then A's
extraction rank is ≤ B's. This makes at-issueness the only input needed
for extraction predictions — syntax, frequency, and projectivity are
irrelevant once at-issueness is known. -/
theorem predictIsland_monotone (d₁ d₂ : AtIssuenessDegree)
    (θ : AtIssuenessThreshold) (h : d₁.val ≤ d₂.val) :
    (predictIsland d₁ θ).rank ≤ (predictIsland d₂ θ).rank := by
  simp only [predictIsland, DiscourseStatus.rank]
  cases h₁ : isAtIssue d₁ θ <;> cases h₂ : isAtIssue d₂ θ <;>
    simp
  -- Contradictory case: d₁ at-issue but d₂ not, yet d₁.val ≤ d₂.val
  unfold isAtIssue Core.Scale.Rat01.exceeds at h₁ h₂
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at h₁ h₂
  exact absurd (lt_of_lt_of_le h₁ (le_trans h h₂)) (lt_irrefl _)

-- ── §12 ExtractionProfile consistency ───────────────────────────────

/-- MoS profile consistent with predictIsland: both say island. -/
theorem mos_profile_consistent :
    (predictIsland (complementAtIssueness .lexical)).isIsland =
    mosComplementProfile.resistsExtraction := by native_decide

/-- Factive profile consistent with predictIsland: both say no island. -/
theorem factive_profile_consistent :
    (predictIsland factiveComplementAI).isIsland =
    factiveComplementProfile.resistsExtraction := by native_decide

/-- Bridge profile consistent with predictIsland: both say no island. -/
theorem bridge_profile_consistent :
    (predictIsland (complementAtIssueness .none)).isIsland =
    bridgeComplementProfile.resistsExtraction := by native_decide

end Semantics.Focus.BackgroundedIslands
