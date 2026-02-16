import Linglib.Core.QUD
import Linglib.Core.InformationStructure
import Linglib.Phenomena.FillerGap.Islands.Data

/-!
# Backgrounded Constituents Are Islands

Formalization of the discourse-backgroundedness account of manner-of-speaking
(MoS) island effects, following Lu, Pan & Degen (2025).

## Core Argument

MoS verbs (whisper, shout, etc.) decompose into SAY + MANNER (Erteschik-Shir
2007). The manner component activates a salient alternative set that addresses
the QUD, foregrounding the verb and — by the single-QUD-at-a-time constraint
(Roberts 1996, 2012) — backgrounding the complement. Backgrounded constituents
resist wh-extraction (Goldberg 2006, 2013; Erteschik-Shir 1973), producing the
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
- Rooth FIP / Q-A congruence (`Focus/Interpretation.lean`) = same as QUD cell membership

## References

- Lu, J., Pan, D., & Degen, J. (2025). Evidence for a discourse account of
  manner-of-speaking islands. *Language* 101(4): 627–659.
- Erteschik-Shir, N. (2007). *Information Structure*.
- Goldberg, A.E. (2013). Backgrounded constituents cannot be 'extracted'.
- Roberts, C. (2012). Information structure in discourse.
- Kratzer, A. & Selkirk, E. (2020). Deconstructing Information Structure.
-/

open Core.InformationStructure

namespace Semantics.Focus.BackgroundedIslands

/-! ## §1. Verb Decomposition (Erteschik-Shir 2007)

MoS verbs are lexically composed of a light verb SAY and a manner component:

    whisper = SAY + [whispering manner]
    shout   = SAY + [shouting manner]
    say     = SAY                        (no manner — bridge verb)

The manner component is what makes MoS verbs lexically "heavier" and activates
manner alternatives that can address the QUD. Bridge verbs like *say* lack this
component and so do not activate manner alternatives by default.
-/

/-- A manner-of-speaking component. The specific manner (whispering, shouting,
etc.) is what generates the alternative set: {say in manner m₁, say in manner
m₂, ...}. -/
structure MannerComponent where
  name : String
  deriving DecidableEq, Repr, BEq

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
  deriving DecidableEq, Repr, BEq

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

/-! ## §4. Default QUD Selection: From Verbs to Backgroundedness

MoS verbs, due to their manner component, activate manner alternatives and
make the manner QUD salient by default. Bridge verbs like *say*, lacking a
manner component, default to the content QUD.

This follows from Roberts (1996, 2012): the QUD is determined by what
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

/-! ## §5. The MoS Island Effect: Main Derivation

We derive the island effect from the chain:
  manner weight → manner QUD → content backgrounded → extraction degraded

Each step is proved, and the full chain is stated as a single theorem.
-/

/-- **The Backgroundedness Constraint on Extraction** (Goldberg 2006, 2013;
Erteschik-Shir 1973, 1979; Kuno 1976, 1987):

Backgrounded constituents resist syntactic extraction. The more backgrounded
a constituent, the less acceptable extraction from it.

This is the bridge between information structure and island effects.
The constraint is purely ordinal: given < new < focused. -/
def extractionRank (status : DiscourseStatus) : Fin 3 :=
  match status with
  | .given   => 0  -- backgrounded: most degraded
  | .new     => 1  -- neutral: baseline
  | .focused => 2  -- foregrounded: most acceptable

/-- **MoS Island Effect (Main Theorem)**: MoS verbs default-background their
complements, degrading extraction.

Derivation chain:
1. MoS verb has manner weight (lexical decomposition)
2. Manner weight → default dimension is manner
3. Manner dimension → complement status is .given (backgrounded)
4. Backgrounded → extraction degraded (.given < .new)
-/
theorem mos_island_effect (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    complementStatus (defaultDimension v) = .given := by
  simp only [defaultDimension, h, ite_true, complementStatus]

/-- **Bridge Verb Transparency**: Bridge verbs do NOT produce island effects,
because they lack manner weight → default to content QUD → complement
foregrounded. -/
theorem bridge_verb_transparent (v : VerbDecomp) (h : v.hasMannerWeight = false) :
    complementStatus (defaultDimension v) = .new := by
  simp only [defaultDimension, h, Bool.false_eq_true, ite_false, complementStatus]

/-- Backgrounded extraction is strictly worse than neutral. -/
theorem backgrounded_lt_new :
    extractionRank .given < extractionRank .new := by native_decide

/-- Neutral extraction is strictly worse than focused. -/
theorem new_lt_focused :
    extractionRank .new < extractionRank .focused := by native_decide

/-- The full ordering: given < new < focused. -/
theorem extraction_ordering :
    extractionRank .given < extractionRank .new ∧
    extractionRank .new < extractionRank .focused := by
  constructor <;> native_decide

/-- **Full Derivation**: the complete causal chain from verb decomposition
to extraction prediction, for both MoS and bridge verbs, in a single theorem.

For any communication verb:
- If it has manner weight → complement is backgrounded (given)
- If it lacks manner weight → complement is neutral (new)

Combined with `extraction_ordering`, this yields the acceptability contrast. -/
theorem full_derivation (v : VerbDecomp) :
    (v.hasMannerWeight = true →
      complementStatus (defaultDimension v) = .given) ∧
    (v.hasMannerWeight = false →
      complementStatus (defaultDimension v) = .new) := by
  exact ⟨mos_island_effect v, bridge_verb_transparent v⟩

/-! ## §6. Prosodic Amelioration (Experiments 1 & 3b)

Prosodic focus ([FoC]) on the embedded object overrides the default
backgroundedness, forcing the content QUD and ameliorating the island.

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

/-- Without prosodic focus, MoS verb complements ARE backgrounded. -/
theorem unfocused_mos_complement_backgrounded
    (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    complementStatus (activeDimension v false) = .given := by
  simp [activeDimension, defaultDimension, h, complementStatus]

/-- **Amelioration improves extraction**: Extraction from prosodically focused
complement is better than extraction from default-backgrounded complement. -/
theorem amelioration_improves_extraction :
    extractionRank (complementStatus .content) >
    extractionRank (complementStatus .manner) := by
  native_decide

/-- **Focus sensitivity for MoS verbs**: Prosodic focus changes the extraction
prediction for MoS verbs from degraded (backgrounded) to acceptable (new). -/
theorem mos_focus_sensitivity (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    extractionRank (complementStatus (activeDimension v true)) >
    extractionRank (complementStatus (activeDimension v false)) := by
  simp [activeDimension, defaultDimension, h, complementStatus]
  native_decide

/-! ## §7. Say + Adverb Replication (Experiment 3)

**The paper's key novel prediction**: adding a manner adverb to *say* gives
it manner weight, shifting the default QUD to manner and replicating the
MoS island effect.

    "say softly" = say + manner adverb → manner weight → manner QUD → island
    "say"        = say (no modifier)   → no manner weight → content QUD → no island

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
    extractionRank (complementStatus (defaultDimension sayDecomp)) >
    extractionRank (complementStatus (defaultDimension saySoftlyDecomp)) := by
  native_decide

/-- The say+adverb island is also focus-sensitive (like the MoS island). -/
theorem say_adverb_focus_sensitive :
    extractionRank (complementStatus (activeDimension saySoftlyDecomp true)) >
    extractionRank (complementStatus (activeDimension saySoftlyDecomp false)) := by
  simp [activeDimension, defaultDimension, VerbDecomp.hasMannerWeight,
        saySoftlyDecomp, complementStatus]
  native_decide

/-! ## §8. Theory Comparison

Three accounts of the MoS island effect make different predictions. Only the
backgroundedness account correctly predicts all five experiments' results.
-/

/-- Accounts of the MoS island effect. -/
inductive MoSAccount where
  /-- Structural: MoS verbs select complex-NP complements
  (Stowell 1981, Snyder 1992). -/
  | subjacency
  /-- Processing: low verb-frame frequency → high surprisal
  (Liu et al. 2019, 2022; Kothari 2008). -/
  | verbFrameFrequency
  /-- Discourse: backgrounded complements resist extraction
  (Goldberg 2006, 2013; Erteschik-Shir 1973, 2007). -/
  | backgroundedness
  deriving DecidableEq, Repr, BEq

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
  deriving DecidableEq, Repr, BEq

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

/-- Empirical results from Lu, Pan & Degen (2025). -/
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

/-! ## §9. Grounding in Linglib Infrastructure

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

This connects to Kratzer & Selkirk (2020)'s insight that [FoC] and [G] are
mutually exclusive features — you can't foreground and background the same
dimension simultaneously. Extended here to cross-dimensional complementarity:
foregrounding one dimension of a communication event necessarily backgrounds
the other, given the single-QUD-at-a-time constraint (Roberts 1996). -/
theorem qud_complementarity :
    (verbStatus .manner = .focused ∧ complementStatus .manner = .given) ∧
    (verbStatus .content = .given ∧ complementStatus .content = .new) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- **Backgroundedness = DiscourseStatus.given**: The paper's notion of
"backgrounded" maps directly to Kratzer & Selkirk's [G]-marked status
in the existing K&S 2020 formalization.

This grounds the paper's informal notion of backgroundedness in the
formal two-feature system already in the codebase. -/
theorem backgroundedness_is_given :
    complementStatus .manner = DiscourseStatus.given := rfl

/-- **Foregrounding = DiscourseStatus.focused**: The paper's notion of
"foregrounded" maps to Kratzer & Selkirk's [FoC]-marked status. -/
theorem foregrounding_is_focused :
    verbStatus .manner = DiscourseStatus.focused := rfl

/-! ## §10. Bridge to Island Classification

These theorems connect the formal backgroundedness model to the shared
island infrastructure in `Phenomena/Islands/Data.lean`. The MoS island
is classified as weak (ameliorable) and discourse-sourced, and we
derive both properties from the formal model.
-/

/-- **Discourse source derivation**: The formal model predicts that MoS islands
are discourse-sourced because the island effect arises from QUD-determined
backgroundedness, not syntactic configuration or processing load.

The classification `constraintSource .mannerOfSpeaking = .discourse` is not
stipulated arbitrarily — it follows from the formal model: the island effect
is predicted by `complementStatus (defaultDimension v)` which depends on
QUD selection (information structure), not syntax or processing. -/
theorem discourse_source_from_model :
    -- The formal model derives backgroundedness from QUD (discourse)
    (complementStatus .manner = .given) ∧
    -- This grounds the discourse classification
    (constraintSource .mannerOfSpeaking = .discourse) := ⟨rfl, rfl⟩

/-- **Weak classification derivation**: The formal model predicts that MoS
islands are weak (ameliorable) because prosodic focus overrides the default
QUD, changing the complement from backgrounded to discourse-new.

The classification `constraintStrength .mannerOfSpeaking = .weak` follows
from the existence of `prosodic_focus_ameliorates`. -/
theorem weak_strength_from_model (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    -- Without focus: backgrounded (island)
    complementStatus (activeDimension v false) = .given ∧
    -- With focus: not backgrounded (ameliorated)
    complementStatus (activeDimension v true) = .new ∧
    -- Classification matches
    constraintStrength .mannerOfSpeaking = .weak := by
  refine ⟨?_, ?_, rfl⟩
  · simp [activeDimension, defaultDimension, h, complementStatus]
  · simp [activeDimension, complementStatus]

/-- **MoS islands are unique among island types**: they are the only islands
whose effect is derived from information structure (discourse source)
rather than syntactic configuration.

This makes a testable prediction: any manipulation that changes the
QUD (not just prosodic focus) should ameliorate MoS islands, but
manipulations that don't change the QUD (like D-linking) should not. -/
theorem mos_unique_discourse_source :
    constraintSource .mannerOfSpeaking = .discourse ∧
    constraintSource .embeddedQuestion = .syntactic ∧
    constraintSource .complexNP = .syntactic ∧
    constraintSource .adjunct = .syntactic ∧
    constraintSource .coordinate = .syntactic ∧
    constraintSource .subject = .syntactic ∧
    constraintSource .sententialSubject = .syntactic := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Semantics.Focus.BackgroundedIslands
