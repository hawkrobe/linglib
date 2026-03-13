import Linglib.Theories.Semantics.Causation.MorphologicalCausation
import Linglib.Theories.Semantics.Lexical.Verb.EventStructure
import Linglib.Theories.Semantics.Lexical.Verb.ArgDerivation
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# @cite{krejci-2012} — Lexical Reflexivity and the Ingestive/Middle Class

Krejci, Bonnie. 2012. *The Event Structural Properties of the Transitive
Alternation: A Cross-Linguistic Study*. Master's Report, University of
Texas at Austin.

## Core claims

1. **Lexically reflexive verbs** (eat, wash, dress, learn) have bieventive,
   causative event structure in their *simple* forms:
   `[[ACT(x)] CAUSE [BECOME ⟨STATE⟩ (x, y)]]` with causer = causee.
   All four bieventivity diagnostics confirm this (§4.3–4.4).

2. Two subtypes: **middles** (wash, dress) where the agent acts on their
   own body, and **ingestives** (eat, drink) where the agent acts on a
   consumed substance directed at themselves. Both are lexically reflexive.
   `learn` is proposed as a "metaphorical ingestive" (§4.2.4).

3. Four diagnostics — *again* ambiguity, *re-* prefixation, *almost*
   ambiguity, and negation over CAUSE — all detect bieventive structure
   in the simple forms of these verbs. All diagnostic data is for English.

4. **Antireflexivization**: the lexical causatives of these verbs
   (eat→feed, learn→teach) are derived by splitting the coidentified
   causer-causee argument into two distinct participants (§4.2).

5. The **causativizability hierarchy** — unaccusatives > middles/ingestives
   > unergatives > simple transitives — is validated across 12 languages
   (Table 2.8). This data is formalized in
   `MorphologicalCausation.krejciLanguages`.

## Bridges

- `eat_is_causativeResult` → `LevinClass.rootEntailments` (root typology)
- `eat_licenses_accomplishment` → `rootLicensesTemplate` (ArgDerivation)
- `eat_argTemplate_is_consumption` → `LevinClass.argTemplate` (LevinClassProfiles)
- `alternation_strips_cause` → `Template.intransitiveVariant`
- `anticausative_no_theta` / `middle_no_theta` → `VoiceHead` (Minimalist syntax)
-/

namespace Phenomena.Causation.Studies.Krejci2012

open Semantics.Causation.MorphologicalCausation
open Semantics.Lexical.Verb.EventStructure
open Semantics.Lexical.Verb.ArgDerivation

-- ════════════════════════════════════════════════════
-- § 1. Lexically Reflexive Verb Data
-- ════════════════════════════════════════════════════

/-- Subtype of lexically reflexive verb (§4.1–4.2). -/
inductive LexReflexiveSubtype where
  /-- Middles: agent acts on own body (wash, dress).
      @cite{kemmer-1994}: one internally complex participant. -/
  | middle
  /-- Ingestives: agent causes substance to enter self (eat, drink).
      Includes "metaphorical ingestives" (learn). -/
  | ingestive
  deriving DecidableEq, BEq, Repr

/-- A lexically reflexive verb: a verb whose simple form has bieventive
    causative event structure with coidentified causer and causee.

    The four bieventivity diagnostics (§4.3–4.4) test for complex
    internal structure — the presence of distinct sub-events connected
    by CAUSE that scopal modifiers can target independently:

    - **again**: restitutive (result state restored) + repetitive (whole event repeated)
    - **re-**: restitutive reading with *re-* prefix
    - **almost**: scope over action sub-event vs. result sub-event
    - **negation over CAUSE**: deny simple form while asserting causative variant -/
structure LexReflexiveVerb where
  gloss : String
  subtype : LexReflexiveSubtype
  /-- Lexical causative counterpart (antireflexivized form).
      `none` when the verb uses the same form transitively (wash, dress). -/
  lexicalCausative : Option String
  /-- Does postverbal *again* produce restitutive + repetitive readings? -/
  againAmbiguity : Bool
  /-- Does *re-* prefixation produce a restitutive reading? -/
  rePrefixation : Bool
  /-- Does *almost* produce scope ambiguity over sub-events? -/
  almostAmbiguity : Bool
  /-- Can the simple form be negated while asserting the causative variant? -/
  negationOverCause : Bool
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. English Diagnostic Data (§4.2–4.4)
-- ════════════════════════════════════════════════════

/-! All diagnostic data is from English. @cite{krejci-2012} tests four
    verbs — eat, wash, dress, learn — each representing a subtype of the
    lexically reflexive class. All four pass all four diagnostics. -/

/-- *eat*: ingestive. `[[ACT⟨manipulate food⟩(x)] CAUSE [BECOME ⟨potentially digest⟩ (x, y)]]`.
    Lexical causative: *feed* (§4.2.1). -/
def eat : LexReflexiveVerb :=
  { gloss := "eat"
    subtype := .ingestive
    lexicalCausative := some "feed"
    againAmbiguity := true       -- (70) "Your guy ate the coin again..."
    rePrefixation := true         -- (76–77) "re-eat" attested, restitutive available
    almostAmbiguity := true       -- (85) "John almost ate the pie"
    negationOverCause := true }   -- (92) "I didn't eat pie; you fed me pie!"

/-- *wash*: middle. `[[ACT⟨manipulate water⟩(x)] CAUSE [BECOME ⟨washed⟩ (x)]]`.
    Transitive *wash (someone)* is the antireflexivized form (§4.2.2). -/
def wash : LexReflexiveVerb :=
  { gloss := "wash"
    subtype := .middle
    lexicalCausative := none  -- same form used transitively
    againAmbiguity := true       -- (71) "John washed again..."
    rePrefixation := true         -- (78–79) "re-wash" attested
    almostAmbiguity := true       -- (86) "John almost washed"
    negationOverCause := true }   -- §4.4: parallel to eat

/-- *dress*: middle. `[[ACT⟨manipulate clothes⟩(x)] CAUSE [BECOME ⟨dressed⟩ (x)]]`.
    Transitive *dress (someone)* is the antireflexivized form (§4.2.3). -/
def dress : LexReflexiveVerb :=
  { gloss := "dress"
    subtype := .middle
    lexicalCausative := none  -- same form used transitively
    againAmbiguity := true       -- (72) "John dressed again..."
    rePrefixation := true         -- (80–81) "re-dress" attested
    almostAmbiguity := true       -- (87) "John almost dressed"
    negationOverCause := true }   -- §4.4: parallel to eat

/-- *learn*: proposed metaphorical ingestive.
    `[[ACT(x)] CAUSE [BECOME ⟨know⟩ (x, y)]]`.
    Lexical causative: *teach* (§4.2.4). -/
def learn : LexReflexiveVerb :=
  { gloss := "learn"
    subtype := .ingestive
    lexicalCausative := some "teach"
    againAmbiguity := true       -- (73) "John learned English again..."
    rePrefixation := true         -- (82) "John re-learned English..."
    almostAmbiguity := true       -- (88) "John almost learned French"
    negationOverCause := true }   -- §4.4: parallel to eat

def allVerbs : List LexReflexiveVerb :=
  [eat, wash, dress, learn]

-- ════════════════════════════════════════════════════
-- § 3. Per-Datum Verification
-- ════════════════════════════════════════════════════

/-- All four verbs pass the *again* ambiguity diagnostic. -/
theorem all_again : allVerbs.all (·.againAmbiguity) = true := by native_decide

/-- All four verbs pass the *re-* prefixation diagnostic. -/
theorem all_re : allVerbs.all (·.rePrefixation) = true := by native_decide

/-- All four verbs pass the *almost* ambiguity diagnostic. -/
theorem all_almost : allVerbs.all (·.almostAmbiguity) = true := by native_decide

/-- All four verbs pass the negation-over-CAUSE diagnostic. -/
theorem all_negation : allVerbs.all (·.negationOverCause) = true := by native_decide

/-- All four diagnostics pass for every verb in the dataset:
    the simple forms of eat, wash, dress, and learn are bieventive. -/
theorem all_bieventive :
    allVerbs.all (λ v =>
      v.againAmbiguity && v.rePrefixation &&
      v.almostAmbiguity && v.negationOverCause) = true := by native_decide

/-- Middles and ingestives are both represented. -/
theorem both_subtypes :
    allVerbs.any (·.subtype == .middle) = true ∧
    allVerbs.any (·.subtype == .ingestive) = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Antireflexivization (§4.2)
-- ════════════════════════════════════════════════════

/-! @cite{krejci-2012}'s central operation: the lexical causative of a
    lexically reflexive verb is derived by **antireflexivization** —
    splitting the coidentified causer-causee into two distinct
    participants.

    Reflexive form (eat):
      `[[ACT⟨manipulate food⟩(x)] CAUSE [BECOME ⟨potentially digest⟩ (x, y)]]`
      — one participant (x) is both causer and causee.

    Antireflexive form (feed):
      `[[ACT⟨manipulate food⟩(x)] CAUSE [BECOME ⟨potentially digest⟩ (y, z)]]`
      — causer (x) and causee (y) are distinct participants.

    Key evidence (§4.2.1): with *eat*, the eater must agentively
    manipulate food; with *feed*, this entailment shifts to the feeder.
    With *make eat* (syntactic causative), the eater retains the
    manipulation entailment. This shows *feed* ≠ *make eat*: the lexical
    and syntactic causatives have different event structures. -/

/-- An antireflexive pair: a lexically reflexive verb and its
    suppletive lexical causative. Only verbs with a distinct lexical
    causative form have such pairs (eat→feed, learn→teach).
    Middles (wash, dress) use the same form transitively — the
    antireflexivization is structural, not morphological. -/
structure AntireflexivePair where
  reflexive : String
  causative : String
  deriving Repr, BEq

def eatFeed : AntireflexivePair := ⟨"eat", "feed"⟩
def learnTeach : AntireflexivePair := ⟨"learn", "teach"⟩

/-- The suppletive pairs are derivable from the verb data. -/
theorem eat_causative : eat.lexicalCausative = some "feed" := rfl
theorem learn_causative : learn.lexicalCausative = some "teach" := rfl

/-- Middles use the same form transitively (no suppletive pair). -/
theorem wash_same_form : wash.lexicalCausative = none := rfl
theorem dress_same_form : dress.lexicalCausative = none := rfl

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Root Dimensions
-- ════════════════════════════════════════════════════

/-! @cite{krejci-2012}'s claim that eat and dress have causative event
    structure aligns with their `RootEntailments` classification:
    both are `causativeResult` (state + result + cause), meaning the
    root itself entails external causation. -/

/-- eat roots are causativeResult: the root entails caused consumption. -/
theorem eat_is_causativeResult :
    LevinClass.rootEntailments .eat = .causativeResult := rfl

/-- dress roots are causativeResult: the root entails caused dressed state. -/
theorem dress_is_causativeResult :
    LevinClass.rootEntailments .dress = .causativeResult := rfl

/-- causativeResult roots entail cause — consistent with
    @cite{krejci-2012}'s analysis that these verbs have CAUSE in their
    simple forms. -/
theorem causativeResult_entails_cause :
    RootEntailments.causativeResult.cause = true := rfl

-- ════════════════════════════════════════════════════
-- § 6. Bridge to ArgDerivation
-- ════════════════════════════════════════════════════

/-! The root→template pipeline predicts that eat and dress roots
    license the accomplishment template (since they entail causation).
    The accomplishment template in turn has an intransitive variant
    (achievement). But eat/dress do NOT undergo the standard
    causative/inchoative alternation (*"The food ate", *"The clothes
    dressed") — the root's obligatory agentive entailments block it.

    Instead, the causativization operation is antireflexivization:
    splitting a coidentified participant, not adding a new external
    cause. -/

/-- eat roots license the accomplishment template. -/
theorem eat_licenses_accomplishment :
    rootLicensesTemplate (LevinClass.rootEntailments .eat) .accomplishment = true := rfl

/-- eat's primary template is accomplishment. -/
theorem eat_primary_accomplishment :
    primaryTemplate (LevinClass.rootEntailments .eat) = some .accomplishment := rfl

/-- eat's ArgTemplate is `consumption` (agent + incremental theme). -/
theorem eat_argTemplate_is_consumption :
    LevinClass.argTemplate .eat =
    some Semantics.Lexical.Verb.LevinClassProfiles.consumption := rfl

/-- The accomplishment template has an intransitive variant (achievement).
    This is the template-level possibility that eat/dress *could* alternate
    — but root semantics blocks it. -/
theorem accomplishment_has_variant :
    Template.intransitiveVariant .accomplishment = some .achievement := rfl

/-- causativeResult roots derive 3 ArgTemplates (state, achievement,
    accomplishment). The template infrastructure predicts alternation;
    the blocking is root-level, not template-level. -/
theorem eat_root_alternation_possible :
    (licensedTemplates (LevinClass.rootEntailments .eat)).length = 3 := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to Event Structure
-- ════════════════════════════════════════════════════

/-- The intransitive variant retains the result state
    (the BECOME sub-event persists). -/
theorem alternation_preserves_result :
    Template.hasResultState .achievement = true := rfl

/-- The intransitive variant loses CAUSE. -/
theorem alternation_loses_cause :
    Template.hasCause .achievement = false := rfl

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Minimalist Voice
-- ════════════════════════════════════════════════════

/-! @cite{krejci-2012}'s reflexive/anticausative distinction maps onto
    the Voice typology in Minimalism: reflexive intransitives correspond
    to middle Voice (bieventive, coidentification), and true
    anticausatives correspond to anticausative Voice (monoeventive,
    cause removed). Both lack an external argument in Spec,VoiceP. -/

/-- Anticausative Voice does not assign a θ-role (no external argument). -/
theorem anticausative_no_theta :
    Minimalism.voiceAnticausative.assignsTheta = false := rfl

/-- Middle Voice does not assign a θ-role. -/
theorem middle_no_theta :
    Minimalism.voiceMiddle.assignsTheta = false := rfl

-- ════════════════════════════════════════════════════
-- § 9. Cross-Linguistic Causativizability
-- ════════════════════════════════════════════════════

/-! @cite{krejci-2012} Table 2.8 validates the causativizability
    hierarchy across 12 languages. This data is formalized in
    `MorphologicalCausation.krejciLanguages` and verified by
    `MorphologicalCausation.krejci_hierarchy_holds`.

    The hierarchy is implicational:
    unaccusatives > middles/ingestives > unergatives > simple transitives

    The key contribution is establishing middles/ingestives as a
    distinct tier: Type 1 languages (Slave, Mapudungun, Classical
    Nahuatl) causativize only unaccusatives; Type 2 (Cora, Marathi,
    Amharic) add middles/ingestives; Type 3 (Ahtna, Tariana, Malayalam)
    add unergatives; Type 4 (Basque, Dulong/Rawang, Koyukon) add simple
    transitives. No language skips tiers. -/

/-- The causativizability hierarchy holds for all 12 languages. -/
theorem hierarchy_holds :
    krejciLanguages.all (·.respectsHierarchy) = true := by native_decide

end Phenomena.Causation.Studies.Krejci2012
