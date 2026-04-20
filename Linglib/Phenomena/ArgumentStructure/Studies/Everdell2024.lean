import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Phenomena.ArgumentStructure.Studies.Pylkkanen2008

/-!
# @cite{everdell-2023} — Applicativization in O'dam (Southeastern Tepiman)

Everdell, Michael. 2023. *Arguments and adjuncts in O'dam:
language-specific realization of a cross-linguistic distinction*. PhD
dissertation, University of Texas at Austin.

Chapter 5 formalizes O'dam applicativization, which provides evidence
that thematic hierarchies cannot be fully eliminated from argument
realization theory — a key counterpoint to purely content-based
linking (MAP alone).

## Core claims

1. **O'dam has two applicative suffixes**: *-dha* and *-tuda*, which are
   specific about which verbs they combine with and which function they
   serve. Unlike Kinyarwanda *-ish*, O'dam applicatives are **unambiguous**
   in their function with a given verb.

2. **Thematic hierarchy of applied arguments** (the dissertation's (273)):

       Agent > Promoted object [+ANIM] > Beneficiary

   The applied argument's thematic role is hierarchically determined:
   agent-introduction takes priority over promotion, which takes
   priority over beneficiary introduction. Beneficiary is the
   **elsewhere** case.

3. **Applicative function is predictable** from two properties of the
   base verb: (a) its transitivity and (b) its semantic participants.

4. **Animacy entailment** is the consistent semantic contribution of
   promotion. Unlike Kinyarwanda (which adds change-of-possession),
   O'dam promotion simply adds an animacy entailment to the promoted
   participant. Benefactive/malefactive inferences are pragmatic.

5. **Applicativization is a valency test**: the applied form always has
   valency = base valency + 1. This explains the **hypertransitivity
   ban**: ditransitives (*makia'* 'give', *tikka'* 'ask') cannot be
   applicativized because O'dam caps syntactic arguments at three.

6. **Locatives are always adjuncts**: they don't count toward
   transitivity, evidenced by motion verbs behaving as intransitives
   under applicativization.

7. **Instruments are always adjuncts AND always inanimate**: they
   cannot be promoted because promotion requires animacy, and
   instruments in O'dam are categorically inanimate.

## Cross-references

- `Studies/Pylkkanen2008.lean`: O'dam applicatives don't fit the
  high/low dichotomy cleanly — they perform agent-introduction
  (high-like), promotion, AND beneficiary licensing depending
  on the base verb.
- `Studies/Beavers2010.lean`: The affectedness hierarchy and MAP
  operate on direct/oblique alternations. O'dam shows a *different*
  dimension of argument realization: thematic hierarchies governing
  which participant gets promoted by an applicative.
- `Studies/BeaversUdayana2022.lean`: Indonesian *ber-* middles
  suppress arguments; O'dam *-dha* and *-tuda* ADD arguments. Both
  are valency operations that probe base argument structure.
-/

namespace Everdell2024

-- ════════════════════════════════════════════════════
-- § 1. O'dam Verb Properties
-- ════════════════════════════════════════════════════

/-- Base transitivity of an O'dam verb.
    Everdell's analysis treats motion verbs with only a locative
    participant as intransitive (the locative is an adjunct). -/
inductive BaseTransitivity where
  | intransitive   -- One syntactic argument (patient-subject or agent-subject)
  | transitive     -- Two syntactic arguments (subject + primary object)
  | ditransitive   -- Three syntactic arguments (subject + 2 objects)
  deriving DecidableEq, Repr

/-- The type of non-argument entailed participant (if any) that a
    transitive verb has. These are participants entailed by the verb's
    semantics but NOT syntactic arguments of the base form. -/
inductive EntailedParticipantType where
  | implicitObject    -- Entailed but not expressible (e.g., *ga'ra'* 'sell' entails buyer)
  | locative          -- Entailed location (goal, source, or container)
  | instrument        -- Entailed instrument (always inanimate, always adjunct)
  | none              -- No relevant entailed non-argument participant
  deriving DecidableEq, Repr

/-- Whether a locative participant is compatible with an animate referent.
    This determines whether the locative can be promoted by an applicative,
    since promotion requires adding an animacy entailment. -/
inductive AnimateCompatibility where
  | compatible        -- Locative can be animate (goal of motion, etc.)
  | incompatible      -- Locative resists animate interpretation (container, surface)
  deriving DecidableEq, Repr

/-- Semantic class of an O'dam verb, relevant to applicativization. -/
inductive VerbClass where
  | unaccusative       -- Patient-subject: *tuklhia'* 'blacken.INTR'
  | unergative         -- Agent-subject: *koxia'* 'sleep'
  | motionIntransitive -- Motion verb with locative adjunct: *aaya'* 'arrive'
  | ingestion          -- Eating/drinking: *bha'ya'* 'swallow'
  | perception         -- Seeing/hearing: *tigia'* 'see', *kaaya'* 'hear'
  | lexicalMiddle      -- Subject ≈ object: *saabu'* 'fast', *namkia'* 'meet'
  | simpleTransitive   -- Canonical agent-patient: *mu'kda'* 'sharpen'
  | denominalCreation  -- Incorporated object in base: *junmada'* 'make mole'
  | ditransitive       -- Three-argument base: *makia'* 'give', *tikka'* 'ask'
  deriving DecidableEq, Repr

/-- An O'dam verb entry for applicativization analysis. -/
structure OdamVerb where
  /-- Base form (citation) -/
  baseForm : String
  /-- Gloss -/
  gloss : String
  /-- Applied form (with *-dha* or *-tuda*) -/
  appliedForm : String
  /-- Verb class -/
  verbClass : VerbClass
  /-- Syntactic transitivity of the base form -/
  transitivity : BaseTransitivity
  /-- Type of entailed non-argument participant (if any) -/
  entailedParticipant : EntailedParticipantType
  /-- Whether the locative (if any) is compatible with an animate referent -/
  animateLocative : AnimateCompatibility := .incompatible
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Applicative Function
-- ════════════════════════════════════════════════════

/-- The function an O'dam applicative performs with a given verb.

    These are ordered by the thematic hierarchy (273):
    Agent > Promoted object [+ANIM] > Beneficiary.

    `blocked` covers the hypertransitivity ban (ditransitives). -/
inductive ApplFunction where
  | agentIntroduction    -- Adds external agent/causer (intransitive bases)
  | promotion            -- Promotes entailed non-argument to core argument [+ANIM]
  | beneficiary          -- Introduces beneficiary (elsewhere case)
  | blocked              -- Cannot applicativize (ditransitives)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Predicting Applicative Function (the core algorithm)
-- ════════════════════════════════════════════════════

/-- **The central prediction**: the applicative's function is determined
    by the base verb's transitivity and entailed participants.

    This implements Everdell's thematic hierarchy (273):
    1. If the base is intransitive → agent introduction
    2. If the base is transitive AND has a promotable participant → promotion
    3. If the base is transitive AND has no promotable participant → beneficiary
    4. If the base is ditransitive → blocked

    A participant is "promotable" if it is either:
    - An implicit object (not expressible in base form), OR
    - A locative compatible with an animate interpretation

    Instruments are NEVER promotable: they are inanimate in O'dam,
    and promotion adds an animacy entailment. -/
def predictFunction (v : OdamVerb) : ApplFunction :=
  match v.transitivity with
  | .intransitive => .agentIntroduction
  | .ditransitive => .blocked
  | .transitive =>
    match v.entailedParticipant with
    | .implicitObject => .promotion
    | .locative =>
      match v.animateLocative with
      | .compatible => .promotion
      | .incompatible => .beneficiary
    | .instrument => .beneficiary
    | .none => .beneficiary

/-- "Exceptional transitives" (ingestion, perception, lexical middles)
    are syntactically transitive but pattern with intransitives under
    applicativization because their subject is not maximally distinct
    from the object.

    This function computes the **effective transitivity** for
    applicativization purposes. -/
def effectiveTransitivity (v : OdamVerb) : BaseTransitivity :=
  match v.verbClass with
  | .ingestion | .perception | .lexicalMiddle => .intransitive
  | _ => v.transitivity

/-- The refined prediction accounting for exceptional transitives. -/
def predictFunctionRefined (v : OdamVerb) : ApplFunction :=
  let effV := { v with transitivity := effectiveTransitivity v }
  predictFunction effV

-- ════════════════════════════════════════════════════
-- § 4. Verb Data — Intransitives (Table 5.1, selection)
-- ════════════════════════════════════════════════════

def tuklhia : OdamVerb :=
  { baseForm := "tuklhia'", gloss := "blacken.INTR"
  , appliedForm := "tuk-chuda'", verbClass := .unaccusative
  , transitivity := .intransitive, entailedParticipant := .none }

def koxia : OdamVerb :=
  { baseForm := "koxia'", gloss := "sleep"
  , appliedForm := "kox-chuda'", verbClass := .unergative
  , transitivity := .intransitive, entailedParticipant := .none }

def miiya_burn : OdamVerb :=
  { baseForm := "miiya'", gloss := "burn.INTR"
  , appliedForm := "mii-dha'", verbClass := .unaccusative
  , transitivity := .intransitive, entailedParticipant := .none }

def miiya_ignite : OdamVerb :=
  { baseForm := "miiya'", gloss := "ignite.INTR"
  , appliedForm := "mii-chdha'", verbClass := .unaccusative
  , transitivity := .intransitive, entailedParticipant := .none }

def tisdia : OdamVerb :=
  { baseForm := "tisdia'", gloss := "climb"
  , appliedForm := "tisaa'ñ-dha'", verbClass := .motionIntransitive
  , transitivity := .intransitive, entailedParticipant := .none }

def aaya : OdamVerb :=
  { baseForm := "aaya'", gloss := "arrive"
  , appliedForm := "ai-chdha'", verbClass := .motionIntransitive
  , transitivity := .intransitive, entailedParticipant := .none }

def kikbo : OdamVerb :=
  { baseForm := "kikbo'", gloss := "stand up"
  , appliedForm := "kikbui-chdha'", verbClass := .unaccusative
  , transitivity := .intransitive, entailedParticipant := .none }

-- ════════════════════════════════════════════════════
-- § 5. Verb Data — Exceptional Transitives (Table 5.2)
-- ════════════════════════════════════════════════════

/-- Ingestion verbs: syntactically transitive but applicativize like
    intransitives because subject is not maximally distinct from object. -/
def bhaya_swallow : OdamVerb :=
  { baseForm := "bha'ya'", gloss := "swallow"
  , appliedForm := "bhai'-chdha'", verbClass := .ingestion
  , transitivity := .transitive, entailedParticipant := .none }

def iya_drink : OdamVerb :=
  { baseForm := "i'ya'", gloss := "drink"
  , appliedForm := "ii-chdha'", verbClass := .ingestion
  , transitivity := .transitive, entailedParticipant := .none }

/-- Perception verbs: also transitive but pattern intransitively. -/
def tigia_see : OdamVerb :=
  { baseForm := "tigia'", gloss := "see"
  , appliedForm := "tiiñxi-dha'", verbClass := .perception
  , transitivity := .transitive, entailedParticipant := .none }

def kaaya_hear : OdamVerb :=
  { baseForm := "kaaya'", gloss := "hear"
  , appliedForm := "kai-dha'", verbClass := .perception
  , transitivity := .transitive, entailedParticipant := .none }

/-- Lexical middles: subject and object are co-identified. -/
def saabu_fast : OdamVerb :=
  { baseForm := "saabu'", gloss := "fast"
  , appliedForm := "saab-tuda'", verbClass := .lexicalMiddle
  , transitivity := .transitive, entailedParticipant := .none }

def namkia_meet : OdamVerb :=
  { baseForm := "namkia'", gloss := "meet"
  , appliedForm := "namki-chdha'", verbClass := .lexicalMiddle
  , transitivity := .transitive, entailedParticipant := .none }

def tulhiina_suffer : OdamVerb :=
  { baseForm := "tulhiiña'", gloss := "suffer"
  , appliedForm := "tulhiiñ-chuda'", verbClass := .lexicalMiddle
  , transitivity := .transitive, entailedParticipant := .none }

def oncho_hide : OdamVerb :=
  { baseForm := "o'ñcho'", gloss := "hide (animate subject)"
  , appliedForm := "o'ñxi-dha'", verbClass := .lexicalMiddle
  , transitivity := .transitive, entailedParticipant := .none }

-- ════════════════════════════════════════════════════
-- § 6. Verb Data — Transitives with Promotion (§5.2–5.3)
-- ════════════════════════════════════════════════════

/-- Verbs with implicit objects (promoted by applicative). -/
def gara_sell : OdamVerb :=
  { baseForm := "ga'ra'", gloss := "sell"
  , appliedForm := "ga'lhi-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .implicitObject }

def jotsa_send : OdamVerb :=
  { baseForm := "jotsa'", gloss := "send"
  , appliedForm := "jotxi-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .locative
  , animateLocative := .compatible }

def aga_say : OdamVerb :=
  { baseForm := "aga'", gloss := "say"
  , appliedForm := "ag-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .implicitObject }

/-- Verbs with locative participants compatible with animate referents
    (promoted to object with animacy entailment). -/
def bua_throw : OdamVerb :=
  { baseForm := "bua'", gloss := "throw.SG"
  , appliedForm := "bui-'ñ", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .locative
  , animateLocative := .compatible }

def baabu_take_out : OdamVerb :=
  { baseForm := "baabu'", gloss := "take out (from under)"
  , appliedForm := "baabui-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .locative
  , animateLocative := .compatible }

def nuina_push : OdamVerb :=
  { baseForm := "nui'ña'", gloss := "push"
  , appliedForm := "nui'ñ-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .locative
  , animateLocative := .compatible }

-- ════════════════════════════════════════════════════
-- § 7. Verb Data — Transitives with Beneficiary (§5.4)
-- ════════════════════════════════════════════════════

def mukda_sharpen : OdamVerb :=
  { baseForm := "mu'kda'", gloss := "sharpen"
  , appliedForm := "mu'kxi-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .none }

def sooma_sew : OdamVerb :=
  { baseForm := "sooma'", gloss := "sew"
  , appliedForm := "soom-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .none }

def sarna_tear : OdamVerb :=
  { baseForm := "sarna'", gloss := "tear, rip"
  , appliedForm := "sarni-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .none }

def uana_clean : OdamVerb :=
  { baseForm := "uana'", gloss := "clean"
  , appliedForm := "uañ-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .none }

def uana_write : OdamVerb :=
  { baseForm := "ua'na'", gloss := "write"
  , appliedForm := "ua'ñxi-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .none }

/-- Transitive with entailed instrument (not promotable). -/
def kuagia_cut_firewood : OdamVerb :=
  { baseForm := "kua'gia'", gloss := "cut firewood"
  , appliedForm := "kua'ñ-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .instrument }

def bulhia_tie : OdamVerb :=
  { baseForm := "bulhia'", gloss := "tie, fasten"
  , appliedForm := "bulh-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .instrument }

/-- Transitive with locative incompatible with animate referent. -/
def bakta_hang : OdamVerb :=
  { baseForm := "bakta'", gloss := "hang up (to dry)"
  , appliedForm := "bakxi-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .locative
  , animateLocative := .incompatible }

def gammu_put_inside : OdamVerb :=
  { baseForm := "gammu'", gloss := "put inside (sack or bag)"
  , appliedForm := "gaam-dha'", verbClass := .simpleTransitive
  , transitivity := .transitive, entailedParticipant := .locative
  , animateLocative := .incompatible }

-- ════════════════════════════════════════════════════
-- § 8. Verb Data — Ditransitives (blocked)
-- ════════════════════════════════════════════════════

def makia_give : OdamVerb :=
  { baseForm := "makia'", gloss := "give"
  , appliedForm := "*maki-dha'", verbClass := .ditransitive
  , transitivity := .ditransitive, entailedParticipant := .none }

def tikka_ask : OdamVerb :=
  { baseForm := "tikka'", gloss := "ask"
  , appliedForm := "*tikki-dha'", verbClass := .ditransitive
  , transitivity := .ditransitive, entailedParticipant := .none }

-- ════════════════════════════════════════════════════
-- § 9. Verb Data — Denominal Creation Verbs
-- ════════════════════════════════════════════════════

/-- Denominal verbs of creation: syntactically transitive (they take
    the resultative *-xim*) but gain a beneficiary, not an agent.
    The incorporated noun satisfies one thematic role. -/
def junmada_make_mole : OdamVerb :=
  { baseForm := "junmada'", gloss := "make mole (food)"
  , appliedForm := "junmax-dha", verbClass := .denominalCreation
  , transitivity := .transitive, entailedParticipant := .none }

-- ════════════════════════════════════════════════════
-- § 10. Verification: predictFunction matches observed behavior
-- ════════════════════════════════════════════════════

-- ── Intransitives → agent introduction ──

theorem tuklhia_gains_agent :
    predictFunction tuklhia = .agentIntroduction := rfl

theorem koxia_gains_agent :
    predictFunction koxia = .agentIntroduction := rfl

theorem miiya_burn_gains_agent :
    predictFunction miiya_burn = .agentIntroduction := rfl

theorem tisdia_gains_agent :
    predictFunction tisdia = .agentIntroduction := rfl

theorem aaya_gains_agent :
    predictFunction aaya = .agentIntroduction := rfl

theorem kikbo_gains_agent :
    predictFunction kikbo = .agentIntroduction := rfl

-- ── Exceptional transitives → agent via refined prediction ──

/-- Ingestion: syntactically transitive, but the refined predictor
    recognizes it as effectively intransitive. -/
theorem bhaya_refined_agent :
    predictFunctionRefined bhaya_swallow = .agentIntroduction := rfl

theorem iya_refined_agent :
    predictFunctionRefined iya_drink = .agentIntroduction := rfl

/-- Perception: same pattern. -/
theorem tigia_refined_agent :
    predictFunctionRefined tigia_see = .agentIntroduction := rfl

theorem kaaya_refined_agent :
    predictFunctionRefined kaaya_hear = .agentIntroduction := rfl

/-- Lexical middles: same pattern. -/
theorem saabu_refined_agent :
    predictFunctionRefined saabu_fast = .agentIntroduction := rfl

theorem namkia_refined_agent :
    predictFunctionRefined namkia_meet = .agentIntroduction := rfl

theorem tulhiina_refined_agent :
    predictFunctionRefined tulhiina_suffer = .agentIntroduction := rfl

theorem oncho_refined_agent :
    predictFunctionRefined oncho_hide = .agentIntroduction := rfl

/-- The naive predictor gets exceptional transitives WRONG — it would
    predict beneficiary, not agent. This motivates the refined predictor. -/
theorem naive_wrong_for_exceptionals :
    predictFunction bhaya_swallow = .beneficiary ∧
    predictFunction tigia_see = .beneficiary ∧
    predictFunction saabu_fast = .beneficiary := ⟨rfl, rfl, rfl⟩

-- ── Transitives with promotable participants → promotion ──

theorem gara_promotes :
    predictFunction gara_sell = .promotion := rfl

theorem jotsa_promotes :
    predictFunction jotsa_send = .promotion := rfl

theorem aga_promotes :
    predictFunction aga_say = .promotion := rfl

theorem bua_promotes :
    predictFunction bua_throw = .promotion := rfl

theorem baabu_promotes :
    predictFunction baabu_take_out = .promotion := rfl

theorem nuina_promotes :
    predictFunction nuina_push = .promotion := rfl

-- ── Transitives without promotable participants → beneficiary ──

theorem mukda_gets_beneficiary :
    predictFunction mukda_sharpen = .beneficiary := rfl

theorem sooma_gets_beneficiary :
    predictFunction sooma_sew = .beneficiary := rfl

theorem sarna_gets_beneficiary :
    predictFunction sarna_tear = .beneficiary := rfl

theorem uana_gets_beneficiary :
    predictFunction uana_clean = .beneficiary := rfl

theorem uana_write_gets_beneficiary :
    predictFunction uana_write = .beneficiary := rfl

-- ── Instruments → beneficiary (because instruments can't be promoted) ──

theorem kuagia_instrument_not_promoted :
    predictFunction kuagia_cut_firewood = .beneficiary := rfl

theorem bulhia_instrument_not_promoted :
    predictFunction bulhia_tie = .beneficiary := rfl

-- ── Inanimate locatives → beneficiary (can't add animacy) ──

theorem bakta_inanimate_loc_not_promoted :
    predictFunction bakta_hang = .beneficiary := rfl

theorem gammu_inanimate_loc_not_promoted :
    predictFunction gammu_put_inside = .beneficiary := rfl

-- ── Denominal creation (transitive base) → beneficiary ──

theorem junmada_gets_beneficiary :
    predictFunction junmada_make_mole = .beneficiary := rfl

-- ── Ditransitives → blocked ──

theorem makia_blocked :
    predictFunction makia_give = .blocked := rfl

theorem tikka_blocked :
    predictFunction tikka_ask = .blocked := rfl

-- ════════════════════════════════════════════════════
-- § 11. All Verbs — Comprehensive Verification
-- ════════════════════════════════════════════════════

/-- The observed applicative function for each verb. -/
structure ApplDatum where
  verb : OdamVerb
  observedFunction : ApplFunction
  deriving Repr, BEq

def allData : List ApplDatum :=
  [ -- Intransitives (agent introduction)
    ⟨tuklhia, .agentIntroduction⟩
  , ⟨koxia, .agentIntroduction⟩
  , ⟨miiya_burn, .agentIntroduction⟩
  , ⟨miiya_ignite, .agentIntroduction⟩
  , ⟨tisdia, .agentIntroduction⟩
  , ⟨aaya, .agentIntroduction⟩
  , ⟨kikbo, .agentIntroduction⟩
    -- Transitives with promotable participants (promotion)
  , ⟨gara_sell, .promotion⟩
  , ⟨jotsa_send, .promotion⟩
  , ⟨aga_say, .promotion⟩
  , ⟨bua_throw, .promotion⟩
  , ⟨baabu_take_out, .promotion⟩
  , ⟨nuina_push, .promotion⟩
    -- Transitives without promotable participants (beneficiary)
  , ⟨mukda_sharpen, .beneficiary⟩
  , ⟨sooma_sew, .beneficiary⟩
  , ⟨sarna_tear, .beneficiary⟩
  , ⟨uana_clean, .beneficiary⟩
  , ⟨uana_write, .beneficiary⟩
  , ⟨kuagia_cut_firewood, .beneficiary⟩
  , ⟨bulhia_tie, .beneficiary⟩
  , ⟨bakta_hang, .beneficiary⟩
  , ⟨gammu_put_inside, .beneficiary⟩
    -- Denominal creation (transitive base → beneficiary)
  , ⟨junmada_make_mole, .beneficiary⟩
    -- Ditransitives (blocked)
  , ⟨makia_give, .blocked⟩
  , ⟨tikka_ask, .blocked⟩
  ]

/-- **The deepest theorem**: `predictFunction` matches the observed
    applicative function for all non-exceptional verbs.

    The prediction succeeds for all verbs that are NOT exceptional
    transitives (ingestion, perception, lexical middles). For those,
    `predictFunctionRefined` is needed. -/
theorem prediction_matches_all_nonexceptional :
    allData.all (λ d => predictFunction d.verb == d.observedFunction) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 12. Structural Properties of the Thematic Hierarchy
-- ════════════════════════════════════════════════════

/-- Valency change is always +1.
    The applied form has exactly one more syntactic argument than the base. -/
def baseValency : BaseTransitivity → Nat
  | .intransitive => 1
  | .transitive   => 2
  | .ditransitive => 3

def appliedValency (v : OdamVerb) : Option Nat :=
  match predictFunction v with
  | .blocked => none           -- No applied form
  | _ => some (baseValency v.transitivity + 1)

theorem intransitive_becomes_transitive :
    appliedValency tuklhia = some 2 := rfl

theorem transitive_becomes_ditransitive :
    appliedValency mukda_sharpen = some 3 := rfl

theorem ditransitive_is_blocked :
    appliedValency makia_give = none := rfl

/-- The hypertransitivity ban: no verb can have more than 3 syntactic
    arguments. This follows from the fact that ditransitives cannot
    applicativize and the +1 valency change. -/
theorem no_hypertransitivity (v : OdamVerb)
    (h : v.transitivity = .ditransitive) :
    predictFunction v = .blocked := by
  simp only [predictFunction, h]

-- ════════════════════════════════════════════════════
-- § 13. Animacy and Instruments
-- ════════════════════════════════════════════════════

/-- Whether a participant type is promotable by the applicative.
    Promotion requires adding an animacy entailment. Instruments
    are categorically inanimate in O'dam, so they cannot be promoted. -/
def isPromotable : EntailedParticipantType → AnimateCompatibility → Prop
  | .implicitObject, _           => True
  | .locative,       .compatible => True
  | .locative,       .incompatible => False
  | .instrument,     _           => False
  | .none,           _           => False

instance : ∀ p ac, Decidable (isPromotable p ac) := fun p ac => by
  cases p <;> cases ac <;> unfold isPromotable <;> infer_instance

/-- Instruments are never promotable. -/
theorem instruments_never_promotable (ac : AnimateCompatibility) :
    ¬ isPromotable .instrument ac := by
  cases ac <;> exact not_false

/-- Implicit objects are always promotable. -/
theorem implicit_objects_always_promotable (ac : AnimateCompatibility) :
    isPromotable .implicitObject ac := by
  cases ac <;> trivial

/-- Animate-compatible locatives are promotable. -/
theorem animate_locatives_promotable :
    isPromotable .locative .compatible := trivial

/-- Inanimate locatives are not promotable. -/
theorem inanimate_locatives_not_promotable :
    ¬ isPromotable .locative .incompatible := not_false

-- ════════════════════════════════════════════════════
-- § 14. Exceptional Transitive Classification
-- ════════════════════════════════════════════════════

/-- The exceptional transitive classes are exactly those where the
    subject is not maximally distinct from the object.

    This captures @cite{naess-2007}'s observation: ingestion/perception
    verbs and lexical middles minimize the affector-affectee distinction,
    making them functionally intransitive. -/
def isExceptionalTransitive : VerbClass → Prop
  | .ingestion    => True
  | .perception   => True
  | .lexicalMiddle => True
  | _             => False

instance : DecidablePred isExceptionalTransitive := fun x => by
  cases x <;> unfold isExceptionalTransitive <;> infer_instance

/-- Exceptional transitives are syntactically transitive. -/
theorem exceptionals_are_transitive :
    bhaya_swallow.transitivity = .transitive ∧
    tigia_see.transitivity = .transitive ∧
    saabu_fast.transitivity = .transitive := ⟨rfl, rfl, rfl⟩

/-- But they are effectively intransitive for applicativization. -/
theorem exceptionals_effectively_intransitive :
    effectiveTransitivity bhaya_swallow = .intransitive ∧
    effectiveTransitivity tigia_see = .intransitive ∧
    effectiveTransitivity saabu_fast = .intransitive := ⟨rfl, rfl, rfl⟩

/-- `predictFunction` depends only on `transitivity`,
    `entailedParticipant`, and `animateLocative`. -/
theorem predictFunction_depends_only (v w : OdamVerb)
    (ht : v.transitivity = w.transitivity)
    (he : v.entailedParticipant = w.entailedParticipant)
    (ha : v.animateLocative = w.animateLocative) :
    predictFunction v = predictFunction w := by
  simp only [predictFunction, ht, he, ha]

/-- `predictFunctionRefined` agrees with `predictFunction` on all
    non-exceptional verb classes. The refinement only changes the
    prediction for ingestion, perception, and lexical middles. -/
theorem refined_agrees_on_nonexceptional (v : OdamVerb)
    (h : ¬ isExceptionalTransitive v.verbClass) :
    predictFunctionRefined v = predictFunction v := by
  obtain ⟨bf, gl, af, vc, tr, ep, al⟩ := v
  unfold predictFunctionRefined
  apply predictFunction_depends_only
  · show effectiveTransitivity ⟨bf, gl, af, vc, tr, ep, al⟩ = tr
    cases vc <;> first | rfl | simp [isExceptionalTransitive] at h
  · rfl
  · rfl

-- ════════════════════════════════════════════════════
-- § 15. Connection to Krejci's Causativizability Hierarchy
-- ════════════════════════════════════════════════════

/-! @cite{krejci-2012} proposes a hierarchy of causativizability:

        unaccusatives > middles/ingestives > unergatives > simple transitives

    O'dam's exceptional transitives are exactly middles and ingestives —
    the verb classes that cross-linguistically pattern with intransitives
    in causativization. This explains why O'dam applicatives (which are
    syncretic with causatives) treat them as intransitive:
    causative-applicative syncretism + the causativizability hierarchy
    predicts the exceptional transitive class.

    The hierarchy data and implicational validation are formalized in
    `Semantics.Causation.Morphological` (§11). -/

-- ════════════════════════════════════════════════════
-- § 16. Bridge to Pylkkänen 2008 (High/Low Typology)
-- ════════════════════════════════════════════════════

/-! O'dam applicatives challenge the @cite{pylkknen-2008} binary
    high/low classification. They exhibit properties of BOTH types:

    - **High-like**: can applicativize unergatives (agent introduction)
      and static verbs (lexical middles gain agents)
    - **Low-like**: can promote a locative to an applied object with
      a transfer-like interpretation

    However, O'dam applicatives are NOT ambiguous in the way Kinyarwanda
    *-ish* is: with a given verb, the function is deterministic. -/

/-- O'dam passes both high-applicative diagnostics from Table 2.1. -/
def odam_appl : Pylkkanen2008.ApplClassification :=
  { language := "O'dam"
  , applType := .high  -- closest fit (agent-introduction for intransitives)
  , unergativeOK := some true      -- *kox-chuda'* 'put to sleep'
  , staticVerbOK := some true      -- *saab-tuda'* 'make fast'
  }

/-- O'dam patterns as high by the diagnostics. -/
theorem odam_diagnostics_predict_high :
    Pylkkanen2008.diagnosticPredictsHigh
      odam_appl = true := rfl

/-- But O'dam also performs promotion (a low-like function). The
    dissertation shows this dual behavior is NOT ambiguity — the
    function is deterministic based on the base verb. This suggests
    that high/low is not a single binary parameter but a cluster
    of partially independent properties. -/
theorem odam_also_promotes :
    predictFunction jotsa_send = .promotion ∧
    predictFunction baabu_take_out = .promotion := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 17. The "Soup" — Thematic Hierarchy as a Linking Factor
-- ════════════════════════════════════════════════════

/-! @cite{beavers-2023-sag-lectures} argues that argument realization is
    governed by a "soup" of factors: truth-conditional strength (MAP),
    event-structural templates, convention, and discourse/pragmatics.
    Beavers acknowledges that thematic hierarchies play SOME role but
    argues they are largely reducible to truth-conditional content.

    O'dam applicatives provide evidence that the thematic hierarchy
    (273) is NOT fully reducible to content:

    1. The hierarchy Agent > Promoted [+ANIM] > Beneficiary determines
       which applicative function is selected, NOT the truth-conditional
       strength of the applied argument.

    2. Instruments cannot be promoted even though they may be entailed
       (truth-conditionally strong) — the blocking comes from a
       representational property (animacy), not from content-based MAP.

    3. The exceptional transitives (ingestion, perception, middles) are
       blocked from beneficiary licensing by a representational property
       (subject-object distinctness), not by content strength.

    This makes O'dam a key test case for the "soup" theory: thematic
    hierarchies are one ingredient that cannot be fully eliminated. -/

/-- The thematic hierarchy makes a prediction that pure MAP cannot:
    the same verb form (*sell*, *send*) always promotes the same
    participant, regardless of context or truth-conditional strength
    of other potential applied arguments. See §19 for the deeper
    analysis of why this is orthogonal to MAP. -/
theorem hierarchy_deterministic :
    predictFunction gara_sell = .promotion ∧
    predictFunction jotsa_send = .promotion ∧
    predictFunction mukda_sharpen = .beneficiary ∧
    predictFunction sooma_sew = .beneficiary := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 18. Locatives as Adjuncts
-- ════════════════════════════════════════════════════

/-! A central claim: locative participants in O'dam are ALWAYS syntactic
    adjuncts. Evidence:

    1. Motion verbs with one non-locative participant (e.g., *aaya'*
       'arrive') are intransitive under applicativization — they gain
       an agent, not a beneficiary.

    2. Motion verbs with two non-locative participants are transitive —
       the locative doesn't count toward valency.

    3. Under the promotative function, entailed locatives are promoted
       to object status, gaining an animacy entailment. If locatives
       were already arguments, promotion of an argument to... argument
       would be incoherent.

    This connects to head-marking and preverbal quantification (Ch. 3–4):
    locatives fail every argumenthood test in O'dam. -/

/-- Motion verbs are intransitive despite having locative participants.
    Their locatives are adjuncts, so they don't count toward valency. -/
theorem motion_verbs_intransitive :
    tisdia.transitivity = .intransitive ∧
    aaya.transitivity = .intransitive := ⟨rfl, rfl⟩

/-- Therefore motion verbs gain agents under applicativization,
    just like other intransitives. -/
theorem motion_verbs_gain_agents :
    predictFunction tisdia = .agentIntroduction ∧
    predictFunction aaya = .agentIntroduction := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 19. Bridge to MAP (@cite{beavers-2010})
-- ════════════════════════════════════════════════════

/-! O'dam applicative promotion is orthogonal to MAP. MAP governs
    direct/oblique alternations based on **truth-conditional strength**
    (affectedness degree). O'dam promotion is governed by **animacy**,
    a representational property independent of change-of-state
    entailments.

    This creates a two-dimensional space for argument realization:

    | Dimension        | Governing property     | Framework       |
    |------------------|------------------------|-----------------|
    | Direct vs oblique| Truth-conditional strength| MAP (Beavers)  |
    | Promoted vs not  | Animacy compatibility  | Hierarchy (273) |

    Instruments can be truth-conditionally strong (entailed by the
    verb) but STILL not promotable, because they are categorically
    inanimate. This is a content-independent constraint that MAP
    cannot capture. -/

/-- Instruments are entailed (potentially high affectedness) but
    not promotable. This witnesses a dimension of argument realization
    orthogonal to MAP: animacy governs promotion, not truth-conditional
    strength. -/
theorem promotion_orthogonal_to_entailment :
    kuagia_cut_firewood.entailedParticipant = .instrument ∧
    predictFunction kuagia_cut_firewood = .beneficiary ∧
    bulhia_tie.entailedParticipant = .instrument ∧
    predictFunction bulhia_tie = .beneficiary := ⟨rfl, rfl, rfl, rfl⟩

/-- The thematic hierarchy makes categorical predictions that
    cannot be derived from truth-conditional strength alone:
    the SAME type of entailed participant (locative) gets different
    treatment based solely on animate compatibility. -/
theorem animacy_gates_promotion :
    baabu_take_out.entailedParticipant = .locative ∧
    baabu_take_out.animateLocative = .compatible ∧
    predictFunction baabu_take_out = .promotion ∧
    bakta_hang.entailedParticipant = .locative ∧
    bakta_hang.animateLocative = .incompatible ∧
    predictFunction bakta_hang = .beneficiary := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Everdell2024
