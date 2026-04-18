import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment

/-!
# The ASSERT Operator and Speech Act Phrase
  @cite{hacquard-2006}

Formalizes the Speech Act Phrase (SAP) from @cite{hacquard-2006}. Every matrix clause is
headed by a SAP that introduces a speech event e* with propositional
CONTENT. The type of speech act determines the content:

- **Declarative**: CON(e*) = speaker's beliefs → epistemic R
- **Imperative**: CON(e*) = addressee's to-do list → deontic R
- **Interrogative**: CON(e*) = question content

## Architectural Significance

`EventBinder.speechAct.hasContent = true` is currently stipulated in
EventRelativity §8. This file DERIVES that fact: ASSERT introduces
a speech event, and all speech events carry propositional content
(that is what makes them speech acts). Content licensing then follows:
the speech event is contentful → epistemic R can project from it.

## Connection to EventRelativity

The speech event's content IS the conversational background that a
modal bound to e* accesses. In the `AnchoringFn` framework:

    anchor f e* = CON(e*)

Different speech act types give different CON(e*), hence different
modal flavors — without lexical ambiguity in the modal.

-/

namespace Semantics.Modality.Assert

open Semantics.Modality.EventRelativity
open Core.Modality (ModalFlavor)
open Core.Mood (IllocutionaryMood)


-- ════════════════════════════════════════════════════
-- § 1. Speech Act Types
-- ════════════════════════════════════════════════════

/-- The type of speech act heading the Speech Act Phrase.

@cite{hacquard-2006}: "The content of the speech event
is different depending on the type of speech act."

Now unified with `IllocutionaryMood` from `Core.Discourse`. The five
constructors — declarative, interrogative, imperative, promissive,
exclamative — classify the pragmatic act performed. -/
abbrev SpeechActType := IllocutionaryMood

/-- All speech acts are contentful events. This is definitional:
a speech act IS the performance of propositional content.

This derives `EventBinder.speechAct.hasContent = true`: the speech
event introduced by SAP always carries content, hence it can always
project epistemic R (content licensing, EventRelativity §8). -/
def hasContent : SpeechActType → Bool
  | _ => true

/-- The primary modal flavor licensed by each speech act type.

- Declarative → epistemic: the content is the speaker's beliefs, so
  R accesses what the speaker considers possible.
- Imperative → deontic: the content is the addressee's obligations, so
  R accesses what is permitted/required.
- Promissive → deontic: the content is the speaker's commitments,
  paralleling imperative. -/
def primaryFlavor : SpeechActType → ModalFlavor
  | .declarative => .epistemic
  | .imperative => .deontic
  | .promissive => .deontic
  | .interrogative => .epistemic
  | .exclamative => .epistemic


-- ════════════════════════════════════════════════════
-- § 2. Speech Act Events
-- ════════════════════════════════════════════════════

/-- A speech act event e* with its content CON(e*).

This is what the Speech Act Phrase introduces at the top of every
matrix clause. The `content` field is the conversational background
that modals in the clause can bind to (@cite{hacquard-2006}, (219)–(222)). -/
structure SpeechActEvent (W : Type*) where
  /-- The type of speech act -/
  actType : SpeechActType
  /-- CON(e*): the propositional content of the speech event.
  Maps each world to the set of propositions encoding the content. -/
  content : W → List ((W → Bool))

/-- ASSERT: introduce a declarative speech event.

(222) `SPEECH ACT_DECLARATIVE(e*)`:
The content encodes the speaker's beliefs — worlds compatible with
what the speaker takes to be true. -/
def ASSERT {W : Type*} (beliefs : W → List ((W → Bool))) : SpeechActEvent W where
  actType := .declarative
  content := beliefs

/-- DIRECT: introduce an imperative speech event.

The content encodes the addressee's to-do list — worlds compatible
with the addressee fulfilling their obligations. -/
def DIRECT {W : Type*} (obligations : W → List ((W → Bool))) : SpeechActEvent W where
  actType := .imperative
  content := obligations


-- ════════════════════════════════════════════════════
-- § 3. From Speech Act to Anchoring
-- ════════════════════════════════════════════════════

/-- A speech act event's content IS a conversational background.

`SpeechActEvent.content : W → List ((W → Bool))` has the same type as
a Kratzer `ConvBackground` and as `anchor f e` from EventRelativity §10.
The speech event's content is the background that modals in its scope
access when they bind to e*. -/
def SpeechActEvent.toBackground {W : Type*}
    (sa : SpeechActEvent W) : W → List ((W → Bool)) :=
  sa.content

/-- Lift a speech act event into an anchoring function.

Given a speech act event sa, we construct an `AnchoringFn` where:
- The speech event (`.inl `) maps to sa's content
- Any described event (`.inr ev`) maps to the described event's
  own background.

This models the clause structure: the speech event anchoring is
provided by ASSERT at the top; the described event anchoring comes
from the verb's event structure lower in the clause. -/
def speechActAnchoring {Ev W : Type*}
    (sa : SpeechActEvent W)
    (describedBg : Ev → W → List ((W → Bool))) : AnchoringFn (Unit ⊕ Ev) W
  | .inl (), w => sa.content w
  | .inr ev, w => describedBg ev w

/-- The speech event slot of `speechActAnchoring` reduces to the
speech act's content. -/
theorem speech_slot_is_content {Ev W : Type*}
    (sa : SpeechActEvent W)
    (bg : Ev → W → List ((W → Bool))) (w : W) :
    speechActAnchoring sa bg (.inl ()) w = sa.content w := rfl

/-- The described event slot passes through to the verb's background. -/
theorem described_slot_passthrough {Ev W : Type*}
    (sa : SpeechActEvent W)
    (bg : Ev → W → List ((W → Bool))) (ev : Ev) (w : W) :
    speechActAnchoring sa bg (.inr ev) w = bg ev w := rfl


-- ════════════════════════════════════════════════════
-- § 4. Content Licensing: Derived, Not Stipulated
-- ════════════════════════════════════════════════════

/-! EventRelativity §8 stipulates `EventBinder.speechAct.hasContent = true`.
With the SAP formalization, this becomes derivable:

1. Every matrix clause has a SAP.
2. SAP introduces a speech event e*.
3. e* carries CON(e*) (the speech act's propositional content).
4. Therefore e* is contentful.
5. Therefore epistemic R can project from e* (content licensing).

The bridge theorems below make this derivation explicit. -/

/-- All speech act types are contentful — by definition, performing
a speech act involves producing propositional content. -/
theorem all_speech_acts_contentful :
    ∀ t : SpeechActType, hasContent t = true := by
  intro t; cases t <;> rfl

/-- ASSERT produces a contentful event. -/
theorem assert_contentful {W : Type*} (beliefs : W → List ((W → Bool))) :
    hasContent (ASSERT beliefs).actType = true := rfl

/-- DIRECT produces a contentful event. -/
theorem direct_contentful {W : Type*} (obligations : W → List ((W → Bool))) :
    hasContent (DIRECT obligations).actType = true := rfl

/-- Speech act contentfulness agrees with `EventBinder.speechAct.hasContent`.

This is the key bridge: the stipulated fact in EventRelativity §8
(`EventBinder.speechAct.hasContent = true`) is justified by the SAP
analysis — ASSERT always introduces a contentful event. -/
theorem sap_justifies_binder_content :
    -- Every speech act type is contentful (this file)
    (∀ t : SpeechActType, hasContent t = true) ∧
    -- EventBinder.speechAct is contentful (EventRelativity §8)
    EventBinder.speechAct.hasContent = true :=
  ⟨all_speech_acts_contentful, rfl⟩


-- ════════════════════════════════════════════════════
-- § 5. Speech Act Type Determines Modal Flavor
-- ════════════════════════════════════════════════════

/-- Declarative speech acts license epistemic modals. -/
theorem declarative_epistemic :
    primaryFlavor .declarative = .epistemic := rfl

/-- Imperative speech acts license deontic modals. -/
theorem imperative_deontic :
    primaryFlavor .imperative = .deontic := rfl

/-- Different speech act types yield different primary flavors for
the same modal. This derives the "must" ambiguity:

- "John must be home" (declarative) → epistemic necessity
  (CON(e*) = speaker's beliefs → must = "given my evidence")
- "Go home!" (imperative) → deontic necessity
  (CON(e*) = to-do list → must = "you are required to")

Same modal, different speech acts, different readings.
No lexical ambiguity needed. -/
theorem speech_act_determines_flavor :
    primaryFlavor .declarative ≠
    primaryFlavor .imperative := by decide


-- ════════════════════════════════════════════════════
-- § 6. Worked Example: "You can leave"
-- ════════════════════════════════════════════════════

/-! Two contexts for "You can leave":

1. **Declarative** (informing): "Based on what I know, it's possible
   you'll leave." ASSERT introduces e* with content = speaker's evidence.
   The modal accesses epistemic R. Staying is also possible.

2. **Imperative** (permitting): "You have permission to leave."
   DIRECT introduces e* with content = addressee's permissions.
   The modal accesses deontic R. Staying is NOT permitted.

The difference: same modal "can" (◇), but different speech events
yield different accessible worlds. -/

/-- Two outcomes: leave or stay. -/
inductive LeaveWorld where | leave | stay
  deriving DecidableEq, Repr, Inhabited

private def allLW : List LeaveWorld := [.leave, .stay]

/-- Declarative context: speaker's evidence is compatible with both
outcomes (speaker doesn't know whether the addressee will leave). -/
def declarativeEvidence : SpeechActEvent LeaveWorld :=
  ASSERT (λ _ => [])  -- empty background: all worlds accessible

/-- Imperative context: permission to leave — only leave-world is
compatible with the addressee's permissions. -/
def imperativePermission : SpeechActEvent LeaveWorld :=
  DIRECT (λ _ => [λ w => w == .leave])  -- only leaving is permitted

/-- The two speech acts have different types. -/
theorem different_speech_acts :
    declarativeEvidence.actType = .declarative ∧
    imperativePermission.actType = .imperative := ⟨rfl, rfl⟩

/-- Anchoring function using declarative speech act content.
The speech event's content provides the conversational background.

NB: These are defined directly rather than via `speechActAnchoring`
(§3) to avoid type inference issues with the generic `Ev` parameter.
The result is equivalent: `fDecl w = speechActAnchoring
declarativeEvidence (λ _ _ => []) (.inl) w`. -/
private def fDecl : AnchoringFn Unit LeaveWorld :=
  λ () => declarativeEvidence.content

/-- Anchoring function using imperative speech act content. -/
private def fImpr : AnchoringFn Unit LeaveWorld :=
  λ () => imperativePermission.content

/-- Under the declarative, both leaving and staying are possible
(speaker is uncertain). -/
theorem declarative_leave_possible :
    possibility fDecl () allLW (· == .leave) .leave := by decide

theorem declarative_stay_possible :
    possibility fDecl () allLW (· == .stay) .leave := by decide

/-- Under the imperative, leaving is permitted but staying is NOT. -/
theorem imperative_leave_permitted :
    possibility fImpr () allLW (· == .leave) .leave := by decide

theorem imperative_stay_not_permitted :
    ¬ possibility fImpr () allLW (· == .stay) .leave := by decide

/-- The core contrast: same modal (◇), same proposition (stay),
same evaluation world — but different speech acts yield different
truth values. The speech act type, mediated through CON(e*),
determines the modal domain. -/
theorem speech_act_modulates_domain :
    -- Declarative: ◇(stay) = true (staying is epistemically possible)
    possibility fDecl () allLW (· == .stay) .leave ∧
    -- Imperative: ◇(stay) = false (staying is not permitted)
    ¬ possibility fImpr () allLW (· == .stay) .leave := by
  refine ⟨?_, ?_⟩ <;> decide


-- ════════════════════════════════════════════════════
-- § 7. Connection to EventProjection (§11)
-- ════════════════════════════════════════════════════

/-! The speech event projects to an individual-time pair via
`EventProjection` (EventRelativity §11):

| Speech act | holder(e*) | τ(e*) |
|------------|-----------|-------|
| Declarative | speaker | speech time |
| Imperative | addressee | speech time |

The holder determines WHOSE propositional attitudes are relevant:
- Declarative: speaker's beliefs (epistemic = "what I know")
- Imperative: addressee's obligations (deontic = "what you must do")

Both share the same time (speech time = now), but the different
holders yield different content types. -/

/-- Speaker and addressee for the projection example. -/
inductive Interlocutor where | speaker | addressee
  deriving DecidableEq, Repr, Inhabited

/-- Speech time. -/
inductive SpeechTime where | now
  deriving DecidableEq, Repr, Inhabited

/-- The event projection for speech act events.

Declarative: holder = speaker (it's the speaker's beliefs).
Imperative: holder = addressee (it's the addressee's obligations).

NB: `.interrogative =>.speaker` because the holder is who PERFORMS the
speech act (always the speaker in Hacquard's framework). This is distinct
from the SEAT OF KNOWLEDGE, which is the hearer for
interrogatives — that notion captures who has epistemic authority over
the content, not who initiates the speech event. The bridge between these
is in `IllocutionaryForce.lean`: `seat_of_knowledge_agrees_with_epistemic_authority`. -/
def speechActProjection : EventProjection SpeechActType Interlocutor SpeechTime where
  holder
    | .declarative => .speaker
    | .imperative => .addressee
    | .promissive => .speaker
    | .interrogative => .speaker
    | .exclamative => .speaker
  time _ := .now

/-- Declarative projects to (speaker, now). -/
theorem declarative_projects_to_speaker :
    speechActProjection.toPair .declarative = ⟨.speaker, .now⟩ := rfl

/-- Imperative projects to (addressee, now). -/
theorem imperative_projects_to_addressee :
    speechActProjection.toPair .imperative = ⟨.addressee, .now⟩ := rfl

/-- Different speech act types project to different holders.
The holder determines whose attitudes provide the modal content:
speaker's beliefs (epistemic) vs addressee's obligations (deontic). -/
theorem different_holders :
    speechActProjection.toPair .declarative ≠
    speechActProjection.toPair .imperative := by decide


end Semantics.Modality.Assert
