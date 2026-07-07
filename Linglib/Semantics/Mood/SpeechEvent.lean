import Linglib.Semantics.Mood.State
import Linglib.Semantics.Modality.EventRelativity

/-!
# The Speech Event and Its Content
[hacquard-2006] [speas-tenny-2003] [portner-2004]

[hacquard-2006] (pp. 141–3) adopts [speas-tenny-2003]'s Speech Act
Phrase — every matrix clause is headed by a SAP whose head introduces
a speech event `e*` and encodes illocutionary force (her (219)–(220))
— and adds one assumption: **the speech event has CONTENT**, varying
with the type of speech act. For a declarative, `CON(e*)` is the
speaker's beliefs; for an imperative, it is the addressee's To-Do List
(the TDL of [portner-2004]). A modal bound by `e*` reads `CON(e*)` as
its conversational background, so the speech act type determines the
modal's flavor with no lexical ambiguity (her (221)–(222)).

This file renders that theory inside the Mood API rather than as
free-standing apparatus:

- **CON(e*) enters the state through the force-targeted update.** A
  `SpeechEvent` induces an `ExpState` (`SpeechEvent.toState`) by
  folding its content through the update morphism of the component its
  force targets: declarative content is `assert`ed (informational),
  imperative content is `promote`d (preferential).
- **The licensed modal is the targeted component's necessity modal.**
  `SpeechEvent.modal := boxOn ∘ target` on the induced state: a
  declarative `e*` yields `boxCs` over belief-compatible worlds,
  an imperative `e*` yields `boxLe` over the TDL-best worlds.
- **Flavor factors through the component classification.**
  `Illocutionary.primaryFlavor := Component.flavor ∘ target` — the
  epistemic/deontic split Hacquard derives from `CON(e*)` is the
  image of [portner-2018]'s component targeting under the reading
  informational ↦ epistemic, preferential ↦ deontic.

**Inventory caveat.** [speas-tenny-2003] (as adopted by
[hacquard-2006]) grammaticalize exactly four speech acts —
declarative, interrogative, imperative, and *quotative*. We type
`SpeechEvent.force` by the library-wide five-way `Illocutionary`
(no quotative; promissive and exclamative extra); the promissive and
exclamative flavor/target assignments are linglib extensions, and
quotatives are unmodeled. Hacquard gives content clauses only for
declaratives and imperatives; the interrogative case (inquisitive
component) is left degenerate here.

Binding height — *which* event a modal is bound by, and hence whether
it reads `CON(e*)` at all — is `Semantics/Modality/EventRelativity`'s
territory; this file consumes its `EventProjection` for the
participant structure of `e*`.
-/

namespace Mood

open Semantics.Dynamic.Default
open Semantics.Modality (ModalFlavor)
open HasTarget (target)
open Semantics.Modality.EventRelativity (EventProjection)

variable {W : Type*}

/-! ### Speech events -/

/-- A speech act event `e*` with its content `CON(e*)`
    ([hacquard-2006], her assumption 4, pp. 142–3): the force the SAP
    head encodes, and the world-indexed conversational background the
    speech event carries — the speaker's beliefs for a declarative,
    the addressee's To-Do List ([portner-2004]) for an imperative. -/
structure SpeechEvent (W : Type*) where
  /-- The illocutionary force the SAP head encodes. -/
  force : Illocutionary
  /-- `CON(e*)`: the propositional content of the speech event. -/
  content : W → List (W → Prop)

/-- A declarative speech event: `CON(e*)` = the speaker's beliefs
    ([hacquard-2006], her (222) `SPEECH ACT_DECLARATIVE(e*)`). -/
def SpeechEvent.declarative (beliefs : W → List (W → Prop)) : SpeechEvent W :=
  ⟨.declarative, beliefs⟩

/-- An imperative speech event: `CON(e*)` = the addressee's To-Do List
    ([hacquard-2006] after [portner-2004]). -/
def SpeechEvent.imperative (todo : W → List (W → Prop)) : SpeechEvent W :=
  ⟨.imperative, todo⟩

/-! ### The induced state: content enters through the targeted update

`CON(e*)` lands in the component the force targets, through that
component's update morphism: `assert` for informational forces,
`promote` for preferential ones. This is the update-side face of the
`HasTarget` classification — the same routing that sends assertion to
`+` and direction to `⋆` in [portner-2018]. -/

/-- The expectation state a speech event induces at anchor world `w₀`:
    fold `CON(e*)(w₀)` through the update morphism of the targeted
    component. Interrogative (and the extension forces routed to the
    inquisitive component) induce the initial state — question content
    is beyond this file. -/
def SpeechEvent.toState (sa : SpeechEvent W) (w₀ : W) : ExpState W :=
  match target sa.force with
  | .informational => (sa.content w₀).foldl ExpState.assert ExpState.init
  | .preferential  => (sa.content w₀).foldl ExpState.promote ExpState.init
  | .inquisitive   => ExpState.init

@[simp] theorem SpeechEvent.toState_declarative
    (beliefs : W → List (W → Prop)) (w₀ : W) :
    (SpeechEvent.declarative beliefs).toState w₀ =
      (beliefs w₀).foldl ExpState.assert ExpState.init := rfl

@[simp] theorem SpeechEvent.toState_imperative
    (todo : W → List (W → Prop)) (w₀ : W) :
    (SpeechEvent.imperative todo).toState w₀ =
      (todo w₀).foldl ExpState.promote ExpState.init := rfl

/-- A declarative's induced information state is exactly the worlds
    compatible with every belief in `CON(e*)` — Hacquard's "worlds
    compatible with the content of my beliefs". -/
theorem SpeechEvent.mem_toState_declarative_info
    (beliefs : W → List (W → Prop)) (w₀ v : W) :
    v ∈ ((SpeechEvent.declarative beliefs).toState w₀).info ↔
      ∀ p ∈ beliefs w₀, p v := by
  rw [SpeechEvent.toState_declarative, ExpState.mem_foldl_assert_info]
  simp [ExpState.init]

/-- An imperative's induced ordering prefers TDL-compliant worlds: `w`
    is at least as good as `v` iff every To-Do item true at `v` is true
    at `w`. The [kratzer-1981] ordering-source construction, arrived at
    by promotion. -/
theorem SpeechEvent.toState_imperative_le
    (todo : W → List (W → Prop)) (w₀ w v : W) :
    ((SpeechEvent.imperative todo).toState w₀).order.le w v ↔
      ∀ p ∈ todo w₀, p v → p w := by
  rw [SpeechEvent.toState_imperative, ExpState.foldl_promote_order_le]
  exact ⟨And.right, fun h => ⟨trivial, h⟩⟩

/-- An imperative's content does not restrict the information state:
    the To-Do List ranks worlds, it does not eliminate them. -/
theorem SpeechEvent.toState_imperative_info
    (todo : W → List (W → Prop)) (w₀ : W) :
    ((SpeechEvent.imperative todo).toState w₀).info = Set.univ := by
  rw [SpeechEvent.toState_imperative, ExpState.foldl_promote_info]
  rfl

/-! ### The licensed modal: `boxOn ∘ target` on the induced state -/

/-- The necessity modal a speech event licenses: the targeted
    component's modal, run on the induced state. A declarative `e*`
    yields `□_cs` over belief-compatible worlds ([hacquard-2006]'s
    epistemic reading, the necessity dual of her (222)); an imperative
    `e*` yields `□_≤` over TDL-best worlds (her deontic reading). -/
def SpeechEvent.modal (sa : SpeechEvent W) (w₀ : W) : (W → Prop) → Prop :=
  (target sa.force).boxOn (State.ofExpState (sa.toState w₀))

/-- The declarative modal is informational necessity over the induced
    state. -/
@[simp] theorem SpeechEvent.modal_declarative
    (beliefs : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.declarative beliefs).modal w₀ p =
      ((SpeechEvent.declarative beliefs).toState w₀).boxCs p := rfl

/-- The imperative modal is preferential necessity over the induced
    state. -/
@[simp] theorem SpeechEvent.modal_imperative
    (todo : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.imperative todo).modal w₀ p =
      ((SpeechEvent.imperative todo).toState w₀).boxLe p := rfl

/-- Hacquard's declarative reading, spelled out: the licensed modal
    quantifies over exactly the belief-compatible worlds. -/
theorem SpeechEvent.modal_declarative_iff
    (beliefs : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.declarative beliefs).modal w₀ p ↔
      ∀ v, (∀ q ∈ beliefs w₀, q v) → p v := by
  constructor
  · intro h v hv
    exact h v ((mem_toState_declarative_info beliefs w₀ v).mpr hv)
  · intro h v hv
    exact h v ((mem_toState_declarative_info beliefs w₀ v).mp hv)

/-! ### Flavor factors through the component classification -/

/-- The modal flavor a POSW component licenses, on [hacquard-2006]'s
    reading of `CON(e*)`: the informational component carries belief
    content (epistemic), the preferential component carries To-Do
    content (deontic). The inquisitive component is routed to
    epistemic (question content is belief-adjacent; a finer treatment
    awaits an interrogative-content story). -/
def Component.flavor : Component → ModalFlavor
  | .informational => .epistemic
  | .preferential  => .deontic
  | .inquisitive   => .epistemic

/-- The primary modal flavor each speech act type licenses
    ([hacquard-2006]: declarative → epistemic, imperative → deontic) —
    **derived** as the targeted component's flavor, not enumerated.
    The promissive and exclamative values are linglib extensions
    (via their conjectural `HasTarget` assignments); [speas-tenny-2003]
    and [hacquard-2006] recognize only declarative, interrogative,
    imperative, and quotative acts. -/
def Illocutionary.primaryFlavor (f : Illocutionary) : ModalFlavor :=
  (target f).flavor

/-- Hacquard's flavor assignment factors through [portner-2018]'s
    component targeting — definitionally. -/
theorem primaryFlavor_eq_flavor_target :
    Illocutionary.primaryFlavor = fun f => (target f).flavor := rfl

@[simp] theorem primaryFlavor_declarative :
    Illocutionary.declarative.primaryFlavor = .epistemic := rfl

@[simp] theorem primaryFlavor_imperative :
    Illocutionary.imperative.primaryFlavor = .deontic := rfl

/-- Different speech act types yield different primary flavors for the
    same modal — the "must" ambiguity without lexical ambiguity:
    "John must be home" (declarative, epistemic) vs "Go home!"
    (imperative context, deontic). Same modal, different speech
    events, different readings. -/
theorem speech_act_determines_flavor :
    Illocutionary.declarative.primaryFlavor ≠
      Illocutionary.imperative.primaryFlavor := by decide

/-! ### Worked example: "You can leave"

Same modal, same proposition, different speech events:

1. **Declarative** (informing): `CON(e*)` = speaker's evidence, here
   uninformative — both outcomes compatible, so neither is necessary.
2. **Imperative** (permitting): `CON(e*)` = the addressee's To-Do
   List containing *leave* — the best worlds are leave-worlds, so
   leaving is preferentially necessary and staying is not.

The speech act type, mediated through `CON(e*)` and the targeted
component, determines the modal domain. -/

/-- Two outcomes: leave or stay. -/
inductive LeaveWorld where | leave | stay
  deriving DecidableEq, Repr, Inhabited

/-- Declarative context: the speaker's evidence is compatible with
    both outcomes. -/
def declarativeEvidence : SpeechEvent LeaveWorld :=
  .declarative (fun _ => [])

/-- Imperative context: *leave* is on the addressee's To-Do List. -/
def imperativePermission : SpeechEvent LeaveWorld :=
  .imperative (fun _ => [(· = .leave)])

/-- Under the declarative, leaving is not informationally necessary —
    the speaker's evidence leaves staying open. -/
theorem declarative_leave_not_necessary :
    ¬ declarativeEvidence.modal .leave (· = .leave) := by
  intro h
  exact LeaveWorld.noConfusion
    (h .stay ((SpeechEvent.mem_toState_declarative_info _ _ _).mpr (by simp)))

/-- Under the imperative, leaving is preferentially necessary: every
    TDL-best world is a leave-world. -/
theorem imperative_leave_required :
    imperativePermission.modal .leave (· = .leave) := by
  have hchar : ∀ v ∈ (imperativePermission.toState LeaveWorld.leave).optimal,
      v = LeaveWorld.leave := by
    intro v hv
    by_contra hstay
    have hle : (imperativePermission.toState LeaveWorld.leave).order.le
        LeaveWorld.leave v :=
      (SpeechEvent.toState_imperative_le _ LeaveWorld.leave LeaveWorld.leave v).mpr
        (fun p hp _ => by rw [List.mem_singleton] at hp; subst hp; rfl)
    have hmem : LeaveWorld.leave ∈ (imperativePermission.toState LeaveWorld.leave).info :=
      (SpeechEvent.toState_imperative_info _ LeaveWorld.leave) ▸ Set.mem_univ _
    have hvl := hv.2 hmem hle
    exact hstay ((SpeechEvent.toState_imperative_le _ LeaveWorld.leave v
      LeaveWorld.leave).mp hvl (· = LeaveWorld.leave) (List.mem_singleton_self _) rfl)
  exact fun v hv => hchar v hv

/-- The core contrast: the same necessity claim over the same
    proposition flips between the two speech events. The force,
    routed through its targeted component, determines the modal
    domain. -/
theorem speech_act_modulates_domain :
    ¬ declarativeEvidence.modal .leave (· = .leave) ∧
      imperativePermission.modal .leave (· = .leave) :=
  ⟨declarative_leave_not_necessary, imperative_leave_required⟩

/-! ### Participant projection

The speech event projects to a holder-time pair ([hacquard-2006];
participant structure per [speas-tenny-2003]): the *performer* is
the speaker throughout; content is keyed to the speaker's beliefs for
declaratives and the addressee's To-Do List for imperatives. Distinct
from the *seat of knowledge* ([speas-tenny-2003]), which is the
hearer for interrogatives — that notion is tracked per-force by
`Illocutionary.authority`. -/

/-- Speaker and addressee for the projection example. -/
inductive Interlocutor where | speaker | addressee
  deriving DecidableEq, Repr, Inhabited

/-- Speech time. -/
inductive SpeechTime where | now
  deriving DecidableEq, Repr, Inhabited

/-- The event projection for speech events: whose attitudes provide
    `CON(e*)`, at speech time. Declarative: the speaker's beliefs.
    Imperative: the addressee's obligations. -/
def speechActProjection : EventProjection Illocutionary Interlocutor SpeechTime where
  holder
    | .declarative => .speaker
    | .imperative => .addressee
    | .promissive => .speaker
    | .interrogative => .speaker
    | .exclamative => .speaker
  time _ := .now

/-- Declarative content is keyed to (speaker, now). -/
theorem declarative_projects_to_speaker :
    speechActProjection.toPair .declarative = ⟨.speaker, .now⟩ := rfl

/-- Imperative content is keyed to (addressee, now). -/
theorem imperative_projects_to_addressee :
    speechActProjection.toPair .imperative = ⟨.addressee, .now⟩ := rfl

end Mood
