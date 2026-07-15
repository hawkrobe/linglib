/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Mood.State
import Linglib.Semantics.Modality.EventRelativity

/-!
# The speech event and its content

[hacquard-2006] (pp. 141–3) adopts [speas-tenny-2003]'s Speech Act
Phrase — every matrix clause is headed by a SAP whose head introduces
a speech event `e*` and encodes illocutionary force — and adds one
assumption: the speech event has *content*, varying with the type of
speech act. For a declarative, `CON(e*)` is the speaker's beliefs;
for an imperative, the addressee's To-Do List ([portner-2004]). A
modal bound by `e*` reads `CON(e*)` as its conversational background,
so the speech act type determines the modal's flavor with no lexical
ambiguity. Here `CON(e*)` enters the mood state through the
force-targeted update — declarative content is `assert`ed, imperative
content `promote`d — and the licensed modal and flavor are read off
the targeted component.

## Main declarations

* `SpeechEvent` — a force together with `CON(e*)`.
* `SpeechEvent.toState`, `SpeechEvent.modal` — the induced state and
  its licensed necessity modal.
* `Component.flavor`, `Illocutionary.primaryFlavor` — Hacquard's
  flavor assignment, derived from component targeting.
* `HasTarget ModalFlavor` — the third instance of [portner-2018]'s
  classification.

## Implementation notes

[speas-tenny-2003] grammaticalize exactly four speech acts
(declarative, interrogative, imperative, quotative). `SpeechEvent`
uses the library-wide five-way `Illocutionary` — no quotative;
promissive and exclamative are conjectural linglib extensions — and
Hacquard gives content clauses only for declaratives and imperatives,
so the inquisitive route induces the initial state. Binding height
(*which* event a modal is bound by) is
`Semantics/Modality/EventRelativity`'s territory.
-/

namespace Mood

open UpdateSemantics.Default
open Semantics.Modality (ModalFlavor)
open HasTarget (target)
open Semantics.Modality.EventRelativity (EventProjection)

variable {W : Type*}

/-! ### Speech events -/

/-- A speech act event `e*` with its content `CON(e*)`
([hacquard-2006], her assumption 4, pp. 142–3). -/
structure SpeechEvent (W : Type*) where
  /-- The illocutionary force the SAP head encodes. -/
  force : Illocutionary
  /-- `CON(e*)`: the propositional content of the speech event. -/
  content : W → List (W → Prop)

/-- A declarative speech event: `CON(e*)` is the speaker's beliefs
([hacquard-2006], her (222)). -/
def SpeechEvent.declarative (beliefs : W → List (W → Prop)) : SpeechEvent W :=
  ⟨.declarative, beliefs⟩

/-- An imperative speech event: `CON(e*)` is the addressee's To-Do
List ([hacquard-2006] after [portner-2004]). -/
def SpeechEvent.imperative (todo : W → List (W → Prop)) : SpeechEvent W :=
  ⟨.imperative, todo⟩

/-! ### The induced state -/

/-- The state a speech event induces at anchor world `w₀`: fold
`CON(e*)(w₀)` through the targeted component's update. -/
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

/-- A declarative's information state is the worlds compatible with
every belief in `CON(e*)`. -/
theorem SpeechEvent.mem_toState_declarative_info
    (beliefs : W → List (W → Prop)) (w₀ v : W) :
    v ∈ ((SpeechEvent.declarative beliefs).toState w₀).info ↔
      ∀ p ∈ beliefs w₀, p v := by
  rw [SpeechEvent.toState_declarative, ExpState.mem_foldl_assert_info]
  simp [ExpState.init]

/-- An imperative's ordering prefers TDL-compliant worlds — the
[kratzer-1981] ordering-source construction, arrived at by
promotion. -/
theorem SpeechEvent.toState_imperative_le
    (todo : W → List (W → Prop)) (w₀ w v : W) :
    ((SpeechEvent.imperative todo).toState w₀).order.le w v ↔
      ∀ p ∈ todo w₀, p v → p w := by
  rw [SpeechEvent.toState_imperative, ExpState.foldl_promote_order_le]
  exact ⟨And.right, fun h => ⟨trivial, h⟩⟩

/-- The To-Do List ranks worlds; it does not eliminate them. -/
theorem SpeechEvent.toState_imperative_info
    (todo : W → List (W → Prop)) (w₀ : W) :
    ((SpeechEvent.imperative todo).toState w₀).info = Set.univ := by
  rw [SpeechEvent.toState_imperative, ExpState.foldl_promote_info]
  rfl

/-! ### The licensed modal -/

/-- The necessity modal a speech event licenses: the targeted
component's modal on the induced state ([hacquard-2006]'s epistemic
and deontic readings). -/
def SpeechEvent.modal (sa : SpeechEvent W) (w₀ : W) : (W → Prop) → Prop :=
  (target sa.force).boxOn (State.ofExpState (sa.toState w₀))

@[simp] theorem SpeechEvent.modal_declarative
    (beliefs : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.declarative beliefs).modal w₀ p =
      ((SpeechEvent.declarative beliefs).toState w₀).boxCs p := rfl

@[simp] theorem SpeechEvent.modal_imperative
    (todo : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.imperative todo).modal w₀ p =
      ((SpeechEvent.imperative todo).toState w₀).boxLe p := rfl

/-- The declarative modal quantifies over exactly the
belief-compatible worlds. -/
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

/-- Modal flavors target the component their Kratzer parameter feeds:
modal-base flavors the informational, ordering-source flavors the
preferential ([kratzer-1981]'s parameter roles; [portner-2018],
p. 233). The third instance of the one classification, beside
sentence and verbal mood. -/
instance : HasTarget Semantics.Modality.ModalFlavor where
  target
    | .epistemic      => .informational
    | .deontic        => .preferential
    | .bouletic       => .preferential
    | .circumstantial => .informational

/-- The flavor a component licenses on [hacquard-2006]'s reading of
`CON(e*)`; the inquisitive component is routed to epistemic pending
an interrogative-content story. -/
def Component.flavor : Component → ModalFlavor
  | .informational => .epistemic
  | .preferential  => .deontic
  | .inquisitive   => .epistemic

/-- The primary flavor a speech act licenses ([hacquard-2006]):
the targeted component's flavor. -/
def Illocutionary.primaryFlavor (f : Illocutionary) : ModalFlavor :=
  (target f).flavor

/-- `Component.flavor` is a section of the modal-flavor targeting on
the two POSW components: the representative flavor of a component
targets that component back. -/
theorem target_flavor (c : Component) (h : c ≠ .inquisitive) :
    target c.flavor = c := by
  cases c <;> first | rfl | exact absurd rfl h

@[simp] theorem primaryFlavor_declarative :
    Illocutionary.declarative.primaryFlavor = .epistemic := rfl

@[simp] theorem primaryFlavor_imperative :
    Illocutionary.imperative.primaryFlavor = .deontic := rfl

/-- Different speech acts, different flavors — the "must" ambiguity
without lexical ambiguity. -/
theorem speech_act_determines_flavor :
    Illocutionary.declarative.primaryFlavor ≠
      Illocutionary.imperative.primaryFlavor := by decide

/-! ### Worked example: "You can leave"

Same modal, same proposition, different speech events: the force,
routed through its targeted component, determines the modal
domain. -/

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

/-- Under the declarative, the speaker's evidence leaves staying
open. -/
theorem declarative_leave_not_necessary :
    ¬ declarativeEvidence.modal .leave (· = .leave) := by
  intro h
  exact LeaveWorld.noConfusion
    (h .stay ((SpeechEvent.mem_toState_declarative_info _ _ _).mpr (by simp)))

/-- Under the imperative, every TDL-best world is a leave-world. -/
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

/-! ### Participant projection -/

/-- Speaker and addressee for the projection example. -/
inductive Interlocutor where | speaker | addressee
  deriving DecidableEq, Repr, Inhabited

/-- Speech time. -/
inductive SpeechTime where | now
  deriving DecidableEq, Repr, Inhabited

/-- Whose attitudes provide `CON(e*)`, at speech time
([speas-tenny-2003]'s participant structure; distinct from the seat
of knowledge, tracked per-force by `Illocutionary.authority`). -/
def speechActProjection : EventProjection Illocutionary Interlocutor SpeechTime where
  holder
    | .declarative => .speaker
    | .imperative => .addressee
    | .promissive => .speaker
    | .interrogative => .speaker
    | .exclamative => .speaker
  time _ := .now

end Mood
