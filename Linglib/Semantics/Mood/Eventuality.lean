import Mathlib.Tactic.TypeStar
import Linglib.Semantics.Mood.Categories

/-!
# Event-Level Mood Operators
[grano-2024]

[grano-2024] proposes that mood morphemes operate on the eventuality
argument of the complement clause: indicative existentially closes it
(`INDev`, his (87)), yielding a proposition; subjunctive leaves it
open for abstraction (`SBJVev₁`, his (88a)), as required by
causatives, intention reports, aspectual predicates, and
memory/perception reports; the *intend* variant additionally requires
causal self-reference (`SBJVev₂`, his (134)). This is the event-level
dimension of grammatical mood, complementary to the situation-level
dimension of `Semantics/Mood/Situation.lean`.

The closed/open contrast is carried by the *type* of the denotation.
`Grammatical.eventDenotation` assigns each mood its operator, landing
in the constructor-distinguished `EventDenotation`; that indicative
closes and subjunctive abstracts is then read off the constructor
(`eventDenotation_indicative`, `eventDenotation_subjunctive`) rather
than stipulated in a feature table.
-/

namespace Semantics.Mood

/-- IND existentially closes the eventuality argument ([grano-2024], (87)).

    ⟦INDIC⟧ = λP_(⟨vt⟩).∃e.P(e)

    The eventuality variable is bound; the complement denotes a proposition. -/
def INDev {Event : Type*} (P : Event → Prop) : Prop := ∃ e, P e

/-- SBJV₁ leaves the eventuality argument open ([grano-2024], (88a);
    §7 Subjunctive₃ (135)).

    ⟦SBJV₁⟧ = λP_(⟨vt⟩).P

    The complement retains type ⟨vt⟩ — an event predicate, not a proposition.
    In the core proposal (§5, (88a)), this is the general non-closing mood
    operator. In the §7 unified theory, it becomes specifically Subjunctive₃
    (135) — the identity variant for perception predicates ('see'), causative
    predicates ('make'), and aspectual predicates ('begin'). These predicates
    require or are compatible with eventuality abstraction but do not involve
    causal self-reference or ordering semantics. Distinct from the 'want'
    variant (§7, Subjunctive₁ (133)), which uses Portner & Rubinstein's `ln`
    (local necessity), and the 'intend' variant (Subjunctive₂ (134) =
    `SBJVev₂`), which incorporates CAUSE*. -/
def SBJVev₁ {Event : Type*} (P : Event → Prop) : Event → Prop := P

/-- SBJV₂ leaves the eventuality argument open AND requires causal
    self-reference ([grano-2024], (134); unified theory §7).

    ⟦Subjunctive₂⟧ = λPλe[sn({λw.∃e'.CAUSE*(e,e',w) & P(w)(e')}, content(e), e)]

    This is the variant operative with 'intend' in the §7 unified theory,
    which integrates CAUSE* from the core proposal (§4, (79)) with Portner
    & Rubinstein's ([portner-rubinstein-2020]) modal quantification
    framework. The attitude state e must causally bring about the described
    event e' "in the right way" ([searle-1983]; [harman-1976]). -/
def SBJVev₂ {Event W : Type*}
    (causeStar : Event → Event → W → Prop)  -- CAUSE*(state, event, world)
    (content : Event → W → Prop)          -- content of the attitude state
    (P : W → Event → Prop)               -- world-indexed event predicate
    (e : Event) : Prop :=
  ∀ w, content e w → ∃ e', causeStar e e' w ∧ P w e'

/-- IND closure yields a proposition (no free eventuality variable). -/
theorem INDev_is_propositional {Event : Type*} (P : Event → Prop) :
    (INDev P) = (∃ e, P e) := rfl

/-- SBJV₁ is the identity on event predicates. -/
theorem SBJVev₁_is_identity {Event : Type*} (P : Event → Prop) :
    SBJVev₁ P = P := rfl

/-! ### Mood as event closure, by constructor

The result of applying a mood's event operator: either a *closed*
proposition (the event argument is bound) or an *abstracted* event
predicate (the argument remains open). The closed/open distinction is
the constructor, so downstream facts about which moods enable
eventuality abstraction are read off `Grammatical.eventDenotation`
rather than stipulated. -/

/-- The result of a mood's event-level denotation: a proposition with
    the event argument closed, or an event predicate with the argument
    still open for abstraction. -/
inductive EventDenotation (Event : Type*) where
  /-- The event argument has been existentially closed. -/
  | closed (p : Prop)
  /-- The event argument remains open for abstraction. -/
  | abstracted (p : Event → Prop)

/-- The event-level denotation each grammatical mood assigns to a
    complement's event predicate ([grano-2024]): indicative applies
    `INDev` (closing), subjunctive applies `SBJVev₁` (abstracting).
    This assignment is the theory's sole stipulation; openness facts
    follow from the constructors. -/
def Grammatical.eventDenotation {Event : Type*} (P : Event → Prop) :
    Grammatical → EventDenotation Event
  | .indicative  => .closed (INDev P)
  | .subjunctive => .abstracted (SBJVev₁ P)

/-- Indicative closes the event argument: its denotation lands in
    `closed`. The formal correlate of [grano-2024]'s premise that
    indicative complements cannot feed CAUSE* or aspectual operators
    that bind the event variable. -/
@[simp] theorem eventDenotation_indicative {Event : Type*} (P : Event → Prop) :
    Grammatical.indicative.eventDenotation P = .closed (∃ e, P e) := rfl

/-- Subjunctive leaves the event argument open: its denotation lands in
    `abstracted`, with the predicate unchanged. The formal correlate of
    [grano-2024]'s premise that subjunctive complements feed
    eventuality abstraction. -/
@[simp] theorem eventDenotation_subjunctive {Event : Type*} (P : Event → Prop) :
    Grammatical.subjunctive.eventDenotation P = .abstracted P := rfl

end Semantics.Mood
