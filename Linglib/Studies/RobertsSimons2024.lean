import Linglib.Semantics.Presupposition.Aboutness
import Linglib.Semantics.Aspect.ChangeOfState
import Linglib.Semantics.Questions.Resolution

/-!
# Roberts and Simons (2024): Preconditions and projection

This file formalizes the paper's account of the projective content of change-of-state
predicates, factives and selectional restrictions as the ontological preconditions of the
event types they describe. A sentence refers to an event type and claims, according to its
polarity, that the event's result obtains; its affirmative and negative forms share the
reference, so the precondition projects while the claim flips, the substrate's
`EventSentence`. The change-of-state predicates are read off `Aspect.ChangeOfState`,
`cosEventPhase`, which makes *stop* and *start* telic and *continue* atelic; factives and
selectional restrictions are the other two instances, *discover* carrying prior ignorance as
a second precondition. Projection is a pragmatic default, the presumption that the speaker's
context entails the preconditions of the events they raise, `Presumes`, and it is suppressed
where that presumption cannot be attributed: when the context settles the precondition
negatively, when the speaker is uncommitted, or when the precondition is at issue, since
presuming an alternative of the question under discussion resolves it,
`resolves_of_presumes`. Filtering in conjunction, conditional and disjunction is the case in
which the trigger's local context already entails the precondition, `localContext_subset`, a
condition on the pair of disjuncts that does not depend on their order.

## Implementation notes

Event types are the substrate's world-indexed phases, so a change of state is represented by
its prior state and its result state rather than by a transition, and the occurrence of a
change-of-state event is the coming about of its result. The paper's two diagnostics for
preconditions, the "part of what allowed for" frame and the counterfactual, distinguish
preconditions from consequences and concomitants ontologically rather than semantically, so
they are not derived here, and neither is the informativity argument for the default nor the
reference-time account of the *know* and *discover* contrast.

## References

* [C. Roberts, M. Simons, *Preconditions and projection: explaining non-anaphoric
  presupposition* (2024)][roberts-simons-2024]
* [L. Karttunen, *Implicative verbs* (1971)][karttunen-1971]
* [L. Karttunen, *Presuppositions of compound sentences* (1973)][karttunen-1973]
* [R. C. Stalnaker, *Pragmatic presuppositions* (1974)][stalnaker-1974]
* [I. Heim, *On the projection problem for presuppositions* (1983)][heim-1983]
* [C. Qing, N. D. Goodman, D. Lassiter, *A rational speech-act model of projective content*
  (2016)][qing-goodman-lassiter-2016]
* [A. Warstadt, *Presupposition triggering reflects pragmatic reasoning about utterance
  utility* (2022)][warstadt-2022]
-/

namespace RobertsSimons2024

open Presupposition.Aboutness Aspect.ChangeOfState Question

variable {W : Type*}

/-! ### The three verb classes -/

/-- A change-of-state predicate as an event type: its prior state is the precondition and
its result state the consequence. -/
def cosEventPhase (t : CoSType) (P : W → Prop) : EventPhase W where
  precondition := priorStatePresup t P
  eventOccurs := resultStateAssertion t P
  consequence := resultStateAssertion t P

/-- *Stop* and *start* are telic, a change from the prior state to its negation, and
*continue* is atelic, its result being its prior state. -/
theorem cosEventPhase_isTelic_iff [Nonempty W] (t : CoSType) (P : W → Prop) :
    (cosEventPhase t P).isTelic ↔ t ≠ .continuation := by
  cases t
  · exact ⟨λ _ => nofun, λ _ => ⟨Classical.arbitrary W, λ h => iff_not_self (iff_of_eq h)⟩⟩
  · exact ⟨λ _ => nofun, λ _ => ⟨Classical.arbitrary W, λ h => iff_not_self (iff_of_eq h).symm⟩⟩
  · exact ⟨λ ⟨_, h⟩ => absurd rfl h, λ h => absurd rfl h⟩

/-- A factive state: the truth of the complement is the precondition of the agent's state
of knowing it. -/
def factive (complement knows : W → Prop) : EventPhase W where
  precondition := complement
  eventOccurs := knows
  consequence := knows

/-- A cognitive change of state such as *discover*: the truth of the complement and the
agent's prior ignorance of it are its preconditions, knowing it the result. -/
def discover (complement ignorant knows : W → Prop) : EventPhase W where
  precondition := λ w => complement w ∧ ignorant w
  eventOccurs := knows
  consequence := knows

/-- An emotive factive such as *regret*: the agent's belief in the complement is the
precondition of the emotive state, veridicality being a default rather than a
precondition. -/
def emotive (believes regrets : W → Prop) : EventPhase W where
  precondition := believes
  eventOccurs := regrets
  consequence := regrets

/-- A selectional restriction as an event type: the requirement is a precondition of the
event. -/
def selectional (requirement event : W → Prop) : EventPhase W where
  precondition := requirement
  eventOccurs := event
  consequence := event

/-- *Discover* carries the factive precondition together with prior ignorance, the extra
precondition that lets its factive implication be suppressed where *know*'s is not. -/
theorem discover_precondition (complement ignorant knows : W → Prop) (w : W) :
    (discover complement ignorant knows).precondition w ↔
      (factive complement knows).precondition w ∧ ignorant w :=
  Iff.rfl

/-- The projective implications of all three classes are their preconditions, shared by the
affirmative and the negative sentence. -/
theorem precondition_projects (e : EventPhase W) (w : W) :
    (negative e).presupposition w ↔ e.precondition w :=
  Iff.rfl

/-! ### Projection as a pragmatic default and its suppression -/

variable (C : Set W) (s : EventSentence W)

/-- The projective reading: the speaker is taken to presume a context entailing the
precondition of the event they raise. -/
def Presumes : Prop := C ⊆ {w | s.presupposition w}

/-- Suppression where the precondition is taken to be false: a nonempty context settling the
precondition negatively admits no projective reading, and the precondition is merely
locally entailed. -/
theorem not_presumes_of_settled_false (hC : C.Nonempty)
    (h : C ⊆ {w | ¬ s.presupposition w}) : ¬ Presumes C s :=
  λ hp => let ⟨_, hw⟩ := hC; h hw (hp hw)

/-- Suppression where the speaker is uncommitted: a speaker whose commitments leave the
precondition open cannot be presuming it. -/
theorem not_presumes_of_open (hopen : ∃ w ∈ C, ¬ s.presupposition w) : ¬ Presumes C s :=
  λ hp => let ⟨_, hw, hn⟩ := hopen; hn (hp hw)

/-- Suppression where the precondition is at issue: presuming a precondition that is one of
the alternatives of the question under discussion resolves that question, which a speaker
still addressing it cannot do. -/
theorem resolves_of_presumes {Q : Question W} (h : {w | s.presupposition w} ∈ alt Q)
    (hp : Presumes C s) : C ∈ Q :=
  mem_of_exists_alt_subset ⟨_, h, hp⟩

/-! ### Filtering -/

/-- The filtering constructions (41), (42), (43): the trigger in the second conjunct, in the
consequent, or in a disjunct. -/
inductive Construction
  | conjunction
  | conditional
  | disjunction
  deriving DecidableEq, Fintype

/-- The local context of the trigger: the context updated with the first conjunct, with the
antecedent, or with the negation of the other disjunct. -/
def localContext (A : Set W) : Construction → Set W
  | .conjunction => C ∩ A
  | .conditional => C ∩ A
  | .disjunction => C ∩ Aᶜ

/-- Filtering: where the first clause asserts or supposes the precondition, or the other
disjunct is its negation, the trigger's local context entails the precondition, so no
global presumption is attributable to the speaker; in disjunction the condition concerns the
other disjunct whichever comes first. -/
theorem localContext_subset {A pre : Set W} :
    (A ⊆ pre → localContext C A .conjunction ⊆ pre ∧ localContext C A .conditional ⊆ pre) ∧
      (Aᶜ ⊆ pre → localContext C A .disjunction ⊆ pre) :=
  ⟨λ h => ⟨λ _ hw => h hw.2, λ _ hw => h hw.2⟩, λ h _ hw => h hw.2⟩

/-- The contrast in (44): in a context that leaves the precondition open, a disjunctive
antecedent whose other disjunct negates the precondition filters it, whereas a simple
antecedent leaves the precondition to be presumed globally, which the open context
forbids. -/
theorem disjunctive_antecedent_filters {pre : Set W} (hopen : ¬ C ⊆ pre) :
    localContext C preᶜ .disjunction ⊆ pre ∧ ¬ localContext C Set.univ .conditional ⊆ pre :=
  ⟨λ _ hw => not_not.mp hw.2, λ h => hopen λ _ hw => h ⟨hw, trivial⟩⟩

end RobertsSimons2024
