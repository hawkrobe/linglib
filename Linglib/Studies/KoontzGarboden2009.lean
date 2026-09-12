import Linglib.Semantics.ArgumentStructure.VerbDenotation
import Linglib.Fragments.Spanish.Predicates

/-!
# Koontz-Garboden (2009): Anticausativization

This file formalizes the reflexivization analysis of anticausativization, the derivation of an
inchoative verb from its causative counterpart as in Spanish *romper* 'break (tr.)' ~
*romperse* 'break (intr.)'. The reflexive clitic denotes the operator `λℜλx[ℜ(x,x)]`
([chierchia-2004]), so a derived inchoative is its causative restricted to the diagonal and
keeps the CAUSE operator. Stated on the library's change-of-state decomposition
(`Verb.CosModel`), the analysis yields the paper's predictions as theorems. The single argument
of a derived inchoative is the causer of its own change, so a verb whose causer must be an
agent (*asesinar* 'assassinate') reflexivizes only to a reflexive-type reading, while a verb
whose causer is an underspecified EFFECTOR ([van-valin-wilkins-1996]; *romper*) also has the
anticausative reading. The causative does not entail the derived inchoative, although the
inchoative entails the causative with the undergoer as its own causer. And *por sí solo* 'by
itself', whose antecedent must be the effector of a causing subevent, is licensed by derived
inchoatives but not by passives or by the CAUSE-less representation of internally caused
verbs like *empeorar* 'worsen' ([rappaport-hovav-levin-1998]).

The paper's second claim concerns the Monotonicity Hypothesis, that word formation
operations never remove operators from lexical semantic representations. On the event
templates of `ArgumentStructure.EventStructure`, the inchoativization rule of [grimshaw-1982]
is `Template.intransitiveVariant`, which strips CAUSE from an accomplishment and so violates
the hypothesis, whereas reflexivization identifies two argument positions and leaves the
template intact.

## Implementation notes

The paper's representations take the change-of-state event as the verb's event argument and
existentially close the causing event; `causative` follows that convention, and
`exists_causative_iff` shows that its existential closure agrees with
`Verb.CosModel.causative`, whose event argument is the causing event. Agent entailments are an
explicit relation on the model, since `Verb.CosModel` has only the underspecified `effector`.
A Spanish verb's causer specification is derived from the proto-role subject profile the
fragment states for it ([dowty-1991]): a causer that must be an agent entails volition. The
reflexive/anticausative syncretism in the survey of [haspelmath-1990] that the paper
tabulates is a typological argument left in prose.

## References

* [koontz-garboden-2009]
* [chierchia-2004] — the reflexivization operator and *da sé* 'by itself'
* [van-valin-wilkins-1996] — the EFFECTOR role
* [grimshaw-1982], [reinhart-siloni-2005] — deletion analyses
* [levin-hovav-1995], [rappaport-hovav-levin-1998] — internally and externally caused
  change of state
* [dowty-1991] — proto-role entailments
* [haspelmath-1990] — the reflexive/anticausative syncretism
-/

namespace KoontzGarboden2009

open ArgumentStructure ArgumentStructure.EventStructure Spanish.Predicates

/-- The reflexivization operator (11): a two-place relation restricted to its diagonal. It is
the denotation of the reflexive clitic *se* (19). -/
def reflexivize {α β : Type*} (R : α → α → β) : α → β := λ x => R x x

section Model

variable {Entity State T : Type*} [LinearOrder T] (M : Verb.CosModel Entity State T)
  (θ agent : Entity → Event T → Prop) (v : Verb)

/-- A causative change-of-state verb ((10b), (17), (29)): an event `e` in which `x` comes to
be in the root's state, caused by an event whose participant `y` bears the causer relation
`θ`, the underspecified `M.effector` for *romper* and an agent relation for *asesinar*. -/
def causative (y x : Entity) (e : Event T) : Prop :=
  ∃ w, θ y w ∧ M.cause w e ∧ M.inchoative v x e

/-- Over the underspecified causer, `causative` and `Verb.CosModel.causative` have the same
existential closure; they differ only in which event is the verb's argument. -/
theorem exists_causative_iff (y x : Entity) :
    (∃ e, causative M M.effector v y x e) ↔ ∃ w, M.causative v y x w :=
  ⟨λ ⟨e, w, hθ, hc, hi⟩ => ⟨w, e, hθ, hc, hi⟩, λ ⟨w, e, hθ, hc, hi⟩ => ⟨e, w, hθ, hc, hi⟩⟩

/-- Anticausativization is reflexivization ((20)–(21), (31)): the derived inchoative is the
causative on its diagonal, so the undergoer is also the participant in the causing event. -/
def anticausative : Entity → Event T → Prop := reflexivize (causative M θ v)

theorem anticausative_iff (x : Entity) (e : Event T) :
    anticausative M θ v x e ↔ ∃ w, θ x w ∧ M.cause w e ∧ M.inchoative v x e := Iff.rfl

/-- The anticausative reading of a reflexivized verb: an instance whose single argument is not
an agent of the event causing its change, as in *el vaso se rompió* 'the cup broke'. -/
def AnticausativeReading (P : Entity → Event T → Prop) : Prop :=
  ∃ x e, P x e ∧ ∀ w, M.cause w e → ¬ agent x w

/-- *Por sí solo* 'by itself' ((54)) is licensed on a predicate that entails a causing subevent
with the subject as its effector; the modifier then adds that the subject is its sole
effector (§3.4, §4.1). -/
def LicensesBySelf (P : Entity → Event T → Prop) : Prop :=
  ∀ x e, P x e → ∃ w, M.cause w e ∧ M.effector x w

/-- The passive of a causative verb ((53a), (64)): the causer is existentially closed rather
than identified with the subject. -/
def passive (x : Entity) (e : Event T) : Prop := ∃ y, causative M M.effector v y x e

variable {M θ agent v}

/-- A derived inchoative entails the causative with its subject as its own causer, the special
kind of causative that §3.5 finds the inchoative to entail. -/
theorem causative_self_of_anticausative {x : Entity} {e : Event T}
    (h : anticausative M θ v x e) : causative M θ v x x e := h

/-- A derived inchoative retains a causing subevent whose causer is its subject: CAUSE
survives reflexivization (§4). -/
theorem exists_cause_of_anticausative {x : Entity} {e : Event T}
    (h : anticausative M θ v x e) : ∃ w, θ x w ∧ M.cause w e :=
  let ⟨w, hθ, hc, _⟩ := h; ⟨w, hθ, hc⟩

/-- Only verbs with a thematically underspecified causer anticausativize (§3.2): an
anticausative reading needs a causer relation satisfied by a non-agent. -/
theorem exists_nonagent_of_anticausativeReading
    (h : AnticausativeReading M agent (anticausative M θ v)) : ∃ x w, θ x w ∧ ¬ agent x w :=
  let ⟨x, _, ⟨w, hθ, hc, _⟩, hna⟩ := h; ⟨x, w, hθ, hna w hc⟩

/-- A verb whose causer must be an agent ((29), *asesinar*) reflexivizes to the reflexive-type
reading only ((27)–(28), (31)). -/
theorem not_anticausativeReading (hθ : ∀ x w, θ x w → agent x w) :
    ¬ AnticausativeReading M agent (anticausative M θ v) := λ h =>
  let ⟨x, w, h₁, h₂⟩ := exists_nonagent_of_anticausativeReading h; h₂ (hθ x w h₁)

/-- Derived inchoatives license *por sí solo* ((68)). -/
theorem licensesBySelf_anticausative : LicensesBySelf M (anticausative M M.effector v) :=
  λ _ _ h => let ⟨w, hθ, hc⟩ := exists_cause_of_anticausative h; ⟨w, hc, hθ⟩

end Model

/-! ### Juan and the glass

The model of (56)–(57) and (60): Juan breaks the glass. Whether the glass counts as an
effector of the causing event is a parameter; the denial in (56) has it that it does not,
the discourse in (60) that both the glass and Juan do. -/

/-- The participants. -/
inductive Participant
  | juan
  | vaso
  deriving DecidableEq

/-- Juan breaks the glass: `eff` says who counts as an effector of the causing event, and
every event gives rise to the glass's broken state. -/
def breaking (eff : Participant → Prop) : Verb.CosModel Participant Unit ℤ where
  rootState _ x _ := x = .vaso
  become _ _ := True
  cause _ _ := True
  effector y _ := eff y
  manner _ _ := False

/-- Juan alone is an agent. -/
def juanAgent (y : Participant) (_ : Event ℤ) : Prop := y = .juan

/-- The model of (56)–(57): Juan, not the glass, is the effector. -/
def breakingByJuan : Verb.CosModel Participant Unit ℤ := breaking (· = .juan)

/-- The model of (60): the glass and Juan are both effectors. -/
def breakingByBoth : Verb.CosModel Participant Unit ℤ := breaking λ _ => True

/-- An event of the models. -/
private def e₀ : Event ℤ := ⟨⟨(0, 0), le_rfl⟩, .action⟩

/-- The causative does not entail the derived inchoative ((56)–(57)): with Juan the only
effector, *Juan rompió el vaso* holds and *el vaso se rompió* fails. -/
theorem not_anticausative_of_causative :
    causative breakingByJuan breakingByJuan.effector romper.toVerb .juan .vaso e₀ ∧
      ¬ anticausative breakingByJuan breakingByJuan.effector romper.toVerb .vaso e₀ :=
  ⟨⟨e₀, rfl, trivial, (), trivial, rfl⟩, λ ⟨_, h, _⟩ => Participant.noConfusion h⟩

/-- *El vaso se rompió* has the anticausative reading: the glass is a non-agentive
effector of its own breaking. -/
theorem anticausativeReading_romper :
    AnticausativeReading breakingByBoth juanAgent
      (anticausative breakingByBoth breakingByBoth.effector romper.toVerb) :=
  ⟨.vaso, e₀, ⟨e₀, trivial, trivial, (), trivial, rfl⟩, λ _ _ h => Participant.noConfusion h⟩

/-- A passive does not license *por sí solo* ((53a), (64)): its subject need not be an
effector of the causing subevent. -/
theorem not_licensesBySelf_passive :
    ¬ LicensesBySelf breakingByJuan (passive breakingByJuan romper.toVerb) := λ h =>
  let ⟨_, _, hw⟩ := h .vaso e₀ ⟨.juan, e₀, rfl, trivial, (), trivial, rfl⟩
  Participant.noConfusion hw

/-- The CAUSE-less representation of an internally caused verb ((65), (67)), the library's
`Verb.CosModel.inchoative`, does not license *por sí solo*. -/
theorem not_licensesBySelf_inchoative :
    ¬ LicensesBySelf breakingByJuan (breakingByJuan.inchoative empeorar.toVerb) := λ h =>
  let ⟨_, _, hw⟩ := h .vaso e₀ ⟨(), trivial, rfl⟩
  Participant.noConfusion hw

/-! ### The Monotonicity Hypothesis -/

/-- The Monotonicity Hypothesis ((8)) for a word formation operation on event templates: the
output keeps CAUSE and BECOME wherever the input has them. -/
def MonotonicityHypothesis (f : Template → Option Template) : Prop :=
  ∀ t t', f t = some t' → (t.HasCause → t'.HasCause) ∧ (t.HasResultState → t'.HasResultState)

/-- The inchoativization rule of [grimshaw-1982] ((95)) is `Template.intransitiveVariant`,
which strips CAUSE from an accomplishment; it violates the hypothesis. -/
theorem not_monotonicityHypothesis_intransitiveVariant :
    ¬ MonotonicityHypothesis Template.intransitiveVariant :=
  λ h => (h .accomplishment .achievement rfl).1 trivial

/-- Reflexivization on templates: it identifies the external-causer position with the
undergoer, so it applies exactly to templates with that position and changes no operator. -/
def reflexivizeTemplate (t : Template) : Option Template :=
  if t.HasExternalCauser then some t else none

/-- Anticausativization as reflexivization satisfies the hypothesis. -/
theorem monotonicityHypothesis_reflexivizeTemplate :
    MonotonicityHypothesis reflexivizeTemplate := by
  intro t t' h
  unfold reflexivizeTemplate at h
  split at h
  · cases h; exact ⟨id, id⟩
  · exact absurd h (by simp)

/-! ### Spanish verbs -/

/-- The thematic specification of a verb's causer (§2.1): an underspecified EFFECTOR, or an
AGENT. -/
inductive Causer
  | effector
  | agent
  deriving DecidableEq, Repr

/-- The causer specification, derived from the verb's stated proto-role subject profile: a
causer that must be an agent entails volition, one that need only cause the change is an
EFFECTOR, and a subject that causes nothing is no causer. -/
def causer (v : Verb) : Option Causer :=
  v.subjectEntailments.bind λ p =>
    if p.volition then some .agent else if p.causation then some .effector else none

/-- Only causative verbs with underspecified causers have derived inchoatives (§3.1–§3.2):
among the fragment's verbs that have a causer, the alternating ones are the EFFECTOR verbs. -/
theorem alternates_iff_effector :
    ∀ v ∈ allVerbs, ∀ c ∈ causer v.toVerb, (v.causativeAlternation = true ↔ c = .effector) := by
  decide

end KoontzGarboden2009
