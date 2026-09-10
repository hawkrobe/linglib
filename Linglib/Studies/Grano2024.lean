import Linglib.Semantics.Mood.Eventuality
import Linglib.Data.Examples.Grano2024
import Mathlib.Data.Set.Basic

/-!
# Grano (2024): Intention Reports and Eventuality Abstraction in a Theory of Mood Choice

This file formalizes [grano-2024]'s account of why 'intend' accepts nonfinite and subjunctive
complements but rejects indicative ones across Spanish, French, Portuguese, Italian, Greek,
Romanian, and English, as 'want' does and as 'hope' does not (Table 1). Three premises carry the
argument: intention reports have causally self-referential content ([searle-1983],
[harman-1976]), an intention being carried out only if it causes the outcome in the right way;
encoding that content takes abstraction over the complement's eventuality argument, since
causation relates eventualities; and subjunctive and nonfinite clauses leave that argument open
where the indicative closes it (`Mood.Grammatical.eventDenotation`). The pool of the paper's judged
complements records each predicate's class, the complement type, and where it matters the
reading, and `abstraction_rejects_indicative` checks the conclusion over every row that requires
abstraction: intention reports, causatives, the intention-rigid *aim* and *try*, aspectual
predicates, the intention readings of *persuade*, *decide*, *promise*, and *plan*, and the event
readings of memory and perception reports. Section 3's case against [portner-rubinstein-2020]
and [giannakidou-mari-2021] is `intend_like_hope_in_logic`: on realism, consistency, and
monotonicity 'intend' patterns with 'hope', whose indicative those theories license by that very
profile, yet every indicative row under 'intend' is rejected. The Hintikka semantics of (73)
derives the three properties from the overlap of intention and doxastic alternatives (`realism`
and its siblings), and section 7's synthesis reads the availability of the indicative off the two
departures from default clausal semantics, a pair of modal backgrounds and eventuality
abstraction (`indicative_possible_iff`).

## Implementation notes

Whether a class needs eventuality abstraction is the paper's premise per class; for the hybrid,
commissive, *plan*, memory, and perception predicates the reading of the row decides. The
simplification condition of [portner-rubinstein-2020] is read off the consistency rows: a pair of
backgrounds may collapse when the class rejects inconsistent prejacents. French *faire* with
indicative complements, (43a) and (44b), which the paper leaves as open exceptions, is not in the
pool, and the paper's remarks on nominal *avoir l'intention* and on French and Italian rejecting
non-control complements under 'intend' altogether are recorded as rows without a theorem.

## References

* [grano-2024]
* [portner-rubinstein-2020]
* [silk-2018]
* [giannakidou-mari-2021]
* [searle-1983]
* [harman-1976]
* [heim-1992]
* [jackendoff-culicover-2003]
* [higginbotham-1983]
-/

namespace Grano2024

open Data.Examples Features Mood

/-! ### The pool -/

/-- The predicate classes of the pool. -/
inductive Class where
  | want
  | hope
  | intend
  | causative
  /-- *aim*, *try*, *endeavor*, *strive*, *seek*, section 6.1. -/
  | intentionRigid
  /-- *persuade*, *convince*, *decide*: intention with a nonfinite or subjunctive complement,
  belief with an indicative one. -/
  | hybrid
  /-- *promise*, *agree*, *pledge*, *swear*: a commissive or an assertion by the same split. -/
  | commissive
  | plan
  | aspectual
  | memory
  | perception
  deriving DecidableEq, Repr, Fintype

/-- The complement types of the pool. -/
inductive Complement where
  | indicative
  | subjunctive
  | infinitive
  | forTo
  | gerund
  | bareInfinitive
  deriving DecidableEq, Repr, Fintype

/-- Premise 3: every complement type but the indicative leaves its eventuality argument open. -/
def Complement.Abstracts (c : Complement) : Prop := c ≠ .indicative

instance (c : Complement) : Decidable c.Abstracts := inferInstanceAs (Decidable (_ ≠ _))

/-- The reading a row is judged on, where the predicate has more than one. -/
inductive Reading where
  | intention
  | belief
  | assertion
  /-- *plan* as 'regard as fixed for planning purposes', section 6.1. -/
  | foresee
  | event
  | proposition
  deriving DecidableEq, Repr

/-- The logical diagnostics of section 3: an impossible prejacent, two incompatible prejacents,
and a prejacent with a rejected superset. -/
inductive Diagnostic where
  | realism
  | consistency
  | monotonicity
  deriving DecidableEq, Repr, Fintype

/-- A judged complement clause. -/
structure Row where
  cls : Class
  complement : Complement
  reading : Option Reading
  diagnostic : Option Diagnostic
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let cls ← ex.parse? "class"
    [("want", Class.want), ("hope", .hope), ("intend", .intend), ("causative", .causative),
      ("intentionRigid", .intentionRigid), ("hybrid", .hybrid), ("commissive", .commissive),
      ("plan", .plan), ("aspectual", .aspectual), ("memory", .memory), ("perception", .perception)]
  let complement ← ex.parse? "complement"
    [("indicative", Complement.indicative), ("subjunctive", .subjunctive),
      ("infinitive", .infinitive), ("forTo", .forTo), ("gerund", .gerund),
      ("bareInfinitive", .bareInfinitive)]
  pure ⟨cls, complement,
    ex.parse? "reading"
      [("intention", Reading.intention), ("belief", .belief), ("assertion", .assertion),
        ("foresee", .foresee), ("event", .event), ("proposition", .proposition)],
    ex.parse? "diagnostic"
      [("realism", Diagnostic.realism), ("consistency", .consistency),
        ("monotonicity", .monotonicity)],
    ex.judgment⟩

/-- The paper's judged complements, sections 2, 3, 6, and 7. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-! ### Premises 1 and 2 and the conclusion, over the pool -/

/-- The classes whose semantics relates to an eventuality: intention through the causal
self-reference of Premises 1 and 2, causation, the intention-rigid predicates, and aspect. -/
def Class.RequiresAbstraction (c : Class) : Prop :=
  c = .intend ∨ c = .causative ∨ c = .intentionRigid ∨ c = .aspectual

instance : DecidablePred Class.RequiresAbstraction := λ c => by
  unfold Class.RequiresAbstraction; infer_instance

/-- A row requires eventuality abstraction by its class or by an intention or event reading. -/
def Row.RequiresAbstraction (r : Row) : Prop :=
  r.cls.RequiresAbstraction ∨ r.reading = some .intention ∨ r.reading = some .event

instance : DecidablePred Row.RequiresAbstraction := λ r => by
  unfold Row.RequiresAbstraction; infer_instance

/-- The conclusion (72d) over the pool: wherever abstraction is required the indicative is
rejected, and where the same predicate takes an indicative complement it is read as belief,
assertion, foresight, or a proposition instead. -/
theorem abstraction_rejects_indicative :
    ∀ r ∈ rows, r.RequiresAbstraction → r.complement = .indicative →
      r.judgment ≠ .acceptable := by
  decide +kernel

/-- Each class that requires abstraction has an acceptable open complement in the pool. -/
theorem abstraction_accepts_open :
    ∀ c : Class, c.RequiresAbstraction →
      ∃ r ∈ rows, r.cls = c ∧ r.complement.Abstracts ∧ r.judgment = .acceptable := by
  decide +kernel

/-- 'want' rejects the indicative throughout, the idle desire of (128) included. -/
theorem want_rejects_indicative :
    ∀ r ∈ rows, r.cls = .want → r.complement = .indicative → r.judgment ≠ .acceptable := by
  decide +kernel

/-- 'hope' varies: Spanish rejects the indicative, the other languages accept it. -/
theorem hope_varies :
    (∃ r ∈ rows, r.cls = .hope ∧ r.complement = .indicative ∧ r.judgment = .acceptable) ∧
      ∃ r ∈ rows, r.cls = .hope ∧ r.complement = .indicative ∧ r.judgment = .ungrammatical := by
  decide

/-! ### Section 3: the logical profile of 'intend' -/

/-- The class fails diagnostic `d` somewhere in the pool. -/
def Class.Fails (c : Class) (d : Diagnostic) : Prop :=
  ∃ r ∈ rows, r.cls = c ∧ r.diagnostic = some d ∧ r.judgment ≠ .acceptable

instance (c : Class) (d : Diagnostic) : Decidable (c.Fails d) := by
  unfold Class.Fails; infer_instance

/-- On realism, consistency, and monotonicity 'intend' patterns with 'hope' and against 'want',
yet on mood with 'want': the theories that license the indicative under 'hope' by that profile,
[portner-rubinstein-2020]'s simplification of consistent backgrounds and
[giannakidou-mari-2021]'s optional nonveridicality, predict it under 'intend' as well. -/
theorem intend_like_hope_in_logic :
    (∀ d, Class.hope.Fails d ∧ Class.intend.Fails d ∧ ¬ Class.want.Fails d) ∧
      (∃ r ∈ rows, r.cls = .hope ∧ r.complement = .indicative ∧ r.judgment = .acceptable) ∧
      ∀ r ∈ rows, r.cls = .intend → r.complement = .indicative → r.judgment ≠ .acceptable := by
  decide +kernel

/-! ### The semantics of intention reports, section 4

(73) quantifies over the worlds compatible with the agent's intentions; the one substantive
constraint is that they overlap the worlds compatible with the agent's beliefs, from which
realism, consistency, and monotonicity follow. (79) adds the de se triples, the intention state,
and the causal self-reference, relating the state by `causeStar` to an eventuality of the
complement, which therefore keeps its eventuality argument. -/

section Hintikka

variable {W : Type*}

/-- (73): the agent intends `p` at `w` when `p` holds throughout the intention alternatives. -/
def Intends (int : W → Set W) (p : Set W) (w : W) : Prop := int w ⊆ p

/-- Realism: what is intended is believed possible. -/
theorem realism {int dox : W → Set W} {p : Set W} {w : W} (h : (int w ∩ dox w).Nonempty)
    (hp : Intends int p w) : ∃ w' ∈ dox w, w' ∈ p :=
  let ⟨w', hw'⟩ := h
  ⟨w', hw'.2, hp hw'.1⟩

/-- Consistency: two intentions are believed jointly possible. -/
theorem consistency {int dox : W → Set W} {p q : Set W} {w : W} (h : (int w ∩ dox w).Nonempty)
    (hp : Intends int p w) (hq : Intends int q w) : ∃ w' ∈ dox w, w' ∈ p ∩ q :=
  let ⟨w', hw'⟩ := h
  ⟨w', hw'.2, hp hw'.1, hq hw'.1⟩

/-- Monotonicity: intending the narrower prejacent is intending the wider. -/
theorem monotonicity {int : W → Set W} {p q : Set W} {w : W} (hpq : p ⊆ q)
    (hp : Intends int p w) : Intends int q w :=
  hp.trans hpq

end Hintikka

/-- The ingredients of (79): intention states, their holders, their content as world, time,
and individual triples, causation in the right way between eventualities, and runtimes. -/
structure IntentionFrame (E W T Ev : Type*) where
  intention : Ev → W → Prop
  holder : E → Ev → W → Prop
  content : Ev → Set (W × T × E)
  causeStar : Ev → Ev → W → Prop
  runtime : Ev → T

/-- (79): `x` intends `P` at `w` when some intention state of `x` is such that, at every triple of
its content, the state causes in the right way a later eventuality satisfying `P`. The
complement is a predicate of individuals, times, worlds, and eventualities. -/
def IntentionFrame.Report {E W T Ev : Type*} [LT T] (F : IntentionFrame E W T Ev) (x : E)
    (P : E → T → W → Ev → Prop) (w : W) : Prop :=
  ∃ s, F.intention s w ∧ F.holder x s w ∧
    ∀ c ∈ F.content s, ∃ e, F.causeStar s e c.1 ∧ c.2.1 < F.runtime e ∧ P c.2.2 (F.runtime e) c.1 e

/-- What a mood's denotation of the complement offers a predicate that needs the eventuality:
the open predicate, or nothing once the argument is closed. -/
def openArgument {Ev : Type*} : EventDenotation Ev → Option (Ev → Prop)
  | .closed _ => none
  | .abstracted P => some P

/-- Premise 3 by the mood denotations (87) and (89): the indicative leaves nothing for `Report`
to take, the subjunctive passes the predicate up. -/
theorem indicative_closes_subjunctive_opens {Ev : Type*} (P : Ev → Prop) :
    openArgument (Grammatical.indicative.eventDenotation P) = none ∧
      openArgument (Grammatical.subjunctive.eventDenotation P) = some P :=
  ⟨rfl, rfl⟩

/-! ### Section 7: the two departures from default clausal semantics -/

/-- A class whose reports carry two modal backgrounds, the doxastic-like and the bouletic
([portner-rubinstein-2020]); 'intend' is taken to carry one, the paper's footnote 50. -/
def Class.TwoBackgrounds (c : Class) : Prop := c = .want ∨ c = .hope

instance : DecidablePred Class.TwoBackgrounds := λ c => by
  unfold Class.TwoBackgrounds; infer_instance

/-- [portner-rubinstein-2020]'s simplification read off the pool: the pair may collapse to one
background when the class requires its backgrounds to be consistent, that is, rejects
inconsistent prejacents. -/
def Class.Simplifiable (c : Class) : Prop := c.Fails .consistency

instance : DecidablePred Class.Simplifiable := λ c => by unfold Class.Simplifiable; infer_instance

/-- The indicative is available when neither departure is in force: no eventuality abstraction,
and a single background or a pair that may simplify. -/
def Class.IndicativePossible (c : Class) : Prop :=
  ¬ c.RequiresAbstraction ∧ (¬ c.TwoBackgrounds ∨ c.Simplifiable)

instance : DecidablePred Class.IndicativePossible := λ c => by
  unfold Class.IndicativePossible; infer_instance

/-- For the four classes of sections 2 and 3, the indicative is possible exactly when the pool
has an acceptable indicative complement for the class. -/
theorem indicative_possible_iff :
    ∀ c ∈ [Class.want, .hope, .intend, .causative],
      (c.IndicativePossible ↔
        ∃ r ∈ rows, r.cls = c ∧ r.complement = .indicative ∧ r.judgment = .acceptable) := by
  decide +kernel

end Grano2024
