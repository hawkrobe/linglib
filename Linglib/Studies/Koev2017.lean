module

public import Linglib.Semantics.Events.Basic
public import Linglib.Semantics.Presupposition.Basic

/-!
# Koev (2017): Evidentiality, Learning Events and Spatiotemporal Distance

[koev-2017] accounts for the Bulgarian evidential *-l* as spatiotemporal distance rather than a
semantic primitive: an evidential sentence introduces a learning event,
the event through which the speaker acquired the evidence for the claim, and requires that it
be spatiotemporally distant from the described event, either not overlapping it in time, as
with standard indirect evidence, or located elsewhere, as when smoke from a chimney shows a
fire in progress (`spatiotemporallyDistant`, Definition 24). Direct witness, the same time and
the same place, is the one configuration the evidential excludes (`direct_not_distant`). The
distance constraint is independent of the temporal ordering that past tense contributes: the
smoke scenario satisfies it with no ordering at all (`smoke_no_tense_ordering`). The evidential
implication is not at issue and projects: in the representation (74b) the learning event
restricts the context set while the declarative operator (72) commits the speaker to the core
proposition itself, so the distance condition is the presupposition of a partial proposition
whose assertion is that proposition, and negation preserves it, (78) (`toEvidentialProp`,
`projection_past_negation`). No modal weakening of the assertion is involved, against
[izvorski-1997].

## Implementation notes

* Events carry no location, so the distance predicate takes a location function as a
  parameter.
* The learning predicate itself, the knowledge change it reports, and the evidence-source
  typology of §5 are not modelled; the scenarios record only the two events.

## References

* [koev-2017]
* [izvorski-1997]
-/

@[expose] public section

namespace Koev2017

open Event (τ)

open Presupposition

variable {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {L : Type*}

/-- Two events are temporally disjoint when their temporal traces do not overlap, the first
disjunct of Definition 24. -/
def temporallyDisjoint (e₁ e₂ : E) : Prop := ¬ (τ e₁).overlaps (τ e₂)

/-- Spatiotemporal distance, Definition 24: the events do not overlap in time or occur at
different locations. -/
def spatiotemporallyDistant (loc : E → L) (e₁ e₂ : E) : Prop :=
  temporallyDisjoint e₁ e₂ ∨ loc e₁ ≠ loc e₂

instance [DecidableEq T] (e₁ e₂ : E) : Decidable (temporallyDisjoint e₁ e₂) :=
  inferInstanceAs (Decidable (¬ (τ e₁).overlaps (τ e₂)))

instance [DecidableEq T] [DecidableEq L] (loc : E → L) (e₁ e₂ : E) :
    Decidable (spatiotemporallyDistant loc e₁ e₂) :=
  inferInstanceAs (Decidable (temporallyDisjoint e₁ e₂ ∨ loc e₁ ≠ loc e₂))

/-- An event that precedes another is temporally disjoint from it, as in standard indirect
evidence, where the described event is over before the learning event begins. -/
theorem temporallyDisjoint_of_precedes {e₁ e₂ : E} (h : (τ e₁).precedes (τ e₂)) :
    temporallyDisjoint e₁ e₂ :=
  NonemptyInterval.precedes_not_overlaps h

/-- A learning scenario pairs the described event with the learning event through which the
speaker acquired the evidence for the claim, (74b). -/
structure LearningScenario (E : Type*) where
  /-- The described event. -/
  described : E
  /-- The learning event. -/
  learning : E

/-- The evidential sentence is a partial proposition whose presupposition is the distance
condition of the learning event, which restricts the context set, (74b), and whose assertion
is the core proposition, to which the declarative operator (72) commits the speaker. -/
def LearningScenario.toEvidentialProp (loc : E → L) (s : LearningScenario E) {W : Type*}
    (p : W → Prop) : PartialProp W where
  presup := λ _ => spatiotemporallyDistant loc s.described s.learning
  assertion := p

/-- Negation preserves the evidential presupposition while negating the core proposition,
(78). -/
theorem projection_past_negation (loc : E → L) (s : LearningScenario E) {W : Type*}
    (p : W → Prop) :
    (s.toEvidentialProp loc p).neg.presup = (s.toEvidentialProp loc p).presup :=
  PartialProp.neg_presup _

/-! ### The scenarios of §4 -/

/-- A place for the events of the scenarios. -/
inductive Place
  | here
  | there
  deriving DecidableEq, Repr

/-- The events of the scenarios are the described event and the learning events of standard
indirect evidence, of direct witness, and of seeing smoke from the chimney. -/
inductive Ev
  | described
  | learnIndirect
  | learnDirect
  | learnSmoke
  deriving DecidableEq, Repr

/-- The described event runs over `[0, 5]`; the speaker learns of it afterwards, witnesses it
during `[2, 4]`, or sees the smoke over the same interval `[0, 5]`. -/
instance : Event.TemporalTrace Ev ℤ where
  τ
    | .described => ⟨(0, 5), by decide⟩
    | .learnIndirect => ⟨(10, 15), by decide⟩
    | .learnDirect => ⟨(2, 4), by decide⟩
    | .learnSmoke => ⟨(0, 5), by decide⟩

/-- In standard indirect evidence, (25a), the speaker learns of the event afterwards. -/
def indirect : LearningScenario Ev := ⟨.described, .learnIndirect⟩

/-- In direct witness the speaker perceives the event as it happens, in the same place. -/
def direct : LearningScenario Ev := ⟨.described, .learnDirect⟩

/-- With smoke from the chimney, (25b), the speaker perceives the evidence at the same time
from elsewhere. -/
def smoke : LearningScenario Ev := ⟨.described, .learnSmoke⟩

/-- The two events of the smoke scenario are distinct and simultaneous. -/
example : smoke.described ≠ smoke.learning ∧ τ smoke.described = τ smoke.learning :=
  ⟨by decide, rfl⟩

/-- The location of every event is `here` except the seeing of the smoke. -/
def loc : Ev → Place
  | .learnSmoke => .there
  | _ => .here

/-- The evidential is felicitous with indirect evidence, by temporal disjointness, and with
smoke from the chimney, by spatial distance alone, and infelicitous under direct witness. -/
theorem felicity :
    spatiotemporallyDistant loc indirect.described indirect.learning ∧
      spatiotemporallyDistant loc smoke.described smoke.learning ∧
      ¬ spatiotemporallyDistant loc direct.described direct.learning := by
  decide

/-- Direct witness fails both disjuncts of Definition 24. -/
theorem direct_not_distant (loc : Ev → L) (h : loc direct.described = loc direct.learning) :
    ¬ spatiotemporallyDistant loc direct.described direct.learning := by
  rintro (hd | hl)
  · exact hd (by decide)
  · exact hl h

/-- The two constraints of (74b) are independent: past tense orders the described event before
the learning event in the indirect scenario, while the smoke scenario satisfies the distance
condition with the two events simultaneous. -/
theorem smoke_no_tense_ordering :
    (τ indirect.described).precedes (τ indirect.learning) ∧
      ¬ (τ smoke.described).precedes (τ smoke.learning) ∧
      temporallyDisjoint indirect.described indirect.learning ∧
      ¬ temporallyDisjoint smoke.described smoke.learning := by
  decide

end Koev2017
