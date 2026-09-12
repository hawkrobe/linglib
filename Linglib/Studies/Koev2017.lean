import Linglib.Semantics.Events.Basic
import Linglib.Semantics.Presupposition.Basic

/-!
# Koev (2017): Evidentiality, Learning Events and Spatiotemporal Distance

This file formalizes [koev-2017]'s account of the Bulgarian evidential *-l* as a spatiotemporal
distance rather than a semantic primitive: an evidential sentence introduces a learning event,
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

* `Event T` carries no location, so the distance predicate takes a location function as a
  parameter.
* The learning predicate itself, the knowledge change it reports, and the evidence-source
  typology of §5 are not modelled; the scenarios record only the two events.

## References

* [koev-2017]
* [izvorski-1997]
-/

namespace Koev2017

open Presupposition

variable {T : Type*} [LinearOrder T] {L : Type*}

/-- Two events are temporally disjoint when their temporal traces do not overlap, the first
disjunct of Definition 24. -/
def temporallyDisjoint (e₁ e₂ : Event T) : Prop := ¬ e₁.τ.overlaps e₂.τ

/-- Spatiotemporal distance, Definition 24: the events do not overlap in time or occur at
different locations. -/
def spatiotemporallyDistant (loc : Event T → L) (e₁ e₂ : Event T) : Prop :=
  temporallyDisjoint e₁ e₂ ∨ loc e₁ ≠ loc e₂

instance [DecidableEq T] (e₁ e₂ : Event T) : Decidable (temporallyDisjoint e₁ e₂) :=
  inferInstanceAs (Decidable (¬ e₁.τ.overlaps e₂.τ))

instance [DecidableEq T] [DecidableEq L] (loc : Event T → L) (e₁ e₂ : Event T) :
    Decidable (spatiotemporallyDistant loc e₁ e₂) :=
  inferInstanceAs (Decidable (temporallyDisjoint e₁ e₂ ∨ loc e₁ ≠ loc e₂))

/-- An event that precedes another is temporally disjoint from it: standard indirect evidence,
the described event over before the learning event begins. -/
theorem temporallyDisjoint_of_precedes {e₁ e₂ : Event T} (h : e₁.τ.precedes e₂.τ) :
    temporallyDisjoint e₁ e₂ :=
  NonemptyInterval.precedes_not_overlaps h

/-- A learning scenario: the described event and the learning event through which the speaker
acquired the evidence for the claim, (74b). -/
structure LearningScenario (T : Type*) [LinearOrder T] where
  described : Event T
  learning : Event T

/-- The evidential sentence as a partial proposition: the distance condition of the learning
event restricts the context set, (74b), and the declarative operator (72) commits the speaker
to the core proposition itself. -/
def LearningScenario.toEvidentialProp (loc : Event T → L) (s : LearningScenario T) {W : Type*}
    (p : W → Prop) : PartialProp W where
  presup := λ _ => spatiotemporallyDistant loc s.described s.learning
  assertion := p

/-- Projection, (78): negation preserves the evidential presupposition while negating the
core proposition. -/
theorem projection_past_negation (loc : Event T → L) (s : LearningScenario T) {W : Type*}
    (p : W → Prop) :
    (s.toEvidentialProp loc p).neg.presup = (s.toEvidentialProp loc p).presup :=
  PartialProp.neg_presup _

/-! ### The scenarios of §4 -/

/-- A place for the events of the scenarios. -/
inductive Place
  | here
  | there
  deriving DecidableEq, Repr

/-- The described event, over the interval `[0, 5]`. -/
def described : Event ℤ := ⟨⟨⟨0, 5⟩, by omega⟩, .action⟩

/-- Standard indirect evidence, (25a): the speaker learns of the event afterwards. -/
def indirect : LearningScenario ℤ := ⟨described, ⟨⟨⟨10, 15⟩, by omega⟩, .state⟩⟩

/-- Direct witness: the speaker perceives the event as it happens, in the same place. -/
def direct : LearningScenario ℤ := ⟨described, ⟨⟨⟨2, 4⟩, by omega⟩, .state⟩⟩

/-- Smoke from the chimney, (25b): the speaker perceives the evidence at the same time from
elsewhere. -/
def smoke : LearningScenario ℤ := ⟨described, ⟨⟨⟨0, 5⟩, by omega⟩, .state⟩⟩

/-- The location of every event is `here` except the smoke scenario's learning event, the
one state that runs alongside the described event. -/
def loc (e : Event ℤ) : Place := if e.sort = .state ∧ e.τ.fst = 0 then .there else .here

/-- The evidential is felicitous with indirect evidence, by temporal disjointness, and with
smoke from the chimney, by spatial distance alone, and infelicitous under direct witness. -/
theorem felicity :
    spatiotemporallyDistant loc indirect.described indirect.learning ∧
      spatiotemporallyDistant loc smoke.described smoke.learning ∧
      ¬ spatiotemporallyDistant loc direct.described direct.learning := by
  decide

/-- Direct witness fails both disjuncts of Definition 24. -/
theorem direct_not_distant (loc : Event ℤ → L) (h : loc direct.described = loc direct.learning) :
    ¬ spatiotemporallyDistant loc direct.described direct.learning := by
  rintro (hd | hl)
  · exact hd (by decide)
  · exact hl h

/-- The two constraints of (74b) are independent: past tense orders the described event before
the learning event in the indirect scenario, while the smoke scenario satisfies the distance
condition with the two events simultaneous. -/
theorem smoke_no_tense_ordering :
    indirect.described.τ.precedes indirect.learning.τ ∧
      ¬ smoke.described.τ.precedes smoke.learning.τ ∧
      temporallyDisjoint indirect.described indirect.learning ∧
      ¬ temporallyDisjoint smoke.described smoke.learning := by
  decide

end Koev2017
