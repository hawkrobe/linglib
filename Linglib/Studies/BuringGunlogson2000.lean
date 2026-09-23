module

public import Linglib.Semantics.Questions.Bias
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Fragments.German.PolarityItems

/-!
# Büring and Gunlogson 2000: aren't positive and negative polar questions the same?

This file formalizes the felicity conditions of [buring-gunlogson-2000]. Standard question
semantics gives *Is she left-handed?*, *Isn't she left-handed?* and *Is she right-handed?* one and
the same denotation, yet the three types are felicitous in different contexts: a positive question
is barred by compelling contextual evidence against its proposition, an inner-negation question
requires such evidence, and an outer-negation question is barred by evidence for it. The paper's
appendix derives all three from one proto-condition applied to the question's proposition, to its
negation, or negated in turn, and the morphosyntactic probes of [ladd-1981] — *kein* vs *nicht
ein*, *no* vs *not some*, and the polarity items they admit — classify a question independently of
those judgements.

The three question types are the substrate's `PQForm`: `posQ` is the paper's PPQ, `loNQ` its
inner-negation NPQ, `hiNQ` its outer-negation NPQ. The contextual evidence of a situation is the
sign of `p` it supports, and reading it relative to `¬p` negates it.

## Main definitions

* `E`, `Felicitous` — the proto-condition and the felicity condition of each question type
* `Determiner`, `Question` — the morphosyntactic probes and a probed question; the polarity items
  are the fragments' `either_npi`, `too` and `brauchen`

## Main results

* `posQ_condition`, `hiNQ_condition`, `loNQ_condition` — the three evidence conditions
* `felicity_separates_forms` — no two question types share a felicity profile
* `outer_is_interrogative_only` — only inner-negation determiners occur in declaratives
* `form_eq_loNQ_of_isNPI`, `form_eq_hiNQ_of_isPPI` — a polarity item forces the reading the
  determiner gives

## References

* [buring-gunlogson-2000]
* [ladd-1981]
* [hamblin-1973b]
-/

@[expose] public section

namespace BuringGunlogson2000

open Question
open English.PolarityItems (either_npi too)
open German.PolarityItems (brauchen)

/-! ### Compelling contextual evidence -/

/-- Compelling evidence for `p`: evidence that would on its own justify the inference that `p`. -/
def CompellingFor (ev : SignType) : Prop := ev = 1

/-- Compelling evidence against `p`: compelling evidence for `¬p`, the evidence read relative to
`¬p`. -/
def CompellingAgainst (ev : SignType) : Prop := CompellingFor (-ev)

instance (ev : SignType) : Decidable (CompellingFor ev) :=
  inferInstanceAs (Decidable (_ = _))

instance (ev : SignType) : Decidable (CompellingAgainst ev) :=
  inferInstanceAs (Decidable (CompellingFor _))

/-! ### The evidence conditions -/

/-- The proto-condition: there is no compelling contextual evidence against `p`. -/
def E (ev : SignType) : Prop := ¬ CompellingAgainst ev

instance (ev : SignType) : Decidable (E ev) := inferInstanceAs (Decidable ¬ _)

/-- The felicity condition of each question type, as one proto-condition applied three ways: a
positive question imposes it on its own proposition, an outer-negation question on the negation,
and an inner-negation question imposes its negation. -/
def Felicitous : PQForm → SignType → Prop
  | .posQ, ev => E ev
  | .loNQ, ev => ¬ E ev
  | .hiNQ, ev => E (-ev)

instance : ∀ (f : PQForm) (ev : SignType), Decidable (Felicitous f ev)
  | .posQ, ev => inferInstanceAs (Decidable (E ev))
  | .loNQ, ev => inferInstanceAs (Decidable ¬ E ev)
  | .hiNQ, ev => inferInstanceAs (Decidable (E (-ev)))

/-- A positive question requires no compelling evidence against `p`. -/
theorem posQ_condition (ev : SignType) :
    Felicitous .posQ ev ↔ ¬ CompellingAgainst ev := Iff.rfl

/-- An outer-negation question requires no compelling evidence *for* `p`. -/
theorem hiNQ_condition (ev : SignType) :
    Felicitous .hiNQ ev ↔ ¬ CompellingFor ev := by
  decide +revert

/-- An inner-negation question requires compelling evidence against `p`. -/
theorem loNQ_condition (ev : SignType) :
    Felicitous .loNQ ev ↔ CompellingAgainst ev := by
  decide +revert

/-- A positive question is barred by compelling evidence against `p` — *Is it sunny?* asked of
someone in a dripping raincoat. -/
theorem posQ_infelicitous_against : ¬ Felicitous .posQ (-1) := by decide

/-- An inner-negation question is felicitous only against `p`, the neutral context included in the
exclusion. -/
theorem loNQ_only_against (ev : SignType) : Felicitous .loNQ ev ↔ ev = -1 := by
  decide +revert

/-- An outer-negation question tolerates a neutral context, unlike an inner-negation one. -/
theorem hiNQ_neutral_loNQ_not : Felicitous .hiNQ 0 ∧ ¬ Felicitous .loNQ 0 := by decide

/-- No two question types share a felicity profile: the predicted synonymies of a Hamblin
denotation ([hamblin-1973b]) are not real. -/
theorem felicity_separates_forms (f g : PQForm) (h : ∀ ev, Felicitous f ev ↔ Felicitous g ev) :
    f = g := by
  cases f <;> cases g <;>
    first
      | rfl
      | exact absurd (h 0) (by decide)
      | exact absurd (h 1) (by decide)

/-! ### The morphosyntactic probes -/

/-- Where the negation sits relative to the questioned proposition. -/
inductive Scope | inner | outer
  deriving DecidableEq

/-- The negative determiners that probe the distinction: German *kein* and *nicht ein*, English
*no* and *not some*. -/
inductive Determiner | kein | nichtEin | no | notSome
  deriving DecidableEq

/-- *nicht ein* and *not some* leave the negation outside the questioned proposition; *kein* and
*no* place it inside. -/
def Determiner.scope : Determiner → Scope
  | .kein | .no => .inner
  | .nichtEin | .notSome => .outer

/-- Whether the determiner also occurs in a declarative. The non-amalgamated forms do not, even
under rising intonation. -/
def Determiner.declarativeOK : Determiner → Prop
  | .kein | .no => True
  | .nichtEin | .notSome => False

instance : ∀ d : Determiner, Decidable d.declarativeOK
  | .kein | .no => inferInstanceAs (Decidable True)
  | .nichtEin | .notSome => inferInstanceAs (Decidable False)

/-- An outer-negation construal is confined to the syntactic category of interrogative: exactly the
determiners that fail in declaratives are the outer-negation ones. -/
theorem outer_is_interrogative_only (d : Determiner) : d.scope = .outer ↔ ¬ d.declarativeOK := by
  cases d <;> decide

/-- A polar question as its two probes: a negative determiner and, optionally, a polarity item,
English *either* or *too* or German *brauchen*. -/
structure Question where
  determiner : Determiner
  item : Option PolarityItem

/-- The probes agree on where the negation sits: a negative polarity item must sit under it, so it
requires the inner construal, and a positive polarity item must escape it, so it requires the outer
one. -/
def Question.WellFormed (q : Question) : Prop :=
  ∀ e ∈ q.item, (e.isNPI → q.determiner.scope = .inner) ∧ (e.isPPI → q.determiner.scope = .outer)

instance : ∀ q : Question, Decidable q.WellFormed
  | ⟨_, none⟩ => isTrue (by simp [Question.WellFormed])
  | ⟨d, some e⟩ =>
    decidable_of_iff ((e.isNPI → d.scope = .inner) ∧ (e.isPPI → d.scope = .outer))
      (by simp [Question.WellFormed])

/-- The question type a well-formed question realizes: inner negation is an inner-negation NPQ,
outer negation an outer-negation one. -/
def Scope.form : Scope → PQForm
  | .inner => .loNQ
  | .outer => .hiNQ

/-- *Is there no vegetarian restaurant either/\*too?* (14a): the inner-negation determiner takes
the negative polarity item and refuses the positive one. -/
theorem no_takes_either_not_too :
    (Question.mk .no (some either_npi)).WellFormed ∧
      ¬ (Question.mk .no (some too)).WellFormed := by decide

/-- *Isn't there some vegetarian restaurant \*either/too?* (14b): the outer-negation determiner
takes the positive polarity item and refuses the negative one. -/
theorem notSome_takes_too_not_either :
    (Question.mk .notSome (some too)).WellFormed ∧
      ¬ (Question.mk .notSome (some either_npi)).WellFormed := by decide

/-- *Brauchst du keine/\*nicht eine Entschuldigung mitzubringen?* (16): the German NPI likewise
goes with the amalgamated determiner only. -/
theorem brauchen_takes_kein_not_nichtEin :
    (Question.mk .kein (some brauchen)).WellFormed ∧
      ¬ (Question.mk .nichtEin (some brauchen)).WellFormed := by decide

/-- A negative polarity item forces the inner-negation reading (13a): in a well-formed question
the determiner makes it a `loNQ`. -/
theorem form_eq_loNQ_of_isNPI {d : Determiner} {e : PolarityItem} (he : e.isNPI)
    (h : (Question.mk d (some e)).WellFormed) : d.scope.form = .loNQ := by
  rw [((h e rfl).1 he)]; rfl

/-- A positive polarity item forces the outer-negation reading (13b): in a well-formed question
the determiner makes it an `hiNQ`. -/
theorem form_eq_hiNQ_of_isPPI {d : Determiner} {e : PolarityItem} (he : e.isPPI)
    (h : (Question.mk d (some e)).WellFormed) : d.scope.form = .hiNQ := by
  rw [((h e rfl).2 he)]; rfl

end BuringGunlogson2000
