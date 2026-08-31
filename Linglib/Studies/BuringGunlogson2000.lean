import Linglib.Semantics.Questions.Bias

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

The three question types are the substrate's `PQForm`: `PosQ` is the paper's PPQ, `LoNQ` its
inner-negation NPQ, `HiNQ` its outer-negation NPQ.

## Main definitions

* `E`, `Felicitous` — the proto-condition and the felicity condition of each question type
* `Determiner`, `PolarityItem`, `Question` — the morphosyntactic probes and a probed question

## Main results

* `posQ_condition`, `hiNQ_condition`, `loNQ_condition` — the three evidence conditions
* `felicitous_iff_evidenceBiasOK` — the derived conditions are the substrate's bias table
* `felicity_separates_forms` — no two question types share a felicity profile
* `outer_is_interrogative_only` — only inner-negation determiners occur in declaratives
* `wellFormed_iff_determiner_form` — the determiner and the polarity item classify a question alike

## References

* [buring-gunlogson-2000]
* [ladd-1981]
* [hamblin-1973b]
-/

namespace BuringGunlogson2000

open Semantics.Questions.Bias

/-! ### Compelling contextual evidence -/

/-- The contextual evidence of a situation, read relative to `¬p` rather than `p`: evidence for `p`
is evidence against `¬p`. -/
def negate : ContextualEvidence → ContextualEvidence
  | .forP => .againstP
  | .neutral => .neutral
  | .againstP => .forP

@[simp] theorem negate_negate (ev : ContextualEvidence) : negate (negate ev) = ev := by
  cases ev <;> rfl

/-- Compelling evidence for `p`: evidence that would on its own justify the inference that `p`. -/
def CompellingFor (ev : ContextualEvidence) : Prop := ev = .forP

/-- Compelling evidence against `p`: compelling evidence for `¬p`. -/
def CompellingAgainst (ev : ContextualEvidence) : Prop := CompellingFor (negate ev)

instance (ev : ContextualEvidence) : Decidable (CompellingFor ev) :=
  inferInstanceAs (Decidable (_ = _))

instance (ev : ContextualEvidence) : Decidable (CompellingAgainst ev) :=
  inferInstanceAs (Decidable (CompellingFor _))

/-! ### The evidence conditions -/

/-- The proto-condition: there is no compelling contextual evidence against `p`. -/
def E (ev : ContextualEvidence) : Prop := ¬ CompellingAgainst ev

instance (ev : ContextualEvidence) : Decidable (E ev) := inferInstanceAs (Decidable ¬ _)

/-- The felicity condition of each question type, as one proto-condition applied three ways: a
positive question imposes it on its own proposition, an outer-negation question on the negation,
and an inner-negation question imposes its negation. -/
def Felicitous : PQForm → ContextualEvidence → Prop
  | .PosQ, ev => E ev
  | .LoNQ, ev => ¬ E ev
  | .HiNQ, ev => E (negate ev)

instance : ∀ (f : PQForm) (ev : ContextualEvidence), Decidable (Felicitous f ev)
  | .PosQ, ev => inferInstanceAs (Decidable (E ev))
  | .LoNQ, ev => inferInstanceAs (Decidable ¬ E ev)
  | .HiNQ, ev => inferInstanceAs (Decidable (E (negate ev)))

/-- A positive question requires no compelling evidence against `p`. -/
theorem posQ_condition (ev : ContextualEvidence) :
    Felicitous .PosQ ev ↔ ¬ CompellingAgainst ev := Iff.rfl

/-- An outer-negation question requires no compelling evidence *for* `p`. -/
theorem hiNQ_condition (ev : ContextualEvidence) :
    Felicitous .HiNQ ev ↔ ¬ CompellingFor ev := by
  cases ev <;> simp [Felicitous, E, CompellingAgainst, CompellingFor, negate]

/-- An inner-negation question requires compelling evidence against `p`. -/
theorem loNQ_condition (ev : ContextualEvidence) :
    Felicitous .LoNQ ev ↔ CompellingAgainst ev := by
  cases ev <;> simp [Felicitous, E, CompellingAgainst, CompellingFor, negate]

/-- The derived conditions are exactly the substrate's contextual-evidence bias table, so the three
rows of that table follow from the single proto-condition instead of being stipulated. -/
theorem felicitous_iff_evidenceBiasOK (f : PQForm) (ev : ContextualEvidence) :
    Felicitous f ev ↔ evidenceBiasOK f ev = true := by
  cases f <;> cases ev <;> decide

/-- A positive question is barred by compelling evidence against `p` — *Is it sunny?* asked of
someone in a dripping raincoat. -/
theorem posQ_infelicitous_against : ¬ Felicitous .PosQ .againstP := by decide

/-- An inner-negation question is felicitous only against `p`, the neutral context included in the
exclusion. -/
theorem loNQ_only_against (ev : ContextualEvidence) : Felicitous .LoNQ ev ↔ ev = .againstP := by
  cases ev <;> decide

/-- An outer-negation question tolerates a neutral context, unlike an inner-negation one. -/
theorem hiNQ_neutral_loNQ_not : Felicitous .HiNQ .neutral ∧ ¬ Felicitous .LoNQ .neutral := by decide

/-- No two question types share a felicity profile: the predicted synonymies of a Hamblin
denotation ([hamblin-1973b]) are not real. -/
theorem felicity_separates_forms (f g : PQForm) (h : ∀ ev, Felicitous f ev ↔ Felicitous g ev) :
    f = g := by
  cases f <;> cases g <;>
    first
      | rfl
      | exact absurd (h .neutral) (by decide)
      | exact absurd (h .forP) (by decide)

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

/-- A polarity item is negative or positive. -/
inductive Polarity | npi | ppi
  deriving DecidableEq

/-- The polarity items that probe the distinction: English *either* and *too*, German *brauchen*. -/
inductive PolarityItem | either | too | brauchen
  deriving DecidableEq

def PolarityItem.polarity : PolarityItem → Polarity
  | .either | .brauchen => .npi
  | .too => .ppi

/-- A negative polarity item must sit under the negation, so it forces the inner construal; a
positive polarity item must escape it, so it forces the outer one. -/
def Polarity.scope : Polarity → Scope
  | .npi => .inner
  | .ppi => .outer

/-- A polar question as its two probes: a negative determiner and, optionally, a polarity item. -/
structure Question where
  determiner : Determiner
  item : Option PolarityItem

/-- The probes agree on where the negation sits. -/
def Question.WellFormed (q : Question) : Prop :=
  ∀ pi ∈ q.item, pi.polarity.scope = q.determiner.scope

instance : ∀ q : Question, Decidable q.WellFormed
  | ⟨_, none⟩ => isTrue (by simp [Question.WellFormed])
  | ⟨d, some pi⟩ =>
    decidable_of_iff (pi.polarity.scope = d.scope) (by simp [Question.WellFormed])

/-- The question type a well-formed question realizes: inner negation is an inner-negation NPQ,
outer negation an outer-negation one. -/
def Scope.form : Scope → PQForm
  | .inner => .LoNQ
  | .outer => .HiNQ

/-- *Is there no vegetarian restaurant either/\*too?*: the inner-negation determiner takes the
negative polarity item and refuses the positive one. -/
theorem no_takes_either_not_too :
    (Question.mk .no (some .either)).WellFormed ∧ ¬ (Question.mk .no (some .too)).WellFormed := by
  decide

/-- *Isn't there some vegetarian restaurant \*either/too?*: the outer-negation determiner takes the
positive polarity item and refuses the negative one. -/
theorem notSome_takes_too_not_either :
    (Question.mk .notSome (some .too)).WellFormed ∧
      ¬ (Question.mk .notSome (some .either)).WellFormed := by decide

/-- *Brauchst du keine/\*nicht eine Entschuldigung mitzubringen?*: the German NPI likewise goes with
the amalgamated determiner only. -/
theorem brauchen_takes_kein_not_nichtEin :
    (Question.mk .kein (some .brauchen)).WellFormed ∧
      ¬ (Question.mk .nichtEin (some .brauchen)).WellFormed := by decide

/-- In a well-formed question the polarity item classifies the question exactly as the determiner
does, so either probe alone settles the reading. -/
theorem wellFormed_iff_determiner_form (d : Determiner) (pi : PolarityItem) :
    (Question.mk d (some pi)).WellFormed ↔ pi.polarity.scope.form = d.scope.form := by
  cases d <;> cases pi <;> decide

/-- The two probes and the evidence conditions are independent diagnostics of the same
distinction: the reading a well-formed question's determiner fixes is felicitous exactly where the
corresponding evidence condition holds. -/
theorem probed_felicity (q : Question) (ev : ContextualEvidence) :
    Felicitous q.determiner.scope.form ev ↔ evidenceBiasOK q.determiner.scope.form ev = true :=
  felicitous_iff_evidenceBiasOK _ _

end BuringGunlogson2000
