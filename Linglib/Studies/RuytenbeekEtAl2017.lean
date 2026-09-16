import Linglib.Discourse.SpeechAct
import Linglib.Semantics.Mood.SpeechEvent
import Linglib.Fragments.Romance.French.Modals
import Linglib.Data.Examples.RuytenbeekEtAl2017

/-!
# Ruytenbeek et al. (2017): Indirect request processing, sentence types and illocutionary forces

This file formalizes the paper's test of speech-act literalism, on which a sentence type
encodes an illocutionary force, so that a directive reading of a non-imperative sentence is
secondary, mediated by the encoded force, unless the construction is a conventionalised
indirect request. Non-literalism instead makes a directive reading primary whenever the
sentence shares the semantic features that make imperatives suited to directives: the deontic
necessity of [kaufmann-2012]'s imperative, the questioning of the addressee's ability that is
[clark-1979]'s convention of means, or the enablement the possibility modals encode. The
two accounts are predicates on the constructions of the paper's two French experiments
(`Literalist.DirectivePrimary`, `NonLiteralist.DirectivePrimary`), with conventionalisation
read off the paper's corpus counts and the modal semantics off the French fragment. In both
experiments directive interpretations came with no fixations on the answer buttons and with
response times matching the imperative, and they came for exactly the constructions
non-literalism predicts (`nonLiteralist_predicts`); the non-conventionalised *Est-il possible
de VP?* and the deontic *Vous devez VP* received them although literalism makes those
readings secondary (`literalist_refuted`).

## Implementation notes

The rows of `Data/Examples/RuytenbeekEtAl2017.json` are the paper's stimulus sentences with
the observed response pattern of each construction, the model estimates of response times the
paper reports, and the corpus counts for the two interrogative requests. A construction is
directive when it received directive interpretations at all, and unactivated when the paper
reports no fixations on the answer buttons and response times equal to the imperative's for
those interpretations; the regression coefficients and confidence intervals stay in the data.
The paper's ranking of directive rates, *Vous devez* above *Vous pouvez* above *Il est
possible*, which it attributes to the permission reading of *pouvoir*, is not derived.

## References

* [ruytenbeek-etal-2017]
* [kaufmann-2012]
* [clark-1979]
* [sadock-zwicky-1985]
* [talmy-2000]
-/

namespace RuytenbeekEtAl2017

open Data.Examples French
open Modality (ModalFlavor ModalForce)
open Mood (Illocutionary)
open Mood.Illocutionary (primaryFlavor)

/-! ### Constructions and forces -/

/-- The constructions of the two experiments. -/
inductive Construction where
  | imperative
  | controlInterrogative
  | canYou
  | isItPossible
  | youMust
  | youCan
  | itIsPossible
  | controlDeclarative
  deriving DecidableEq, Repr, Fintype

/-- The morphosyntactic mood of a construction. -/
def Construction.mood : Construction → Illocutionary
  | .imperative => .imperative
  | .controlInterrogative | .canYou | .isItPossible => .interrogative
  | .youMust | .youCan | .itIsPossible | .controlDeclarative => .declarative

/-- The modal of a construction, from the French fragment. -/
def Construction.modal : Construction → Option FrenchModalEntry
  | .canYou | .youCan => some pouvoir
  | .isItPossible | .itIsPossible => some ilEstPossible
  | .youMust => some devoir
  | _ => none

/-- The force of a construction's modal. -/
def Construction.modalForce (c : Construction) : Option ModalForce := c.modal.map (·.force)

/-- The flavors of a construction's modal. -/
def Construction.modalFlavors (c : Construction) : List ModalFlavor :=
  (c.modal.map (·.flavors)).getD []

/-- The preparatory condition a construction questions: the two interrogative requests ask
about the addressee's ability. -/
def Construction.queriedPrep : Construction → Option PreparatoryCondition
  | .canYou | .isItPossible => some .ability
  | _ => none

/-- The construction's key in the rows. -/
def Construction.tag : Construction → String
  | .imperative => "imperative"
  | .controlInterrogative => "controlInterrogative"
  | .canYou => "canYou"
  | .isItPossible => "isItPossible"
  | .youMust => "youMust"
  | .youCan => "youCan"
  | .itIsPossible => "itIsPossible"
  | .controlDeclarative => "controlDeclarative"

/-- The major illocutionary forces. -/
inductive Force where
  | directive
  | question
  | assertion
  deriving DecidableEq, Repr

/-- Literalism: the force a sentence type encodes. -/
def encodedForce : Illocutionary → Option Force
  | .imperative => some .directive
  | .interrogative => some .question
  | .declarative => some .assertion
  | _ => none

/-! ### The corpus and conventionalisation -/

/-- The paper's corpus coding of a construction's uses, as a percentage. -/
def corpusPct (c : Construction) (use : String) : ℕ :=
  ((Examples.all.filter λ x => x.feature? "construction" = some c.tag ∧
      (x.feature? "corpusN").isSome).filterMap (·.nat? use)).headD 0

/-- A construction is conventionalised as a request when its directive uses outnumber its
question uses in the corpus. -/
def Conventionalised (c : Construction) : Prop :=
  corpusPct c "questionPct" < corpusPct c "directivePct"

instance (c : Construction) : Decidable (Conventionalised c) := by
  unfold Conventionalised; infer_instance

/-- *Pouvez-vous VP?* is conventionalised as a request and *Est-il possible de VP?* is not. -/
theorem conventionalised : Conventionalised .canYou ∧ ¬ Conventionalised .isItPossible := by
  decide +kernel

/-! ### The two accounts -/

/-- Under literalism a directive reading is primary only when the sentence type encodes
directive force or the construction is a conventionalised indirect request; any other
directive reading is secondary and activates the encoded force. -/
def Literalist.DirectivePrimary (c : Construction) : Prop :=
  encodedForce c.mood = some .directive ∨ Conventionalised c

/-- Under non-literalism a directive reading is primary when the construction shares the
imperative's directive-making semantics: the imperative's own deontic necessity, the
questioning of the addressee's ability, or a possibility modal's enablement. -/
def NonLiteralist.DirectivePrimary (c : Construction) : Prop :=
  c.mood = .imperative ∨
    (c.modalForce = some .necessity ∧ primaryFlavor .imperative ∈ c.modalFlavors) ∨
    c.queriedPrep = some .ability ∨ c.modalForce = some .possibility

instance (c : Construction) : Decidable (Literalist.DirectivePrimary c) := by
  unfold Literalist.DirectivePrimary; infer_instance

instance (c : Construction) : Decidable (NonLiteralist.DirectivePrimary c) := by
  unfold NonLiteralist.DirectivePrimary; infer_instance

/-- The accounts agree on the constructions without a modal and on the conventionalised
request, and differ on every other modal construction. -/
theorem accounts_differ (c : Construction) :
    (Literalist.DirectivePrimary c ↔ NonLiteralist.DirectivePrimary c) ↔
      c.modalForce = none ∨ Conventionalised c := by
  cases c <;> decide +kernel

/-! ### The observations -/

/-- How often a construction received directive interpretations. -/
inductive Directiveness where
  | only
  | dominant
  | minority
  | none
  deriving DecidableEq, Repr

private def constructions : List (String × Construction) :=
  [.imperative, .controlInterrogative, .canYou, .isItPossible, .youMust, .youCan, .itIsPossible,
    .controlDeclarative].map λ c => (c.tag, c)

/-- A stimulus row: its construction and how often it was interpreted as a directive. -/
def datum (x : LinguisticExample) : Option (Construction × Directiveness) := do
  pure (← x.parse? "construction" constructions,
    ← x.parse? "directive"
      [("only", .only), ("dominant", .dominant), ("minority", .minority), ("none", .none)])

/-- The stimulus rows of the two experiments. -/
def stimuli : List (LinguisticExample × Construction × Directiveness) :=
  Examples.all.filterMap λ x => (datum x).map (x, ·)

/-- The construction received directive interpretations. -/
def Directive (p : LinguisticExample × Construction × Directiveness) : Prop := p.2.2 ≠ .none

instance (p : LinguisticExample × Construction × Directiveness) : Decidable (Directive p) := by
  unfold Directive; infer_instance

/-- The directive interpretations came without activation of the encoded force: no fixations
on the answer buttons and response times equal to the imperative's. -/
def Unactivated (p : LinguisticExample × Construction × Directiveness) : Prop :=
  p.1.feature? "activation" = some "none"

instance (p : LinguisticExample × Construction × Directiveness) : Decidable (Unactivated p) := by
  unfold Unactivated; infer_instance

/-- Every construction that received directive interpretations received them without
activating the force its sentence type encodes. -/
theorem directive_unactivated : ∀ p ∈ stimuli, Directive p → Unactivated p := by
  decide +kernel

/-- Non-literalism predicts primary directive readings for exactly the constructions that
received directive interpretations. -/
theorem nonLiteralist_predicts :
    ∀ p ∈ stimuli, Directive p ↔ NonLiteralist.DirectivePrimary p.2.1 := by
  decide +kernel

/-- Literalism is refuted on both of the paper's predictions: the non-conventionalised
*Est-il possible de VP?* and the deontic *Vous devez VP*, like the two possibility
declaratives, received directive interpretations without activating the question or the
assertion, although literalism makes those readings secondary. -/
theorem literalist_refuted :
    ∀ p ∈ stimuli, ¬ Literalist.DirectivePrimary p.2.1 → Directive p → Unactivated p := by
  decide +kernel

/-- The secondary readings literalism posits are the ones the experiments found primary. -/
theorem literalist_secondary_found :
    ∀ c, c = .isItPossible ∨ c = .youMust ∨ c = .youCan ∨ c = .itIsPossible →
      ¬ Literalist.DirectivePrimary c ∧ ∃ p ∈ stimuli, p.2.1 = c ∧ Directive p := by
  decide +kernel

/-- The reported response time of a construction's answer responses, in milliseconds. -/
def rtAnswer (c : Construction) : ℕ :=
  ((Examples.all.filter λ x => x.feature? "construction" = some c.tag ∧
      x.feature? "study" = some "1").filterMap (·.nat? "rtAnswer")).headD 0

/-- Answering the conventionalised request as a question is slower than answering a control
question, which the paper reads as interference from its entrenched directive use. -/
theorem canYou_question_slower : rtAnswer .controlInterrogative < rtAnswer .canYou := by
  decide +kernel

end RuytenbeekEtAl2017
