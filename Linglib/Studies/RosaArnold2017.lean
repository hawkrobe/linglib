import Linglib.Data.Examples.RosaArnold2017
import Linglib.Fragments.English.Pronouns
import Linglib.Morphology.Word.Agree
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith

/-!
# Rosa and Arnold (2017): Predictability affects production

This file formalizes [rosa-arnold-2017]'s test of whether the predictability of a referent
affects the speaker's choice of a pronoun. Transfer verbs separate thematic role from
grammatical role, since *get* and *take* put the goal in subject position while *give* and
*hand* put it in a nonsubject position, so the design crosses the role of the continued
character with its grammatical role and with the gender contrast of the character pair, and a
rating study finds the goal expected as the next mention well above the source while subjects
are not expected above nonsubjects. The expectancy hypothesis of [arnold-2001] predicts more
pronouns for goals; the topicality account of [kehler-rohde-2013] and
[fukumura-van-gompel-2010] predicts that thematic role leaves the production probability
untouched once grammatical role is fixed. The production probability is a logistic model over
the design, the paper's regression with its two main effects: `topical_iff` states the
topicality account as the vanishing of the thematic effect, and `source_subject_gt_goal_iff`
shows that a subject source pronominalized above a nonsubject goal, the earlier finding taken as
evidence against predictability, is consistent with a positive thematic effect whenever the
subject effect exceeds it. The rows carry the pronoun rates of the three experiments and the
rating study; `topical_not_fits` reads the Experiment 1 contrast at fixed grammatical role and
`goal_expected` the rating study. The effect sizes, the marginal amplification of the goal
effect under Occasion and Result continuations in Experiment 2, and the shorter latencies for
goal continuations stay in prose.

## Implementation notes

* A model fits a table of rates when its log-odds order the cells as the rates do, which the
  logistic link guarantees for population rates.
* The gender contrast of an item is derived from the characters' φ-features: a pronoun is
  ambiguous exactly when the two characters agree.

## References

* [rosa-arnold-2017]
* [arnold-2001]
* [kehler-rohde-2013]
* [fukumura-van-gompel-2010]
-/

namespace RosaArnold2017

open Data.Examples Morphology

/-! ### The design -/

/-- The thematic role of the continued character in the transfer event. -/
inductive Role where
  | goal
  | source
  deriving DecidableEq, Repr, Fintype

/-- The grammatical role of the continued character in the prompt sentence. -/
inductive Gram where
  | subject
  | nonsubject
  deriving DecidableEq, Repr, Fintype

/-- Whether the two characters share a gender, so that a pronoun is ambiguous between them. -/
inductive Gender where
  | same
  | different
  deriving DecidableEq, Repr, Fintype

/-- A cell of the design. -/
structure Cell where
  role : Role
  gram : Gram
  gender : Gender
  deriving DecidableEq, Repr, Fintype

/-- The gender contrast of a pair of characters: `same` exactly when their φ-features agree,
the pairs a third-person singular pronoun cannot tell apart. -/
def Gender.ofPair (w₁ w₂ : Word) : Gender := if w₁.Agree w₂ then .same else .different

/-- Lisa, of *Lisa gave the leftover pie to Brendan*. -/
def lisa : Word :=
  ⟨"Lisa", .PROPN, { person := some .third, number := some .Sing, gender := some .Fem }⟩

/-- Brendan. -/
def brendan : Word :=
  ⟨"Brendan", .PROPN, { person := some .third, number := some .Sing, gender := some .Masc }⟩

/-- The running example is a different-gender item: *she* has Lisa as its only candidate
antecedent. -/
theorem lisa_brendan :
    Gender.ofPair lisa brendan = .different ∧
      Proform.CandidateAntecedent English.Pronouns.she lisa ∧
      ¬ Proform.CandidateAntecedent English.Pronouns.she brendan := by
  decide

/-! ### The production model

The regressions predict the log-odds of a pronoun from subjecthood and thematic role. -/

/-- A logistic production model over the design: the log-odds of a pronoun as a baseline plus
a subject effect and a goal effect. -/
structure Model where
  base : ℚ
  subject : ℚ
  goal : ℚ

/-- The log-odds of a pronoun in a cell. -/
def Model.logit (M : Model) (c : Cell) : ℚ :=
  M.base + (if c.gram = .subject then M.subject else 0) + (if c.role = .goal then M.goal else 0)

/-- The topicality account: production is insensitive to thematic role. -/
def Model.Topical (M : Model) : Prop := M.goal = 0

/-- The topicality account is the claim that goals and sources are pronominalized alike at
every grammatical role and gender. -/
theorem topical_iff (M : Model) :
    M.Topical ↔ ∀ g d, M.logit ⟨.goal, g, d⟩ = M.logit ⟨.source, g, d⟩ := by
  unfold Model.Topical
  constructor
  · intro h g d; simp [Model.logit, h]
  · intro h; simpa [Model.logit] using h .nonsubject .same

/-- A subject source pronominalized above a nonsubject goal, the earlier finding read as
evidence that production ignores predictability, holds exactly when the subject effect exceeds
the goal effect, so it leaves a positive goal effect untested. -/
theorem source_subject_gt_goal_iff (M : Model) (d : Gender) :
    M.logit ⟨.goal, .nonsubject, d⟩ < M.logit ⟨.source, .subject, d⟩ ↔ M.goal < M.subject := by
  simp [Model.logit]

/-- A model fits a table of rates when its log-odds order the cells as the rates do. -/
def Model.Fits (M : Model) (r : Cell → ℕ) : Prop :=
  ∀ c c', M.logit c < M.logit c' ↔ r c < r c'

/-! ### The findings -/

/-- The first percentage the rows matching the features record under `key`. -/
def pct (fs : List (String × String)) (key : String) : ℕ :=
  ((Examples.all.filter λ e => fs.all λ kv => e.feature? kv.1 = some kv.2).filterMap
    (·.nat? key)).headD 0

/-- The three experiments: in-person event retelling, sentence completion over the story
materials, and sentence completion with disconnected items. -/
inductive Experiment where
  | retelling
  | completion
  | renamed
  deriving DecidableEq, Repr

def Experiment.tag : Experiment → String
  | .retelling => "retelling"
  | .completion => "completion"
  | .renamed => "renamed"

def Role.tag : Role → String
  | .goal => "goal"
  | .source => "source"

def Gram.tag : Gram → String
  | .subject => "subject"
  | .nonsubject => "nonsubject"

def Gender.tag : Gender → String
  | .same => "same"
  | .different => "different"

/-- The rate of pronoun production in a cell of an experiment (Tables 1, 4, 7), in percent. -/
def rate (e : Experiment) (c : Cell) : ℕ :=
  pct [("experiment", e.tag), ("role", c.role.tag), ("gram", c.gram.tag),
    ("gender", c.gender.tag)] "pronouns"

/-- The rating study: the percentage of raters choosing the character named by `key`, the goal
or the subject, as the one more likely to be talked about next. -/
def nextMention (key : String) : ℕ := pct [("study", "rating")] key

/-- Goals are expected as the next mention above sources, and above subjects. -/
theorem goal_expected : 50 < nextMention "goal" ∧ nextMention "subject" < nextMention "goal" := by
  decide +kernel

/-- Experiment 1 at fixed grammatical role refutes the topicality account: goals in subject
position are pronominalized above sources in subject position, which no model without a
thematic effect fits. -/
theorem topical_not_fits (M : Model) (hM : M.Topical) : ¬ M.Fits (rate .retelling) := by
  intro hf
  have h := (topical_iff M).1 hM .subject .different
  have hlt := (hf ⟨.source, .subject, .different⟩ ⟨.goal, .subject, .different⟩).2
    (by decide +kernel)
  rw [h] at hlt
  exact lt_irrefl _ hlt

end RosaArnold2017
