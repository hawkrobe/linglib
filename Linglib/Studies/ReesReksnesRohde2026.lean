import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring

/-!
# Rees, Reksnes, and Rohde (2026): Why are you telling me this? The availability and timing of relevance inferences

This file formalizes the reasoning the paper attributes to the addressee of a trivial
utterance such as *the library walls are blue*, and the logic of its timing experiments.
Speaking rather than staying silent presumes that what is conveyed is worth the speaker's
while, so an utterance whose content alone falls short of the speaker's bar leaves a
`deficit` that the addressee makes up by inferring additional meaning: a relevance inference.
Which reading makes up the deficit depends on the speaker, `Reconciles`. The inference that
the situation used to be different is warranted only by a speaker who knows the situation over
time, which licenses it for Suzy's school and not for the Prime Minister's office, the Speaker
Knowledge effect of all four experiments. A quiet speaker's bar is higher, so the same
utterance leaves a larger deficit, `deficit_le_deficit`, the Speaker Style effect of
Experiment 2; for an unfamiliar location the addressee then looks for additional meaning other
than a change, which is what the paper offers for the interaction it found there. An emphasis
cue changes neither the bar nor the content, and so nothing, the null effect of Experiment 1.

Experiments 3 and 4 ask whether the inference is costly with a verification question whose
polarity endorses the inference in one experiment and rejects it in the other. Under an
additive model of response times, `ResponseModel.rt`, the contrast within Experiment 3
confounds the cost of the inference with that of answering *no*, while the contrast between
the two experiments' *yes* answers identifies it, `yes_contrast`; the model also predicts a
contrast between the *no* answers, which the paper did not find.

## Implementation notes

Importance and the speaker's bar are exact rationals compared by order, so the model says
which readings are available, not how often they are chosen; the paper's proportions and
times belong to it and its data release. Situations are classified as the paper selected its
items: plausibly changeable for the targets, inevitably changing for the attention checks,
and constant for what it excluded.

## References

* [A. Rees, V. Reksnes, H. Rohde, *Why are you telling me this? The availability and timing
  of relevance inferences* (2026)][rees-reksnes-rohde-2026]
* [H. Rohde, J. Hoek, M. Keshev, M. Franke, *This better be interesting: a speaker's decision
  to speak cues listeners to expect informative content* (2022)][rohde-etal-2022]
* [D. Sperber, D. Wilson, *Relevance: communication and cognition* (1986)][sperber-wilson-1986]
* [H. P. Grice, *Logic and conversation* (1975)][grice-1975]
* [L. Bergen, D. J. Grodner, *Speaker knowledge influences the comprehension of pragmatic
  inferences* (2012)][bergen-grodner-2012]
* [E. Kravtchenko, V. Demberg, *Informationally redundant utterances elicit pragmatic
  inferences* (2022)][kravtchenko-demberg-2022]
* [L. Bott, I. A. Noveck, *Some utterances are underinformative: the onset and time course of
  scalar inferences* (2004)][bott-noveck-2004]
-/

namespace ReesReksnesRohde2026

/-! ### The availability of relevance inferences -/

/-- The addressee's model of the speaker: whether they know the situation over time, and how
important a contribution must be for them to make it, a quiet speaker's bar being the
higher. -/
structure Speaker where
  knowledgeable : Bool
  bar : ℚ

/-- How a described situation varies over time: constant, like the white lines of a zebra
crossing; plausibly changeable, like the colour of walls; or inevitably changing, like the
leaves of a tree in autumn. -/
inductive Mutability where
  | constant
  | changeable
  | inevitable
  deriving DecidableEq

/-- An utterance about a situation: the importance of its content on its own, and how the
situation varies over time. -/
structure Utterance where
  importance : ℚ
  mutability : Mutability

/-- The importance the decision to speak presumes beyond what the content itself provides. -/
def deficit (s : Speaker) (u : Utterance) : ℚ := s.bar - u.importance

/-- An utterance is trivial for a speaker when its content alone does not meet their bar. -/
def Trivial (s : Speaker) (u : Utterance) : Prop := 0 < deficit s u

instance (s : Speaker) (u : Utterance) : Decidable (Trivial s u) :=
  inferInstanceAs (Decidable (_ < _))

/-- The readings of a trivial utterance the paper distinguishes. -/
inductive Reading where
  /-- The content at face value: the walls are blue. -/
  | literal
  /-- The situation has changed: the walls used to be a different colour. -/
  | changed
  /-- Some other additional meaning, such as that the speaker finds the situation unusual. -/
  | other
  /-- Small talk, conveying nothing further. -/
  | phatic
  deriving DecidableEq

/-- Whether a reading reconciles the speaker's decision to speak with what they said. The
face-value reading does when the content meets the bar. The inference of a change does for a
situation that inevitably changes, for a changeable one when the content falls short and the
speaker knows the situation over time, and never for a constant one. Some other additional
meaning does whenever the content falls short, and small talk always. -/
def Reconciles (s : Speaker) (u : Utterance) : Reading → Prop
  | .literal => ¬ Trivial s u
  | .changed =>
    u.mutability ≠ .constant ∧ (u.mutability = .changeable → Trivial s u ∧ s.knowledgeable = true)
  | .other => Trivial s u
  | .phatic => True

instance (s : Speaker) (u : Utterance) : DecidablePred (Reconciles s u) := λ r => by
  cases r <;> unfold Reconciles <;> infer_instance

variable {s t : Speaker} {u : Utterance}

/-- Whatever a speaker leaves for the addressee to infer, a quieter speaker leaves more. -/
theorem deficit_le_deficit (h : s.bar ≤ t.bar) : deficit s u ≤ deficit t u :=
  sub_le_sub_right h _

/-- An utterance trivial for a speaker is trivial for a quieter one. -/
theorem Trivial.mono (h : Trivial s u) (hb : s.bar ≤ t.bar) : Trivial t u :=
  lt_of_lt_of_le h (deficit_le_deficit hb)

/-- For a changeable situation, the inference of a change is licensed exactly when the
content falls short of the bar and the speaker knows the situation over time. -/
theorem reconciles_changed_iff (hu : u.mutability = .changeable) :
    Reconciles s u .changed ↔ Trivial s u ∧ s.knowledgeable = true := by
  simp [Reconciles, hu]

/-- A speaker who does not know the situation over time never licenses the inference of a
change to a changeable situation: the Prime Minister's office. -/
theorem not_reconciles_changed (h : s.knowledgeable = false) (hu : u.mutability = .changeable) :
    ¬ Reconciles s u .changed := by
  simp [Reconciles, hu, h]

/-- The inference of a change is one way of making up the deficit; when it is unavailable, as
for a quiet speaker at an unfamiliar location, the addressee still looks for some additional
meaning. -/
theorem reconciles_other_of_changed (hu : u.mutability = .changeable)
    (h : Reconciles s u .changed) : Reconciles s u .other :=
  ((reconciles_changed_iff hu).1 h).1

/-- The addressee either takes the content at face value or looks for additional meaning. -/
theorem reconciles_literal_iff : Reconciles s u .literal ↔ ¬ Reconciles s u .other := Iff.rfl

/-- An inevitably changing situation was different before whoever speaks: the attention
checks. -/
theorem reconciles_changed_of_inevitable (hu : u.mutability = .inevitable) :
    Reconciles s u .changed := by
  simp [Reconciles, hu]

/-! ### The timing of relevance inferences -/

/-- The two verification experiments, which differ in the polarity of the question: *was it
the same?*, so that *no* endorses the inference, and *was it different?*, so that *yes*
does. -/
inductive Experiment where
  | same
  | different
  deriving DecidableEq

/-- Whether an answer endorses the inference. -/
def Experiment.endorses : Experiment → Bool → Bool
  | .same, yes => !yes
  | .different, yes => yes

/-- An additive model of the time to answer a verification question: a cost of the answer's
polarity, negative answers being the slower, and a cost of endorsing the inference. -/
structure ResponseModel where
  polarity : Bool → ℚ
  inference : ℚ

/-- The predicted response time. -/
def ResponseModel.rt (m : ResponseModel) (e : Experiment) (yes : Bool) : ℚ :=
  m.polarity yes + if e.endorses yes then m.inference else 0

variable (m : ResponseModel)

/-- Within Experiment 3, the contrast between the inference-endorsing *no* and the *yes*
confounds the cost of the inference with that of a negative answer. -/
theorem exp3_confounded :
    m.rt .same false - m.rt .same true = (m.polarity false - m.polarity true) + m.inference := by
  simp [ResponseModel.rt, Experiment.endorses]; ring

/-- Across the experiments, the contrast between the *yes* answers isolates the cost of the
inference. -/
theorem yes_contrast : m.rt .different true - m.rt .same true = m.inference := by
  simp [ResponseModel.rt, Experiment.endorses]

/-- The model likewise predicts that Experiment 3's *no* answers exceed Experiment 4's by the
cost of the inference, a difference the paper did not find. -/
theorem no_contrast : m.rt .same false - m.rt .different false = m.inference := by
  simp [ResponseModel.rt, Experiment.endorses]

end ReesReksnesRohde2026
