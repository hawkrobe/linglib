import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Semantics.Conditionals.Basic
import Linglib.Pragmatics.NeoGricean.Basic
import Linglib.Studies.VonFintel2001
import Linglib.Studies.BaleEtAl2025

/-!
# Evcen, Bale & Barner (2026): QUD, knowledge, and conditional perfection

[evcen-bale-barner-2026] test [von-fintel-2001]'s answer-level exhaustivity
account of conditional perfection in a three-button paradigm: Mary presses
buttons that each play a sound only she can hear, answers a question with a
conditional ("If you press the blue button, it will play a dog barking"), and
participants judge whether a *different* button plays the sound ("No" =
perfected). Perfection rates (estimated marginal means of "No" responses from
logistic mixed-effects regressions):

* **QUD** (Exp 1, N = 98, between-subjects): antecedent-focused questions
  ("Which of these buttons will play a dog sound?") yield far more perfection
  (M = 0.65) than consequent-focused (M = 0.22) or neutral (M = 0.29) ones,
  which do not differ (p > .05).
* **Answer form** (Exp 2, N = 55, within-subjects): optimally (M = 0.92) and
  overly (M = 0.84) informative answers perfect at comparable rates
  (p = .16) — overly informative answers still count as QUD answers.
* **Speaker knowledge** (Exp 3, N = 72, within-subjects): a speaker who
  tested all buttons (M = 0.72) licenses far more perfection than one who
  tested only two (M = 0.21).

The paper's ALT constraint — alternatives are QUD answers the speaker is
competent about, `ALT(p) ⊆ ANS(QUD) ∩ {q : Kₛ(q) ∨ Kₛ(¬q)}` — is
`exhaustificationLicensed`; the competence half is
`BaleEtAl2025.toBeliefState`, the same mapping [bale-etal-2025]'s
scalar-implicature paradigm uses, so conditional perfection and scalar
implicature share the competence gate by construction. Perfection is not a semantic entailment
(`Semantics.Conditionals.perfection_not_entailed_variablyStrict`), and
coverage without exclusion does not suffice
(`VonFintel2001.coverage_without_exclusion_insufficient`).

## Main results

* `perfection_of_exhaustifiedAnswer`: in the three-button scenario,
  exhaustifying Mary's answer yields `conditionalPerfection`.
* `exhaustificationLicensed_iff`: exhaustification is licensed exactly under
  an antecedent-focused QUD with a fully knowledgeable speaker.
* `exp1_licensing` / `exp3_licensing`: the licensed condition shows the
  highest observed perfection rate in each experiment.
* `horn_not_entails_vonFintel`: [horn-2000]'s existential exclusion is
  strictly weaker than per-trigger exclusion — the paradigm's per-button
  "No" responses require the latter.
-/

namespace EvcenBaleBarner2026

open VonFintel2001 Semantics.Conditionals Exhaustification NeoGricean
open BaleEtAl2025 (SpeakerKnowledge toBeliefState)

/-! ### Experimental conditions and observed rates -/

/-- QUD manipulation (Experiment 1): the question Mary's conditional
answers. -/
inductive QUDType where
  /-- "Which of these buttons will play a dog sound?" -/
  | antecedentFocused
  /-- "What will happen if I press the blue button?" -/
  | consequentFocused
  /-- "What will happen if I press the buttons?" -/
  | neutral
  deriving DecidableEq

/-- Answer-form manipulation (Experiment 2): whether Mary's conditional
names a QUD cell or a strict subset of one. -/
inductive AnswerType where
  /-- "If you press the triangles, it will play a dog barking." -/
  | optimallyInformative
  /-- "If you press the blue square, it will play a dog barking." -/
  | overlyInformative
  deriving DecidableEq

/-- Experiment 1 perfection rate by QUD type (N = 98). Follow-ups with
"what buttons" (M = 0.86, n = 32) and "which buttons" (M = 0.77, n = 32)
phrasings replicate the antecedent-focused effect, ruling out a uniqueness
presupposition from "which of these". -/
def exp1Rate : QUDType → ℚ
  | .antecedentFocused => 65 / 100
  | .consequentFocused => 22 / 100
  | .neutral => 29 / 100

/-- Experiment 2 perfection rate by answer form (N = 55; QUD always
antecedent-focused). The two rates do not differ reliably (p = .16). -/
def exp2Rate : AnswerType → ℚ
  | .optimallyInformative => 92 / 100
  | .overlyInformative => 84 / 100

/-- Experiment 3 perfection rate by speaker knowledge (N = 72; QUD always
antecedent-focused): Mary tested all three buttons or only two. -/
def exp3Rate : SpeakerKnowledge → ℚ
  | .fullKnowledge => 72 / 100
  | .partialKnowledge => 21 / 100

/-! ### When exhaustification is licensed -/

/-- A QUD makes alternative antecedents salient iff it is
antecedent-focused. -/
def qudProvidesAlternatives (q : QUDType) : Prop := q = .antecedentFocused

/-- Exhaustification is licensed when the QUD provides alternative
antecedents and the speaker is competent about them — the paper's ALT
constraint `ALT(p) ⊆ ANS(QUD) ∩ {q : Kₛ(q) ∨ Kₛ(¬q)}`. Competence is
`BaleEtAl2025.toBeliefState`'s mapping into `NeoGricean.BeliefState.Competent`. -/
def exhaustificationLicensed (k : SpeakerKnowledge) (q : QUDType) : Prop :=
  qudProvidesAlternatives q ∧ (toBeliefState k).Competent

/-- Exhaustification is licensed exactly under an antecedent-focused QUD
with a fully knowledgeable speaker. -/
@[simp] theorem exhaustificationLicensed_iff
    {k : SpeakerKnowledge} {q : QUDType} :
    exhaustificationLicensed k q ↔
      q = .antecedentFocused ∧ k = .fullKnowledge := by
  cases k <;>
    simp [exhaustificationLicensed, qudProvidesAlternatives, toBeliefState,
      BeliefState.Competent]

/-! ### Licensing predicts the observed rates -/

/-- Experiment 1 (fully knowledgeable speaker): every unlicensed QUD
condition shows less perfection than the licensed one. -/
theorem exp1_licensing (q : QUDType)
    (h : ¬exhaustificationLicensed .fullKnowledge q) :
    exp1Rate q < exp1Rate .antecedentFocused := by
  cases q with
  | antecedentFocused => exact absurd (by simp) h
  | consequentFocused => norm_num [exp1Rate]
  | neutral => norm_num [exp1Rate]

/-- Experiment 3 (antecedent-focused QUD): the unlicensed knowledge
condition shows less perfection than the licensed one. -/
theorem exp3_licensing (k : SpeakerKnowledge)
    (h : ¬exhaustificationLicensed k .antecedentFocused) :
    exp3Rate k < exp3Rate .fullKnowledge := by
  cases k with
  | fullKnowledge => exact absurd (by simp) h
  | partialKnowledge => norm_num [exp3Rate]

/-- Experiment 2: both answer forms occur under licensed conditions, and
both perfect above chance. -/
theorem exp2_above_chance (a : AnswerType) : 1 / 2 < exp2Rate a := by
  cases a <;> norm_num [exp2Rate]

/-! ### The three-button scenario -/

/-- The three buttons of the experimental paradigm. -/
inductive Button where
  | A | B | C
  deriving DecidableEq

/-- Worlds of the paradigm: one button is pressed, and the target sound
plays or stays silent. -/
inductive ButtonWorld where
  | pressA_plays | pressA_silent
  | pressB_plays | pressB_silent
  | pressC_plays | pressC_silent
  deriving DecidableEq

/-- Button A is pressed. -/
def pressA : Set ButtonWorld := {.pressA_plays, .pressA_silent}

/-- The target sound plays. -/
def soundPlays : Set ButtonWorld := {.pressA_plays, .pressB_plays, .pressC_plays}

/-- Button `b` causes the target sound: `b` is pressed and the sound plays. -/
def causes : Button → Set ButtonWorld
  | .A => {.pressA_plays}
  | .B => {.pressB_plays}
  | .C => {.pressC_plays}

/-- All three buttons are salient triggers. -/
def buttons : Set Button := {.A, .B, .C}

variable {w : ButtonWorld} {b : Button}

/-- Button A causes the sound only if button A is pressed. -/
theorem causes_A_subset_pressA : causes .A ⊆ pressA := by
  rintro w rfl; exact Set.mem_insert _ _

/-- Coverage: every world where the sound plays has a button causing it. -/
theorem coverage (hw : w ∈ soundPlays) : ∃ b ∈ buttons, w ∈ causes b := by
  rcases hw with rfl | rfl | rfl
  · exact ⟨.A, by simp [buttons], rfl⟩
  · exact ⟨.B, by simp [buttons], rfl⟩
  · exact ⟨.C, by simp [buttons], rfl⟩

/-- Every alternative button's answer is innocently excludable: at
`pressA_plays`, A's answer holds while both alternatives fail. -/
theorem alt_isInnocentlyExcludable (hb : b ∈ buttons) (hne : b ≠ .A) :
    IsInnocentlyExcludable (answerAlternatives causes buttons .A)
      (causes .A) (causes b) := by
  refine .of_full_exclusion_consistent
    (mem_answerAlternatives.mpr ⟨b, hb, hne, rfl⟩) ⟨.pressA_plays, rfl, ?_⟩
  intro q hq
  obtain ⟨b', -, hne', rfl⟩ := mem_answerAlternatives.mp hq
  cases b' with
  | A => exact absurd rfl hne'
  | B => exact nofun
  | C => exact nofun

/-- Theory chain: exhaustifying Mary's answer "button A plays the sound"
yields conditional perfection — if A is not pressed, the sound does not
play. -/
theorem perfection_of_exhaustifiedAnswer
    (h_exh : w ∈ exhaustifiedAnswer causes buttons .A) :
    w ∈ conditionalPerfection pressA soundPlays :=
  exhaustification_yields_perfection causes_A_subset_pressA
    (fun _ hb hne => alt_isInnocentlyExcludable hb hne) coverage h_exh

/-- The participant's inference: granting exclusion of the other buttons,
a world where A is unpressed is a world without the sound. -/
theorem perfection_of_exclusion (hB : w ∉ causes .B) (hC : w ∉ causes .C) :
    w ∈ conditionalPerfection pressA soundPlays :=
  perfection_from_exclusion_and_coverage (fun h => causes_A_subset_pressA h)
    (fun b _ hne => by
      cases b with
      | A => exact absurd rfl hne
      | B => exact hB
      | C => exact hC)
    coverage

/-! ### Per-trigger vs existential exclusion -/

section HornComparison

variable {ι W : Type*}

/-- [von-fintel-2001]-style prediction: every alternative salient trigger
is excluded. -/
def vonFintelPrediction (causes : ι → Set W) (triggers : Set ι) (t : ι)
    (w : W) : Prop :=
  ∀ t' ∈ triggers, t' ≠ t → w ∉ causes t'

/-- [horn-2000]-style prediction: some alternative salient trigger is
excluded, with no commitment to which. -/
def hornPrediction (causes : ι → Set W) (triggers : Set ι) (t : ι)
    (w : W) : Prop :=
  ∃ t' ∈ triggers, t' ≠ t ∧ w ∉ causes t'

/-- Per-trigger exclusion implies existential exclusion. -/
theorem vonFintel_entails_horn {causes : ι → Set W} {triggers : Set ι}
    {t : ι} {w : W} (h_other : ∃ t' ∈ triggers, t' ≠ t)
    (h_vf : vonFintelPrediction causes triggers t w) :
    hornPrediction causes triggers t w :=
  let ⟨t', ht', hne⟩ := h_other
  ⟨t', ht', hne, h_vf t' ht' hne⟩

end HornComparison

/-- At `pressB_plays`, Horn's existential holds (button C is excluded) but
von Fintel's universal fails (button B does cause the sound): per-trigger
exclusion is strictly stronger, and participants' "No" responses to
*specific* other buttons require it. -/
theorem horn_not_entails_vonFintel :
    ∃ w, hornPrediction causes buttons .A w ∧
      ¬vonFintelPrediction causes buttons .A w := by
  refine ⟨.pressB_plays, ⟨.C, by simp [buttons], nofun, by simp [causes]⟩,
    fun h => ?_⟩
  exact h .B (by simp [buttons]) nofun rfl

end EvcenBaleBarner2026
