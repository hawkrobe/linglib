import Linglib.Morphology.InflectionRules
import Linglib.Fragments.English.Tense
import Linglib.Semantics.Tense.Evidential

/-!
# [lakoff-1970]: Tense and Its Relation to Participants
[lakoff-1970] [cumming-2026]

[lakoff-1970] argues that tense selection is sensitive to speaker/hearer
epistemic states, not just temporal ordering: past tense can apply to a
present-time event that has lost psychological **salience** ("The animal
you saw WAS a chipmunk" — it still is one), and embedded present survives
a past matrix when the content is **novel** to the hearer. The
`TensePerspective` frame extends [cumming-2026]'s `EvidentialFrame` with
these two participant dimensions; the paper's acceptability judgments
are collected as `TenseJudgment` data.

## Key Minimal Pairs

- §1 False tense: synthetic forms (WAS, IS) can express non-temporal tense;
  periphrastic forms (USED TO) cannot.
- §2 SOT/novelty: present tense survives under past matrix when content is
  novel to hearer ("discovered that the boy HAS blue eyes").
- §4 Perfect/salience: present perfect requires current relevance
  (*"Shakespeare has quarreled with Bacon" vs "Shakespeare has written...").
- §5 Will-deletion: scheduled events allow present-for-future
  ("The meeting starts at 3"), but unscheduled events do not
  (*"It rains Thursday").
-/

namespace Lakoff1970

open Morphology.Tense

/-- Acceptability judgment for a tense example. -/
inductive Acceptability where
  | grammatical
  | ungrammatical
  | marginal
  deriving DecidableEq, Repr

/-- Whether the tense use is "true" (temporal) or "false" (psychological). -/
inductive TenseUseType where
  | trueTense
  | falseTense
  deriving DecidableEq, Repr

/-- A grammaticality judgment from [lakoff-1970]. -/
structure TenseJudgment where
  /-- Example number in the paper (e.g., "4a", "8a") -/
  exNumber : String
  /-- The sentence (abbreviated) -/
  sentence : String
  /-- True or false tense use -/
  tenseUse : TenseUseType
  /-- Synthetic or periphrastic form -/
  formType : TenseFormType
  /-- The paper's acceptability judgment -/
  acceptability : Acceptability
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § 1. False Tense (§1)
-- ════════════════════════════════════════════════════

/-- (4a) "The animal you saw WAS a chipmunk" — false past, synthetic, OK. -/
def ex4a : TenseJudgment where
  exNumber := "4a"
  sentence := "The animal you saw was a chipmunk"
  tenseUse := .falseTense
  formType := .synthetic
  acceptability := .grammatical

/-- (6a) "The animal you saw IS a chipmunk" — true present, synthetic, OK. -/
def ex6a : TenseJudgment where
  exNumber := "6a"
  sentence := "The animal you saw is a chipmunk"
  tenseUse := .trueTense
  formType := .synthetic
  acceptability := .grammatical

/-- (8a) *"The animal you saw USED TO BE a chipmunk" — false past,
    periphrastic, ungrammatical. The periphrastic form forces true-past
    reading, which conflicts with the present-time event. -/
def ex8a : TenseJudgment where
  exNumber := "8a"
  sentence := "The animal you saw used to be a chipmunk"
  tenseUse := .falseTense
  formType := .periphrastic
  acceptability := .ungrammatical

/-- (9a) "The animal you saw USED TO BE a chipmunk" — true past,
    periphrastic, grammatical. It genuinely WAS a chipmunk before. -/
def ex9a : TenseJudgment where
  exNumber := "9a"
  sentence := "That used to be a chipmunk"
  tenseUse := .trueTense
  formType := .periphrastic
  acceptability := .grammatical

-- ════════════════════════════════════════════════════
-- § 2. SOT and Hearer Novelty (§2)
-- ════════════════════════════════════════════════════

/-- (13a) "He discovered that the boy HAD blue eyes" — SOT past-under-past, OK. -/
def ex13a : TenseJudgment where
  exNumber := "13a"
  sentence := "He discovered that the boy had blue eyes"
  tenseUse := .trueTense
  formType := .synthetic
  acceptability := .grammatical

/-- (13b) "He discovered that the boy HAS blue eyes" — novel-info present
    survives under past matrix, grammatical when content is new to hearer. -/
def ex13b : TenseJudgment where
  exNumber := "13b"
  sentence := "He discovered that the boy has blue eyes"
  tenseUse := .trueTense
  formType := .synthetic
  acceptability := .grammatical

-- ════════════════════════════════════════════════════
-- § 3. Perfect and Salience (§4)
-- ════════════════════════════════════════════════════

/-- (22a) "Shakespeare has written 37 plays" — salient (enduring relevance), OK. -/
def ex22a : TenseJudgment where
  exNumber := "22a"
  sentence := "Shakespeare has written 37 plays"
  tenseUse := .trueTense
  formType := .synthetic
  acceptability := .grammatical

/-- (22b) *"Shakespeare has quarreled with Bacon" — not salient
    (no current relevance), ungrammatical with present perfect. -/
def ex22b : TenseJudgment where
  exNumber := "22b"
  sentence := "Shakespeare has quarreled with Bacon"
  tenseUse := .trueTense
  formType := .synthetic
  acceptability := .ungrammatical

-- ════════════════════════════════════════════════════
-- § 4. Will-Deletion (§5)
-- ════════════════════════════════════════════════════

/-- (27a) "John will die" — overt future, grammatical (control). -/
def ex27a : TenseJudgment where
  exNumber := "27a"
  sentence := "John will die"
  tenseUse := .trueTense
  formType := .synthetic
  acceptability := .grammatical

/-- (27b) "John dies tomorrow" — will-deletion with scheduled/salient event, OK. -/
def ex27b : TenseJudgment where
  exNumber := "27b"
  sentence := "John dies tomorrow"
  tenseUse := .falseTense
  formType := .synthetic
  acceptability := .grammatical

/-- (25b) *"It rains Thursday" — will-deletion without salience/schedule,
    ungrammatical. Weather events are not scheduled. -/
def ex25b : TenseJudgment where
  exNumber := "25b"
  sentence := "It rains Thursday"
  tenseUse := .falseTense
  formType := .synthetic
  acceptability := .ungrammatical

-- ════════════════════════════════════════════════════
-- § 5. Collections
-- ════════════════════════════════════════════════════

/-- All judgments from the paper. -/
def allJudgments : List TenseJudgment :=
  [ex4a, ex6a, ex8a, ex9a, ex13a, ex13b, ex22a, ex22b, ex27a, ex27b, ex25b]

/-- False-tense judgments only. -/
def falseTenseJudgments : List TenseJudgment :=
  allJudgments.filter (·.tenseUse == .falseTense)

/-- Periphrastic judgments only. -/
def periphrasticJudgments : List TenseJudgment :=
  allJudgments.filter (·.formType == .periphrastic)

-- ════════════════════════════════════════════════════
-- § 6. Data Verification
-- ════════════════════════════════════════════════════

/-- There are 11 total judgments. -/
theorem total_count : allJudgments.length = 11 := rfl

/-- There are 4 false-tense judgments. -/
theorem false_tense_count : falseTenseJudgments.length = 4 := rfl

/-- There are 2 periphrastic judgments. -/
theorem periphrastic_count : periphrasticJudgments.length = 2 := rfl

/-- The only ungrammatical false-tense-with-periphrastic example is ex8a. -/
theorem false_periphrastic_ungrammatical :
    (falseTenseJudgments.filter (·.formType == .periphrastic)).length = 1 := rfl

-- ════════════════════════════════════════════════════
-- § 7. Participant-Perspective Frame
-- ════════════════════════════════════════════════════

open Tense.Evidential
open Tense

/-- Lakoff's participant-sensitive tense frame. Extends [cumming-2026]'s
    `EvidentialFrame` (which extends `ReichenbachFrame` with acquisition
    time A) with two psychological dimensions. Lakoff's observations are
    orthogonal to Cumming's evidential constraint: "false past" arises
    even when evidence is downstream (the chipmunk is still there, so
    T ≤ A holds) because the event has lost psychological salience. -/
structure TensePerspective (Time : Type*) extends EvidentialFrame Time where
  /-- Is the event psychologically salient to the speaker at S? -/
  speakerSalience : Bool
  /-- Is the propositional content new to the hearer? -/
  hearerNovelty : Bool

variable {Time : Type*}

/-- **False tense** (Lakoff §1): past (or future) morphology applied to a
    present-time event because the speaker does not find it salient.

    Past example: "The animal you saw WAS a chipmunk" (it still IS one).
    Future example: "That thing WILL be a chipmunk" (it already IS one).
    The licensing condition is the same for both; the surface-form
    divergence is recorded in the Fragment entries (`formType`). -/
def falsePast (f : TensePerspective Time) : Prop :=
  f.eventTime = f.speechTime ∧ ¬(f.speakerSalience = true)

/-- **Novel-information present** (Lakoff §2): present tense survives under
    a past-tense matrix verb because the embedded content is new to the
    hearer ("He discovered that the boy HAS blue eyes"). -/
def novelInfoPresent (f : TensePerspective Time) : Prop :=
  f.hearerNovelty = true ∧ f.eventTime = f.speechTime

/-- **Perfect requires salience** (Lakoff §4): the present perfect is
    infelicitous when the event lacks current relevance to the speaker
    (*"Shakespeare has quarreled with Bacon"). -/
def perfectRequiresSalience (f : TensePerspective Time) : Prop :=
  f.speakerSalience = true

/-- **Will-deletion** (Lakoff §5): future-time events can appear in present
    tense (deleting *will*) when the speaker treats them as salient and
    scheduled ("The meeting starts at 3"). -/
def willDeletion [LT Time] (f : TensePerspective Time) : Prop :=
  f.speechTime < f.eventTime ∧ f.speakerSalience = true

/-- Classify a tense use as true (grammatical tense matches the temporal
    relation) or false (tense encodes psychological perspective instead),
    reusing the `TenseUseType` classification of the judgment data.

    *Derived, not stipulated*: the use is *true* exactly when the event-vs-speech
    comparison falls in the tense's `Finset Ordering` cell
    (`Core.Order.holds gramTense f.eventTime f.speechTime`), reproducing the
    four-way past/present/future/nonpast table (`before`: `E < S`; `overlapping`:
    `E = S`; `after`: `S < E`; `notBefore`: `S ≤ E`). -/
def classifyUse [LinearOrder Time] (gramTense : Finset Ordering)
    (f : TensePerspective Time) : TenseUseType :=
  if Core.Order.holds gramTense f.eventTime f.speechTime then .trueTense else .falseTense

open Morphology.Tense in
/-- **Periphrastic forms block false tense** (Lakoff §1, ex. 8a vs 9a):
    a false tense use demands a synthetic form; true tense is compatible
    with any form. -/
def FalseTenseLicensed (use : TenseUseType) (form : TenseFormType) : Prop :=
  use = .falseTense → form = .synthetic

-- ════════════════════════════════════════════════════
-- § 8. Bridge: Fragment and Theory Connections
-- ════════════════════════════════════════════════════

open English.Tense
open Morphology.Tense

theorem ex4a_formType :
    ex4a.formType = simplePastPerspective.formType := rfl

theorem ex8a_formType :
    ex8a.formType = usedTo.formType := rfl

theorem ex9a_formType :
    ex9a.formType = usedTo.formType := rfl

theorem synthetic_allows_false_tense :
    FalseTenseLicensed .falseTense .synthetic := λ _ => rfl

theorem periphrastic_blocks_false_tense :
    ¬ FalseTenseLicensed .falseTense .periphrastic := λ h => nomatch h rfl

theorem true_tense_any_form :
    FalseTenseLicensed .trueTense .periphrastic := λ h => nomatch h

theorem usedTo_entry_blocks_false :
    usedTo.allowsFalseTense = false := rfl

theorem simplePast_entry_allows_false :
    simplePastPerspective.allowsFalseTense = true := rfl

/-- A false past is temporally present — the mismatch is purely
    psychological (salience), not temporal. -/
theorem false_past_is_temporally_present (f : TensePerspective Time)
    (h : falsePast f) :
    f.eventTime = f.speechTime :=
  h.1

/-- When `falsePast` holds, the UP present-tense constraint (T = S) of
    [cumming-2026]'s `UPCondition.present` is satisfied. -/
theorem false_past_satisfies_up_present (f : TensePerspective ℤ)
    (h : falsePast f) :
    UPCondition.present.toConstraint f.toEvidentialFrame :=
  h.1

theorem false_past_classified_correctly [LinearOrder Time]
    (f : TensePerspective Time) (h : falsePast f) :
    classifyUse Tense.past f = .falseTense := by
  simp only [classifyUse, Tense.past, Core.Order.holds_before]
  exact if_neg (by rw [h.1]; exact lt_irrefl _)

theorem will_deletion_requires_future_and_salience (f : TensePerspective ℤ)
    (h : willDeletion f) :
    f.speechTime < f.eventTime ∧ f.speakerSalience = true :=
  h

theorem grammatical_false_tense_all_synthetic :
    (falseTenseJudgments.filter
      (λ j => j.acceptability == .grammatical)).all
      (λ j => j.formType == .synthetic) = true := rfl

theorem false_periphrastic_is_ungrammatical :
    (ex8a.tenseUse == .falseTense &&
     ex8a.formType == .periphrastic &&
     ex8a.acceptability == .ungrammatical) = true := rfl

end Lakoff1970
