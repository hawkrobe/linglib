import Linglib.Theories.Morphology.Tense

/-!
# Lakoff (1970) Grammaticality Judgments

Pure empirical data from Lakoff (1970) "Tense and Its Relation to Participants."
No theoretical commitments — just the paper's acceptability judgments organized
by phenomenon.

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

## References

- Lakoff, R. (1970). Tense and its relation to participants. *Language* 46(4).
-/

namespace Phenomena.Tense.Studies.Lakoff1970.Data

open Core.Morphology.Tense

/-- Acceptability judgment for a tense example. -/
inductive Acceptability where
  | grammatical
  | ungrammatical
  | marginal
  deriving DecidableEq, Repr, BEq

/-- Whether the tense use is "true" (temporal) or "false" (psychological). -/
inductive TenseUseType where
  | trueTense
  | falseTense
  deriving DecidableEq, Repr, BEq

/-- A grammaticality judgment from Lakoff (1970). -/
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

end Phenomena.Tense.Studies.Lakoff1970.Data
