import Linglib.Core.InformationStructure
import Linglib.Theories.Semantics.Focus.Interpretation
import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Phenomena.Focus.Basic

/-!
# Rooth (1992) Bridge — Focus Interpretation

Bridges the empirical data in `Focus/Basic.lean` to the formal theory
in `Focus/Interpretation.lean` (FIP, Q-A congruence).

## Model

- Q-A congruence (§6): 4 worlds crossing subject (Fred/Mary) × object
  (beans/rice). Subject focus matches the question "Who ate the beans?";
  object focus does not.
- "Only" association (§7): 3 worlds for who Mary introduced to Sue.
  Focus determines the domain of quantification for "only" (Rooth §2.1,
  formalized in (30b) and (36–37)).

## Core.InformationStructure definitions exercised

- `AltMeaning`, `AltMeaning.unfeatured` — O/A-value computation (§3)
- `Focus`, `Background` — focus/background partition (§4)
- `Theme`, `Rheme`, `InfoStructure` — information structure analysis (§5)
- `HasInfoStructure` — typeclass instance (§5b)
- `FIPApplication` — FIP application classification (§8)

## References

- Rooth, M. (1992). A Theory of Focus Interpretation. NLS 1: 75-116.
-/

namespace Phenomena.Focus.Rooth1992Bridge

open Core.InformationStructure
open Semantics.FocusInterpretation (fip)
open Semantics.Questions.Hamblin

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Q-A Congruence World Model
-- ═══════════════════════════════════════════════════════════════════════

/-- Worlds crossing subject (Fred/Mary) × object (beans/rice).
    Sufficient to distinguish subject-focus from object-focus
    alternative sets. -/
inductive QAWorld where
  | fredBeans | fredRice | maryBeans | maryRice
  deriving DecidableEq, BEq, Repr

open QAWorld

def qaWorlds : List QAWorld := [fredBeans, fredRice, maryBeans, maryRice]

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Propositions
-- ═══════════════════════════════════════════════════════════════════════

/-- "Fred ate the beans" -/
def fredAteBeans : QAWorld → Bool | .fredBeans => true | _ => false

/-- "Mary ate the beans" -/
def maryAteBeans : QAWorld → Bool | .maryBeans => true | _ => false

/-- "Fred ate the rice" -/
def fredAteRice  : QAWorld → Bool | .fredRice  => true | _ => false

-- ═══════════════════════════════════════════════════════════════════════
-- §3  AltMeaning: Focused vs. Unfeatured
-- ═══════════════════════════════════════════════════════════════════════

/-- Focused "FRED" in "FRED ate the beans" (Rooth §2.4, ex. 23a):
    O-value = "Fred"; A-value = {"Fred", "Mary"}. -/
def altSubjectFocused : AltMeaning String :=
  { oValue := "Fred", aValue := ["Fred", "Mary"] }

/-- Non-focused "ate the beans": singleton A-value (no alternatives).
    Exercises `AltMeaning.unfeatured`. -/
def altPredicateUnfeatured : AltMeaning String :=
  AltMeaning.unfeatured "ate the beans"

/-- Unfeatured O-value equals the input. -/
theorem unfeatured_preserves_oValue :
    altPredicateUnfeatured.oValue = "ate the beans" := rfl

/-- Unfeatured A-value is a singleton containing the O-value.
    Non-focused expressions evoke no alternatives (Rooth 1992 §1). -/
theorem unfeatured_singleton_aValue :
    altPredicateUnfeatured.aValue = ["ate the beans"] := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Focus and Background Partition
-- ═══════════════════════════════════════════════════════════════════════

/-- Focus partition of "FRED ate the beans": Fred is focused,
    evoking {Fred, Mary} as alternatives (Rooth §2.4, ex. 25a). -/
def qaFocus : Focus String :=
  { focused := "Fred"
  , alternatives := ["Fred", "Mary"] }

/-- Background of "FRED ate the beans": the non-focused material. -/
def qaBackground : Background String :=
  { elements := ["ate", "the", "beans"] }

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Theme, Rheme, InfoStructure
-- ═══════════════════════════════════════════════════════════════════════

/-- Theme: the QUD presupposition "_ ate the beans" (λ-abstract).
    Rooth §2.4: in a Q-A pair, the theme corresponds to the
    question's content. -/
def qaTheme : Theme String :=
  { content := "λx. x ate the beans", marked := false }

/-- Rheme: the answer "Fred". -/
def qaRheme : Rheme String :=
  { content := "Fred", marked := true }

/-- Full information structure of "FRED ate the beans"
    in response to "Who ate the beans?" -/
def qaInfo : InfoStructure String :=
  { theme := qaTheme
  , rheme := qaRheme
  , foci := ["Fred"]
  , background := ["ate", "the", "beans"] }

/-- Theme carries the presupposed content. -/
theorem qa_theme_content :
    qaInfo.theme.content = "λx. x ate the beans" := rfl

/-- Rheme carries the asserted answer. -/
theorem qa_rheme_content :
    qaInfo.rheme.content = "Fred" := rfl

/-- Focus list matches the focused element. -/
theorem qa_foci_match :
    qaInfo.foci = [qaFocus.focused] := rfl

/-- Background list matches the background elements. -/
theorem qa_background_match :
    qaInfo.background = qaBackground.elements := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §5b  HasInfoStructure Instance
-- ═══════════════════════════════════════════════════════════════════════

/-- Minimal derivation type for exercising HasInfoStructure.
    Pairs a focused constituent with background material. -/
structure FocusedSentence where
  focusedWord : String
  backgroundWords : List String
  deriving Repr

/-- Exercises the HasInfoStructure typeclass:
    a FocusedSentence determines an InfoStructure. -/
instance : HasInfoStructure FocusedSentence String where
  infoStructure s :=
    { theme := { content := "background", marked := false }
    , rheme := { content := s.focusedWord, marked := true }
    , foci := [s.focusedWord]
    , background := s.backgroundWords }

def fredSentence : FocusedSentence :=
  { focusedWord := "Fred"
  , backgroundWords := ["ate", "the", "beans"] }

/-- The typeclass correctly extracts focus. -/
theorem infoStructure_extracts_focus :
    (HasInfoStructure.infoStructure fredSentence).foci = ["Fred"] := rfl

/-- The typeclass correctly extracts background. -/
theorem infoStructure_extracts_background :
    (HasInfoStructure.infoStructure fredSentence).background =
      ["ate", "the", "beans"] := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Q-A Congruence: FIP at the Propositional Level
-- ═══════════════════════════════════════════════════════════════════════

/-! Rooth (1992) §2.4, constraint (26d):
    In a Q-A pair ⟨ψ, α⟩, ⟦ψ⟧° ⊆ ⟦α⟧f.
    The ordinary semantic value of the question is a subset of the
    focus semantic value of the answer. -/

/-- "Who ate the beans?" — Hamblin question with subject alternatives.
    ⟦Q⟧° = {fredAteBeans, maryAteBeans} (Rooth §2.4, ex. 24). -/
def q_whoAteBeans : QuestionDen QAWorld :=
  fromAlternatives [fredAteBeans, maryAteBeans] qaWorlds

/-- Focus value of "[FRED]_F ate the beans" — same subject alternatives.
    ⟦A⟧f = {fredAteBeans, maryAteBeans} (Rooth §2.4, ex. 25a). -/
def fv_subjectFocus : QuestionDen QAWorld :=
  fromAlternatives [fredAteBeans, maryAteBeans] qaWorlds

/-- Focus value of "Fred ate the [BEANS]_F" — object alternatives.
    ⟦A⟧f = {fredAteBeans, fredAteRice} (varies object, not subject). -/
def fv_objectFocus : QuestionDen QAWorld :=
  fromAlternatives [fredAteBeans, fredAteRice] qaWorlds

-- ───────────────────────────────────────────────────────────────────
-- §6a  Congruent Case
-- ───────────────────────────────────────────────────────────────────

/-- Q-A congruence: subject focus value = question denotation.
    ⟦[FRED]_F ate the beans⟧f = ⟦Who ate the beans?⟧ (Rooth §2.4). -/
theorem qa_subject_focus_congruent :
    Semantics.FocusInterpretation.qaCongruent
      fv_subjectFocus q_whoAteBeans := rfl

/-- FIP (27) holds: question alternatives ⊆ focus value.
    Trivially satisfied when the sets are equal. -/
theorem fip_congruent :
    fip q_whoAteBeans fv_subjectFocus :=
  fun _ h => h

-- ───────────────────────────────────────────────────────────────────
-- §6b  Incongruent Case
-- ───────────────────────────────────────────────────────────────────

/-- FIP fails for object focus: "maryAteBeans" is in the question
    alternatives but not in the object-focus alternatives.
    This is why "#Fred ate the BEANS" is not a congruent answer
    to "Who ate the beans?" -/
theorem fip_fails_object_focus :
    ¬ fip q_whoAteBeans fv_objectFocus := by
  intro h
  exact absurd (h maryAteBeans (by native_decide)) (by native_decide)

/-- Witness: "Mary ate the beans" is an answer to the question... -/
theorem maryAteBeans_answers_question :
    isAnswer q_whoAteBeans maryAteBeans = true := by native_decide

/-- ...but is NOT in the object-focus alternative set. -/
theorem maryAteBeans_not_in_objectFocus :
    isAnswer fv_objectFocus maryAteBeans = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §7  "Only" Association (Rooth 1992 §2.1)
-- ═══════════════════════════════════════════════════════════════════════

/-! Rooth §2.1, constraint (26a): the domain of quantification C of
    a focusing adverb is a subset of the focus semantic value ⟦α⟧f.

    Rooth's formalization (30b): only(C) introduces
      ∀P[P ∈ C ∧ P(m) → P = VP']
    where C is constrained by the FIP to be a set of properties
    matching the focus semantic value. -/

/-- Worlds for the "only" model: who Mary introduced to Sue. -/
inductive OnlyWorld where
  | billOnly   -- Mary introduced only Bill to Sue
  | johnOnly   -- Mary introduced only John to Sue
  | both       -- Mary introduced both Bill and John
  deriving DecidableEq, BEq, Repr

open OnlyWorld

def onlyWorlds : List OnlyWorld := [billOnly, johnOnly, both]

/-- "Mary introduced Bill to Sue" -/
def introBill : OnlyWorld → Bool
  | billOnly => true | johnOnly => false | both => true

/-- "Mary introduced John to Sue" -/
def introJohn : OnlyWorld → Bool
  | billOnly => false | johnOnly => true | both => true

/-- Focus on BILL (Rooth §2.1, ex. 3a):
    O-value = introBill; A-value = {introBill, introJohn}.
    Focus determines the domain of "only". -/
def altBillFocused : AltMeaning (OnlyWorld → Bool) :=
  { oValue := introBill, aValue := [introBill, introJohn] }

/-- "Only Bill" = Mary introduced Bill but not John (Rooth §2.1). -/
def onlyBill : OnlyWorld → Bool
  | billOnly => true | _ => false

/-- "Only John" = Mary introduced John but not Bill. -/
def onlyJohn : OnlyWorld → Bool
  | johnOnly => true | _ => false

/-- "Only" with focus on BILL: O-value holds and all non-actual
    alternatives are excluded (Rooth §2.1, (30b)). -/
theorem only_bill_semantics :
    (onlyWorlds.all fun w =>
      onlyBill w == (introBill w && !introJohn w)) = true := by
  native_decide

/-- "Only" with focus on JOHN: symmetric case. -/
theorem only_john_semantics :
    (onlyWorlds.all fun w =>
      onlyJohn w == (introJohn w && !introBill w)) = true := by
  native_decide

/-- Different focus → different "only" meaning.
    Focus on BILL excludes John; focus on JOHN excludes Bill
    (Rooth §2.1, exs. 3a vs 3b). -/
theorem only_focus_determines_meaning :
    onlyBill ≠ onlyJohn := by
  intro h; exact absurd (congrFun h billOnly) (by decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Per-Datum Verification (connect to Focus/Basic.lean)
-- ═══════════════════════════════════════════════════════════════════════

/-- The Q-A congruent datum uses the correct FIPApplication. -/
theorem datum_qa_congruent_app :
    Basic.qaCongruent.application = .qaCongruence := rfl

/-- The Q-A incongruent datum uses the correct FIPApplication. -/
theorem datum_qa_incongruent_app :
    Basic.qaIncongruent.application = .qaCongruence := rfl

/-- Focus in the congruent answer matches the data. -/
theorem datum_qa_congruent_focus :
    Basic.qaCongruent.focus = "Fred" := rfl

/-- Focus in the incongruent answer matches the data. -/
theorem datum_qa_incongruent_focus :
    Basic.qaIncongruent.focus = "beans" := rfl

/-- The "only Bill" datum uses focusing adverb application. -/
theorem datum_only_bill_app :
    Basic.roothOnlyBill.application = .focusingAdverb := rfl

/-- The "only Sue" datum uses focusing adverb application. -/
theorem datum_only_sue_app :
    Basic.roothOnlySue.application = .focusingAdverb := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §9  Bridge: Data ↔ Theory
-- ═══════════════════════════════════════════════════════════════════════

/-! The data (Basic.lean) says "FRED ate the beans" is congruent and
    "#Fred ate the BEANS" is incongruent with "Who ate the beans?".
    The theory (FIP, §6) explains:

    - Subject focus produces a focus value equal to the question
      denotation (§6a), so FIP is satisfied.
    - Object focus produces a focus value that differs (§6b):
      maryAteBeans ∈ ⟦Q⟧° but maryAteBeans ∉ ⟦A⟧f, so FIP fails.

    For "only" (§7), the data says focus determines what "only"
    excludes. The theory confirms: the FIP constrains the domain C
    of "only" to be a subset of the focus value, so different focus
    positions yield different exclusion domains. -/

/-- Bridge: congruent judgment confirmed by FIP. -/
theorem bridge_qa_congruent :
    Basic.qaCongruent.application = .qaCongruence ∧
    Semantics.FocusInterpretation.qaCongruent
      fv_subjectFocus q_whoAteBeans :=
  ⟨rfl, rfl⟩

/-- Bridge: incongruent judgment explained by FIP failure. -/
theorem bridge_qa_incongruent :
    Basic.qaIncongruent.application = .qaCongruence ∧
    ¬ fip q_whoAteBeans fv_objectFocus := by
  constructor
  · rfl
  · intro h
    exact absurd (h maryAteBeans (by native_decide)) (by native_decide)

end Phenomena.Focus.Rooth1992Bridge
