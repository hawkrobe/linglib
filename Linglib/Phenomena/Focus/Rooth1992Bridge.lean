import Linglib.Core.InformationStructure
import Linglib.Theories.Semantics.Focus.Interpretation
import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Theories.Semantics.Montague.Composition
import Linglib.Theories.Semantics.Montague.Derivation
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.Focus.Basic

/-!
# Rooth (1992) Bridge — Focus Interpretation @cite{rooth-1992}

Bridges the empirical data in `Focus/Basic.lean` to the formal theory
in `Focus/Interpretation.lean` (FIP, Q-A congruence), with a full
compositional derivational chain through Montague semantics and
connection to English fragment entries.

## Pipeline

```
Fragments/English/Nouns  ──▷  Montague Lexicon  ──▷  SynTree
                                                        │
                                                    interpTree
                                                        │
                                                        ▼
                              propositions (QAWorld → Bool)
                                                        │
                                                   fromAlternatives
                                                        │
                                                        ▼
                                              QuestionDen / PropFocusValue
                                                        │
                                                   FIP / qaCongruent
                                                        │
                                                        ▼
                                              Bridge theorems ↔ Data
```

## Model

- Q-A congruence: 4 worlds crossing subject (Fred/Mary) × object
  (beans/rice). Subject focus matches "Who ate the beans?";
  object focus does not.
- "Only" association: 3 worlds for who Mary introduced to Sue.

## What's exercised

- `AltMeaning`, `AltMeaning.unfeatured` — O/A-value computation (§3)
- `Focus`, `Background` — focus/background partition (§4)
- `Theme`, `Rheme`, `InfoStructure` — information structure analysis (§5)
- `HasInfoStructure` — typeclass instance (§5b)
- `FIPApplication` — FIP application classification (§8)
- `SynTree`, `interpTree` — compositional derivation (§10–§11)
- `SemDeriv` — derivation bundles (§13)
- `Fragments.English.Nouns`, `.Predicates.Verbal` — fragment entries (§14)

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

-- ═══════════════════════════════════════════════════════════════════════
-- §10  Montague Model and Compositional Lexicon
-- ═══════════════════════════════════════════════════════════════════════

/-! The propositions in §2 were hand-defined. Here we derive them
    compositionally: entity denotations + a world-indexed verb meaning
    are combined via Montague's `interpSVO` and Heim & Kratzer's
    `interpTree` to produce the same truth conditions.

    The derivational chain is:
      Fragment entry → Montague LexEntry → SynTree → interpTree → Bool
    run once per world to yield a world-indexed proposition. -/

open Semantics.Montague
open Semantics.Montague.Composition

/-- Entity domain for the focus model. -/
inductive E where
  | fred | mary | beans | rice
  deriving DecidableEq, BEq, Repr

def focusModel : Model := { Entity := E, decEq := inferInstance }

/-- World-indexed verb semantics for "ate".
    `ateInWorld w obj subj` follows Montague's argument order
    (object first, then subject — cf. `interpSVO`). -/
def ateInWorld (w : QAWorld) : focusModel.interpTy (.e ⇒ .e ⇒ .t) :=
  fun obj subj => match w, subj, obj with
  | .fredBeans, .fred, .beans => true
  | .fredRice,  .fred, .rice  => true
  | .maryBeans, .mary, .beans => true
  | .maryRice,  .mary, .rice  => true
  | _, _, _ => false

/-- Montague lexicon parameterized by world.
    Maps surface forms to typed denotations. -/
def focusLex (w : QAWorld) : Lexicon focusModel := fun word =>
  match word with
  | "Fred"  => some ⟨.e, E.fred⟩
  | "Mary"  => some ⟨.e, E.mary⟩
  | "ate"   => some ⟨.e ⇒ .e ⇒ .t, ateInWorld w⟩
  | "beans" => some ⟨.e, E.beans⟩
  | "rice"  => some ⟨.e, E.rice⟩
  | _ => none

-- ═══════════════════════════════════════════════════════════════════════
-- §11  Syntax Trees and Compositional Interpretation
-- ═══════════════════════════════════════════════════════════════════════

/-- Syntax tree: [S [NP Fred] [VP [V ate] [NP beans]]] -/
def tree_fredAteBeans : SynTree :=
  .binary (.terminal "Fred") (.binary (.terminal "ate") (.terminal "beans"))

/-- Syntax tree: [S [NP Mary] [VP [V ate] [NP beans]]] -/
def tree_maryAteBeans : SynTree :=
  .binary (.terminal "Mary") (.binary (.terminal "ate") (.terminal "beans"))

/-- Syntax tree: [S [NP Fred] [VP [V ate] [NP rice]]] -/
def tree_fredAteRice : SynTree :=
  .binary (.terminal "Fred") (.binary (.terminal "ate") (.terminal "rice"))

/-- Extract the Bool truth value from a tree interpretation.
    Returns `none` if the tree is uninterpretable or has non-`t` type. -/
def treeResult (lex : Lexicon focusModel) (t : SynTree) : Option Bool :=
  match interpTree focusModel lex t with
  | some ⟨.t, b⟩ => some b
  | _ => none

-- ═══════════════════════════════════════════════════════════════════════
-- §12  Grounding: Compositional Meaning = Hand-Defined Propositions
-- ═══════════════════════════════════════════════════════════════════════

/-! The propositions from §2 were stipulated directly. Here we show
    they are derivable: running `interpTree` at each world produces
    the same truth values. -/

/-- Compositionally derived "Fred ate beans" proposition. -/
def fredAteBeans_comp : QAWorld → Bool :=
  fun w => (treeResult (focusLex w) tree_fredAteBeans).getD false

/-- Compositionally derived "Mary ate beans" proposition. -/
def maryAteBeans_comp : QAWorld → Bool :=
  fun w => (treeResult (focusLex w) tree_maryAteBeans).getD false

/-- Compositionally derived "Fred ate rice" proposition. -/
def fredAteRice_comp : QAWorld → Bool :=
  fun w => (treeResult (focusLex w) tree_fredAteRice).getD false

/-- Grounding: compositional "Fred ate beans" = hand-defined proposition. -/
theorem comp_grounds_fredAteBeans :
    fredAteBeans_comp = fredAteBeans := by
  funext w; cases w <;> native_decide

/-- Grounding: compositional "Mary ate beans" = hand-defined proposition. -/
theorem comp_grounds_maryAteBeans :
    maryAteBeans_comp = maryAteBeans := by
  funext w; cases w <;> native_decide

/-- Grounding: compositional "Fred ate rice" = hand-defined proposition. -/
theorem comp_grounds_fredAteRice :
    fredAteRice_comp = fredAteRice := by
  funext w; cases w <;> native_decide

/-- Direct composition matches tree interpretation. -/
theorem interpSVO_eq_interpTree (w : QAWorld) :
    treeResult (focusLex w) tree_fredAteBeans =
    some (interpSVO focusModel E.fred (ateInWorld w) E.beans) := by
  cases w <;> native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §13  SemDeriv: Derivation Bundles
-- ═══════════════════════════════════════════════════════════════════════

open Semantics.Montague.Derivation

/-- Semantic derivation bundle for "Fred ate beans" at world w.
    Packages surface form + Montague type + compositional meaning. -/
def fredAteBeans_deriv (w : QAWorld) : SemDeriv focusModel :=
  { surface := ["Fred", "ate", "beans"]
  , ty := .t
  , meaning := interpSVO focusModel E.fred (ateInWorld w) E.beans }

/-- The derivation sentence matches the surface string. -/
theorem deriv_sentence :
    (fredAteBeans_deriv .fredBeans).sentence = "Fred ate beans" := rfl

/-- The derivation meaning is true in the correct world. -/
theorem deriv_true_in_actual :
    (fredAteBeans_deriv .fredBeans).meaning = true := rfl

/-- The derivation meaning is false in other worlds. -/
theorem deriv_false_elsewhere :
    (fredAteBeans_deriv .maryBeans).meaning = false := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §14  Fragment Connection
-- ═══════════════════════════════════════════════════════════════════════

/-! Connect the model's lexicon to English fragment entries. Fragment
    entries provide morphological and syntactic properties; the bridge
    verifies that these properties are consistent with the model and
    that fragment surface forms feed the compositional lexicon. -/

section FragmentNouns
open Fragments.English.Nouns

/-- Fred is a proper name in the English fragment. -/
theorem fragment_fred_proper : fred.proper = true := rfl

/-- Mary is a proper name in the English fragment. -/
theorem fragment_mary_proper : mary.proper = true := rfl

/-- "bean" is countable in the English fragment. -/
theorem fragment_bean_countable : bean.countable = true := rfl

/-- Fragment surface forms feed the Montague lexicon.
    The form field of each fragment entry matches a lexicon key. -/
theorem fragment_fred_in_lexicon :
    (focusLex .fredBeans fred.formSg).isSome = true := rfl

theorem fragment_mary_in_lexicon :
    (focusLex .fredBeans mary.formSg).isSome = true := rfl

theorem fragment_bean_pl_in_lexicon :
    (focusLex .fredBeans (bean.formPl.getD "")).isSome = true := rfl

end FragmentNouns

section FragmentVerbs
open Fragments.English.Predicates.Verbal

/-- "eat" is transitive (NP complement). -/
theorem fragment_eat_transitive : eat.complementType = .np := rfl

/-- "eat" has past tense "ate" matching the lexicon entry. -/
theorem fragment_eat_past_form : eat.formPast = "ate" := rfl

/-- The past form of "eat" is in the Montague lexicon. -/
theorem fragment_eat_past_in_lexicon :
    (focusLex .fredBeans eat.formPast).isSome = true := rfl

/-- "eat" assigns agent to subject and patient to object. -/
theorem fragment_eat_agent_patient :
    eat.subjectTheta = some .agent ∧
    eat.objectTheta = some .patient := ⟨rfl, rfl⟩

end FragmentVerbs

-- ═══════════════════════════════════════════════════════════════════════
-- §15  Full End-to-End Chain
-- ═══════════════════════════════════════════════════════════════════════

/-! The complete derivational chain from fragments to FIP:

    1. Fragment entries (§14) provide surface forms and properties
    2. Surface forms feed the Montague lexicon (§10)
    3. SynTree derivations compose meanings via interpTree (§11)
    4. Running at each world yields propositions grounding §2 (§12)
    5. Propositions build Hamblin questions and focus values (§6)
    6. FIP/qaCongruent proves congruence (§6a) or incongruence (§6b)
    7. Theoretical predictions match empirical judgments (§9) -/

/-- End-to-end: the compositionally derived question matches the
    hand-built question, so the FIP results in §6 apply to the
    compositional derivation. -/
theorem endToEnd_question_grounded :
    fromAlternatives [fredAteBeans_comp, maryAteBeans_comp] qaWorlds =
    q_whoAteBeans := by
  funext p; simp only [fromAlternatives, q_whoAteBeans, fredAteBeans_comp]
  cases p fredBeans <;> cases p fredRice <;> cases p maryBeans <;> cases p maryRice <;> rfl

end Phenomena.Focus.Rooth1992Bridge
