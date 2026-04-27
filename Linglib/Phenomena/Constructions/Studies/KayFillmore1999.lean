import Linglib.Phenomena.Constructions.Studies.FillmoreKayOConnor1988
import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Semantics.CommonGround
import Linglib.Theories.Pragmatics.Expressives.Basic
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Core.Question.Hamblin
import Linglib.Theories.Interfaces.SyntaxSemantics.LeftPeriphery
import Linglib.Theories.Syntax.ConstructionGrammar.Studies.FillmoreKayOConnor1988
import Linglib.Phenomena.TenseAspect.Diagnostics

/-!
# @cite{kay-fillmore-1999}: *What's X Doing Y?* — Empirical Data
@cite{kay-fillmore-1999}

Theory-neutral judgment data from "Grammatical Constructions and Linguistic
Generalizations: The *What's X doing Y?* Construction" (Language 75(1):1–33).

## Phenomena covered

1. **Incredulity reading**: "What's this fly doing in my soup?" (speaker knows the answer)
2. **Literal question reading**: "What's John doing in the kitchen?" (genuine information-seeking)
3. **Progressive requirement**: WXDY requires progressive *doing*; bare infinitive is out
4. **Subject referentiality**: referential subjects OK; non-referential degraded
5. **Complement types**: locative PP, participial VP, instrumental PP
6. **Ambiguity**: sentences admitting both readings
7. **Embedding / CI projection**: WXDY meaning under embedding predicates
8. **FKO1988 comparison**: relation to Incredulity Response construction

-/

namespace KayFillmore1999

open FillmoreKayOConnor1988
open Features (Acceptability)

/-- Check if a string contains a substring. -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-! ## Reading type -/

/-- The available readings of a WXDY sentence. -/
inductive WXDYReading where
  | literal       -- genuine information-seeking question
  | incredulity   -- speaker expresses surprise/disapproval at the situation
  | ambiguous     -- both readings available
  deriving Repr, DecidableEq

/-! ## Datum structure -/

/-- A single WXDY example with judgment and reading information. -/
structure WXDYDatum where
  /-- Example identifier -/
  exId : String
  /-- The sentence -/
  sentence : String
  /-- Acceptability judgment -/
  judgment : Acceptability
  /-- Available reading(s) -/
  reading : WXDYReading
  /-- What phenomenon this illustrates -/
  phenomenon : String
  deriving Repr, BEq

/-! ## 1. Basic incredulity (§1, pp.1–3) -/

def fly_in_soup : WXDYDatum :=
  { exId := "1"
  , sentence := "What's this fly doing in my soup?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "canonical incredulity: speaker sees the fly" }

def cat_on_table : WXDYDatum :=
  { exId := "2"
  , sentence := "What's the cat doing on the dinner table?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "incredulity: speaker disapproves of cat's location" }

def car_in_driveway : WXDYDatum :=
  { exId := "3"
  , sentence := "What's that car doing in my driveway?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "incredulity: referential subject + locative PP" }

/-! ## 2. Literal question (genuine information-seeking) -/

def john_in_kitchen_literal : WXDYDatum :=
  { exId := "4"
  , sentence := "What's John doing in the kitchen?"
  , judgment := .ok
  , reading := .literal
  , phenomenon := "literal question: speaker genuinely asks about activity" }

def mary_with_scissors : WXDYDatum :=
  { exId := "5"
  , sentence := "What's Mary doing with those scissors?"
  , judgment := .ok
  , reading := .literal
  , phenomenon := "literal question: instrumental PP complement" }

/-! ## 3. Progressive requirement (§2.2)

WXDY requires the progressive auxiliary + *doing*. Without it, only a
standard wh-question remains; the incredulity reading disappears. -/

def no_progressive : WXDYDatum :=
  { exId := "6"
  , sentence := "*What does this fly do in my soup?"
  , judgment := .unacceptable
  , reading := .incredulity
  , phenomenon := "incredulity lost without progressive" }

def habitual_do : WXDYDatum :=
  { exId := "7"
  , sentence := "What does John do in the kitchen?"
  , judgment := .ok
  , reading := .literal
  , phenomenon := "habitual reading OK, but no incredulity" }

def bare_infinitive : WXDYDatum :=
  { exId := "8"
  , sentence := "*What's this fly do in my soup?"
  , judgment := .unacceptable
  , reading := .incredulity
  , phenomenon := "bare infinitive blocks WXDY construction" }

/-! ## 4. Subject referentiality (§2.3)

Referential subjects are fine; non-referential or quantified subjects
are degraded on the incredulity reading. -/

def referential_subject : WXDYDatum :=
  { exId := "9"
  , sentence := "What's this book doing on the floor?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "demonstrative subject: fully referential" }

def nonreferential_subject : WXDYDatum :=
  { exId := "10"
  , sentence := "?What's something doing on the floor?"
  , judgment := .marginal
  , reading := .incredulity
  , phenomenon := "indefinite subject: degraded incredulity reading" }

/-! ## 5. Complement types (§2.4)

WXDY accepts various complement types: locative PPs, participial VPs,
and instrumental PPs. -/

def locative_pp : WXDYDatum :=
  { exId := "11"
  , sentence := "What's my coat doing on the floor?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "locative PP complement" }

def participial_vp : WXDYDatum :=
  { exId := "12"
  , sentence := "What's John doing reading my diary?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "participial VP complement" }

def instrumental_pp : WXDYDatum :=
  { exId := "13"
  , sentence := "What are you doing with my car keys?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "instrumental PP complement" }

/-! ## 6. Ambiguous (both readings available) -/

def john_in_kitchen_ambig : WXDYDatum :=
  { exId := "14"
  , sentence := "What's John doing in the garden?"
  , judgment := .ok
  , reading := .ambiguous
  , phenomenon := "ambiguous: genuine Q or incredulity depending on context" }

def dog_on_couch : WXDYDatum :=
  { exId := "15"
  , sentence := "What's the dog doing on the couch?"
  , judgment := .ok
  , reading := .ambiguous
  , phenomenon := "ambiguous: activity Q or disapproval" }

/-! ## 7. Embedding / CI projection (§3)

Under embedding, the incredulity component projects like a CI. -/

def embedded_wonder : WXDYDatum :=
  { exId := "16"
  , sentence := "I wonder what this fly is doing in my soup"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "embedded: incredulity projects through wonder" }

def embedded_tell : WXDYDatum :=
  { exId := "17"
  , sentence := "Tell me what your shoes are doing on the table"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "embedded: incredulity projects through imperative" }

/-! ## 8. FKO1988 comparison

WXDY relates to the Incredulity Response construction from FKO1988
("Him be a doctor?"). Both express speaker incredulity via non-standard
question form. -/

def fko_comparison : WXDYDatum :=
  { exId := "18"
  , sentence := "What's HIM doing being a doctor?"
  , judgment := .ok
  , reading := .incredulity
  , phenomenon := "WXDY with accusative subject: cf. FKO1988 Incredulity Response" }

/-! ## All data -/

def allExamples : List WXDYDatum :=
  [ fly_in_soup, cat_on_table, car_in_driveway
  , john_in_kitchen_literal, mary_with_scissors
  , no_progressive, habitual_do, bare_infinitive
  , referential_subject, nonreferential_subject
  , locative_pp, participial_vp, instrumental_pp
  , john_in_kitchen_ambig, dog_on_couch
  , embedded_wonder, embedded_tell
  , fko_comparison ]

/-! ## Verification theorems -/

/-- Both readings are attested in the data. -/
theorem has_both_readings :
    (allExamples.any (·.reading == .literal)) = true ∧
    (allExamples.any (·.reading == .incredulity)) = true ∧
    (allExamples.any (·.reading == .ambiguous)) = true := by
  constructor; native_decide
  constructor; native_decide
  native_decide

/-- All judgment types are represented. -/
theorem has_all_judgment_types :
    (allExamples.any (·.judgment == .ok)) = true ∧
    (allExamples.any (·.judgment == .unacceptable)) = true ∧
    (allExamples.any (·.judgment == .marginal)) = true := by
  constructor; native_decide
  constructor; native_decide
  native_decide

/-- All grammatical WXDY examples with incredulity reading have progressive. -/
theorem progressive_is_required :
    (allExamples.filter (λ d =>
      d.judgment == .ok && d.reading != .literal
    )).all (λ d => containsSubstr d.sentence "doing" || containsSubstr d.sentence "is doing") = true := by
  native_decide

end KayFillmore1999

/-! ## Bridge content (merged from CxG_KayFillmore1999Bridge.lean) -/

/-!
# @cite{kay-fillmore-1999}: *What's X Doing Y?* Construction
@cite{kay-fillmore-1999} @cite{dayal-2025} @cite{potts-2005}

Formalization of "Grammatical Constructions and Linguistic Generalizations:
The *What's X doing Y?* Construction" (Language 75(1):1–33).

## Key insight

WXDY has interrogative *form* but expressive *function* on the incredulity
reading. This form–function mismatch is precisely what the existing
LeftPeriphery + Expressives + Presupposition infrastructure can derive:

- **Interrogative form**: +WH feature, wh-fronting, subject-aux inversion
- **Expressive function**: CI content (unexpectedness), presupposed proposition

The two readings are distinguished by the PerspectiveP layer:
- **Literal**: speaker is ignorant → PerspP satisfied → genuine question
- **Incredulity**: speaker knows the answer → PerspP blocked → not a real question

## Bridge targets (10 modules)

| # | Module | Bridge |
|---|--------|--------|
| 1 | `Core/Presupposition` | WXDY presupposes the embedded proposition |
| 2 | `Expressives/Basic` | Incredulity is CI content (projects through negation) |
| 3 | `Semantics.Questions/Hamblin` | Literal = standard `which`; incredulity = degenerate Q |
| 4 | `Interfaces.SyntaxSemantics/LeftPeriphery` | PerspP disambiguates the two readings |
| 5 | `Core/CommonGround` | Presupposition requires CG entailment |
| 6 | `Verb/Aspect` | Progressive requirement (durative ∧ dynamic) |
| 7 | `Focus/DomainWidening` | Incongruity = normative expectation violation |
| 8 | `Semantics.Questions/Polarity` | Incredulity = rhetorical question |
| 9 | `FKO1988` | WXDY is a formal idiom; sibling to Incredulity Response |
| 10 | `Phenomena/KayFillmore1999` | Per-datum verification |

-/

open KayFillmore1999
open FillmoreKayOConnor1988

namespace ConstructionGrammar.Studies.KayFillmore1999

open ConstructionGrammar

-- ============================================================================
-- A. Construction definition
-- ============================================================================

/-- The WXDY construction as a `Construction`.

Form: [CP What's [TP NP doing [VP/PP...]]]
- Interrogative form: wh-fronting, subject-aux inversion, +WH
- *doing* is frozen progressive: licenses the construction
- Complement: locative PP, participial VP, or instrumental PP -/
def wxdyConstruction : Construction :=
  { name := "What's X doing Y?"
  , form := "[CP What's [TP NP doing [VP/PP ...]]]"
  , meaning := "Incredulity: speaker presupposes embedded prop, expresses surprise; Literal: genuine activity question"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presupposes situation; CI: speaker finds it unexpected/inappropriate" }

-- ============================================================================
-- B. FKO1988 idiom classification bridge
-- ============================================================================

/-- WXDY is a formal idiom in FKO1988's typology: encoding (must learn the
incredulity convention), grammatical (fills proper grammatical slots),
formal (productive open pattern). -/
def wxdyIdiomType : FillmoreKayOConnor1988.IdiomType :=
  { interpretability := .encoding
  , grammaticality := .grammatical
  , formality := .formal }

/-- WXDY uses familiar pieces in a familiar arrangement: "what", "doing", etc.
are all standard English items in standard syntactic positions. The
non-compositional meaning (incredulity) is what must be learned. -/
def wxdyFamiliarity : FillmoreKayOConnor1988.FamiliarityPattern :=
  .familiarPiecesFamiliarlyArranged

/-- WXDY is a formal idiom: partially open, with pragmatic function. -/
theorem wxdy_is_formal_idiom :
    wxdyIdiomType.formality = .formal ∧
    wxdyConstruction.specificity = .partiallyOpen ∧
    wxdyConstruction.pragmaticFunction.isSome := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- C. CxG inheritance network
-- ============================================================================

/-- WXDY inherits from wh-questions: wh-fronting, +WH feature,
subject-aux inversion. Overrides: question semantics (on the incredulity
reading, it's not a genuine information-seeking question). -/
def wxdyInheritanceFromWhQ : InheritanceLink :=
  { parent := "Wh-question"
  , child := "What's X doing Y?"
  , mode := .normal
  , sharedProperties :=
      [ "wh-fronting"
      , "+WH feature on C"
      , "subject-aux inversion" ]
  , overriddenProperties :=
      [ "question semantics (incredulity reading is not info-seeking)" ] }

/-- WXDY inherits progressive morphology from the progressive construction:
*doing* carries -ing morphology. -/
def wxdyInheritanceFromProgressive : InheritanceLink :=
  { parent := "Progressive"
  , child := "What's X doing Y?"
  , mode := .normal
  , sharedProperties :=
      [ "-ing morphology on main verb"
      , "selects durative dynamic predicates" ]
  , overriddenProperties :=
      [ "progressive semantics (doing is frozen, not compositional progressive)" ] }

/-- WXDY and FKO1988's Incredulity Response ("Him be a doctor?") are
siblings in the "rhetorical question family" — both express incredulity
via non-standard question forms. -/
def wxdyInheritanceFromIncredulity : InheritanceLink :=
  { parent := "Rhetorical question family"
  , child := "What's X doing Y?"
  , mode := .normal
  , sharedProperties :=
      [ "interrogative form"
      , "expressive function (speaker incredulity)"
      , "speaker knows/presupposes the answer" ]
  , overriddenProperties :=
      [ "WXDY uses standard syntax; IR uses accusative subject + bare stem" ] }

/-- WXDY and the Incredulity Response share the same expressive family. -/
theorem wxdy_same_class_as_incredulity_response :
    wxdyInheritanceFromIncredulity.parent =
    "Rhetorical question family" := rfl

-- ============================================================================
-- D. Presupposition bridge (Core/Presupposition.lean)
-- ============================================================================

open Core.Presupposition

/-- On the incredulity reading, WXDY presupposes the embedded proposition
(the situation that the speaker finds surprising) and has trivial assertion.

"What's this fly doing in my soup?" presupposes: there is a fly in the soup.
The at-issue assertion is trivial — the point is to express the CI. -/
def wxdyPresup {W : Type*} (embeddedProp : W → Bool) : PrProp W :=
  PrProp.ofBool embeddedProp (λ _ => true)

/-- Presupposition projects through negation: "It's not the case that
[what's this fly doing in my soup]" still presupposes the fly is there. -/
theorem wxdy_presup_projects_neg {W : Type*} (embeddedProp : W → Bool) :
    ∀ w, (PrProp.neg (wxdyPresup embeddedProp)).presup w ↔
         (embeddedProp w = true) := by
  intro w; simp [wxdyPresup, PrProp.neg, PrProp.ofBool]

-- ============================================================================
-- E. Two-dimensional semantics bridge (Expressives/Basic.lean)
-- ============================================================================

open Pragmatics.Expressives

/-- WXDY on the incredulity reading has two-dimensional meaning:
- At-issue: the embedded proposition (there's a fly in my soup)
- CI: speaker finds this unexpected/inappropriate

This mirrors @cite{potts-2005}'s analysis of expressives: the expressive
content is independent of at-issue truth. -/
def wxdyTwoDim {W : Type*} (embeddedProp unexpectedness : W → Prop) : TwoDimProp W :=
  TwoDimProp.withCI embeddedProp unexpectedness

/-- WXDY's CI properties: perspective-dependent (speaker-oriented), not
repeatable (you don't say "What's this fly doing in my soup?" twice for
emphasis), immediate, independent, nondisplaceable, descriptively
ineffable (the unexpectedness resists paraphrase). -/
def wxdyCIProperties : SecondaryMeaningProperties :=
  { independent := true
  , nondisplaceable := true
  , perspectiveDependent := true
  , descriptivelyIneffable := true
  , immediate := true
  , repeatable := false
  , allowsPerspectiveShift := false
  , requiresDiscourseAntecedent := false }

/-- CI projects through negation: the unexpectedness meaning
survives under negation. Delegates to `TwoDimProp.ci_projects_through_neg`. -/
theorem wxdy_ci_projects_through_neg {W : Type*}
    (embeddedProp unexpectedness : W → Prop) :
    (TwoDimProp.neg (wxdyTwoDim embeddedProp unexpectedness)).ci = unexpectedness := by
  simp [wxdyTwoDim, TwoDimProp.withCI, TwoDimProp.neg]

/-- CI is independent of at-issue truth: the unexpectedness holds regardless
of whether the embedded proposition is true or false. -/
theorem wxdy_ci_independent {W : Type*}
    (embeddedProp unexpectedness : W → Prop) (w : W)
    (h_ci : unexpectedness w) :
    ((wxdyTwoDim embeddedProp unexpectedness).atIssue w →
      (wxdyTwoDim embeddedProp unexpectedness).ci w) ∧
    (¬ (wxdyTwoDim embeddedProp unexpectedness).atIssue w →
      (wxdyTwoDim embeddedProp unexpectedness).ci w) := by
  exact ⟨λ _ => h_ci, λ _ => h_ci⟩

-- ============================================================================
-- F. Hamblin question semantics bridge (Core/Question/Hamblin.lean substrate)
-- ============================================================================

open Core.Question

/-- Literal reading: standard wh-question "which activity is X engaged in?"
Delegates to substrate `Core.Question.which` over a domain of activities. -/
def wxdyLiteralQ {W E : Type*}
    (activities : Set E) (pred : E → Set W) : Core.Question W :=
  which activities pred

/-- Incredulity reading: degenerate question with only the presupposed
proposition as an answer. The "question" is not information-seeking;
the speaker already knows the answer.

In the substrate, this is the declarative principal ideal of the
presupposed proposition — a single-alternative question. -/
def wxdyIncredulityQ {W : Type*} (presupposedProp : Set W) : Core.Question W :=
  declarative presupposedProp

/-- The incredulity reading has exactly one alternative: the presupposed
proposition. The proposition itself is the unique alternative. -/
theorem incredulity_single_answer {W : Type*}
    (presupposedProp : Set W) :
    alt (wxdyIncredulityQ presupposedProp) = {presupposedProp} :=
  alt_declarative presupposedProp

/-- The literal reading is a genuine (non-degenerate) question: it delegates
to substrate `Core.Question.which`, which yields a Hamblin-style alternative
set indexed by the activity domain. -/
theorem literal_is_genuine_question {W E : Type*}
    (activities : Set E) (pred : E → Set W) :
    wxdyLiteralQ activities pred = which activities pred := rfl

-- ============================================================================
-- G. Left Periphery bridge (Interfaces.SyntaxSemantics/LeftPeriphery.lean) — DEEPEST BRIDGE
-- ============================================================================

open Interfaces.SyntaxSemantics.LeftPeriphery

/-- WXDY has a +WH feature on C (it is syntactically interrogative). -/
def wxdyWHFeature : WHFeature := .plusWH

/-- On the incredulity reading, the speaker KNOWS the answer to the question.
This is modeled as a veridical epistemic model at the evaluation world. -/
def wxdyIncredulitySpeakerModel {W : Type*} (w : W) : EpistemicModel W :=
  veridicalModel w

/-- CORE DERIVATION: Veridical speaker model → PerspP presupposition fails
→ not a real question.

On the incredulity reading, the speaker knows the answer (veridical model).
PerspP presupposes possible ignorance: ◇¬know(speaker, Ans(Q)).
But veridical knowledge contradicts possible ignorance.
Therefore PerspP is blocked, and the utterance is NOT a genuine question.

Delegates to `responsive_contradicts_perspP_comp` from LeftPeriphery.lean. -/
theorem wxdy_incredulity_blocks_perspP {W : Type*}
    (q : Semantics.Questions.GSQuestion W) (w : W) :
    perspPPresupComp (wxdyIncredulitySpeakerModel w) q w = false :=
  responsive_contradicts_perspP_comp q w

/-- On the literal reading, the speaker is genuinely ignorant (ignorant model).
PerspP presupposition is satisfied → genuine question.

Delegates to `rogative_allows_perspP_comp` from LeftPeriphery.lean. -/
theorem wxdy_literal_allows_perspP {W : Type*}
    (q : Semantics.Questions.GSQuestion W) (w : W) :
    perspPPresupComp ignorantModel q w = true :=
  rogative_allows_perspP_comp q w

/-- PerspP STATUS DISAMBIGUATES the two readings:
- Incredulity: PerspP fails (veridical model) → not a question → expressive
- Literal: PerspP succeeds (ignorant model) → genuine question

This is the deepest bridge: the form–function mismatch of WXDY is
*derived* from the PerspP mechanism, not stipulated. -/
theorem perspP_disambiguates_wxdy {W : Type*}
    (q : Semantics.Questions.GSQuestion W) (w : W) :
    perspPPresupComp (wxdyIncredulitySpeakerModel w) q w = false ∧
    perspPPresupComp ignorantModel q w = true :=
  ⟨wxdy_incredulity_blocks_perspP q w, wxdy_literal_allows_perspP q w⟩

-- ============================================================================
-- H. Common ground bridge (Core/CommonGround.lean)
-- ============================================================================

open Core.CommonGround

/-- The WXDY presupposition must be entailed by the common ground.
For "What's this fly doing in my soup?", the CG must already entail
that there is a fly in the soup (the speaker sees it). -/
theorem wxdy_presup_requires_cg {W : Type*}
    (c : ContextSet W) (embeddedProp : W → Bool)
    (h : c ⊧ (wxdyPresup embeddedProp).presup) (w : W) (hw : c w) :
    (wxdyPresup embeddedProp).presup w :=
  h hw

-- ============================================================================
-- I. Aspect bridge (Semantics.Montague/Verb/Aspect.lean + Diagnostics)
-- ============================================================================

open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Phenomena.TenseAspect.Diagnostics

/-- WXDY's *doing* selects for activities and accomplishments — predicates
that are durative ∧ dynamic. This connects to the progressive diagnostic:
`progressivePrediction =.accept ↔ durative ∧ dynamic`.

The progressive requirement in WXDY reflects the same aspectual constraint
as the standard progressive: it selects predicates with internal stages. -/
theorem wxdy_requires_progressive_aspect (c : VendlerClass) :
    progressivePrediction c = .accept ↔
    (c.duration = .durative ∧ c.dynamicity = .dynamic) :=
  progressive_accepts_durative_dynamic c

-- ============================================================================
-- L. Per-datum verification
-- ============================================================================

/-- All grammatical WXDY examples use progressive *doing*. -/
theorem progressive_required_all :
    (allExamples.filter (λ d : WXDYDatum =>
      d.judgment == .ok && d.reading != .literal
    )).all (λ d : WXDYDatum => containsSubstr d.sentence "doing" || containsSubstr d.sentence "is doing") = true := by
  native_decide

/-- The data contains all three reading types. -/
theorem all_readings_attested :
    (allExamples.any (λ d : WXDYDatum => d.reading == .literal)) = true ∧
    (allExamples.any (λ d : WXDYDatum => d.reading == .incredulity)) = true ∧
    (allExamples.any (λ d : WXDYDatum => d.reading == .ambiguous)) = true := by
  constructor; native_decide
  constructor; native_decide
  native_decide

end ConstructionGrammar.Studies.KayFillmore1999
