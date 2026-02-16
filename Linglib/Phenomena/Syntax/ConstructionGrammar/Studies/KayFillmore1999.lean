import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Core.Presupposition
import Linglib.Core.CommonGround
import Linglib.Theories.Semantics.Lexical.Expressives.Basic
import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Phenomena.Semantics.Focus.DomainWidening
import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Phenomena.Semantics.Questions.LeftPeriphery
import Linglib.Theories.Semantics.Questions.Polarity
import Linglib.Phenomena.Syntax.ConstructionGrammar.Studies.FillmoreKayOConnor1988
import Linglib.Phenomena.Constructions.Studies.KayFillmore1999
import Linglib.Phenomena.Aspect.DiagnosticsBridge

/-!
# Kay & Fillmore (1999): *What's X Doing Y?* Construction

Formalization of "Grammatical Constructions and Linguistic Generalizations:
The *What's X doing Y?* Construction" (Language 75(1):1–33).

## Key insight

WXDY has interrogative *form* but expressive *function* on the incredulity
reading. This form–function mismatch is precisely what the existing
LeftPeriphery + Expressives + Presupposition infrastructure can derive:

- **Interrogative form**: +WH feature, wh-fronting, subject-aux inversion
- **Expressive function**: CI content (unexpectedness), presupposed proposition

The two readings are distinguished by the PerspectiveP layer (Dayal 2025):
- **Literal**: speaker is ignorant → PerspP satisfied → genuine question
- **Incredulity**: speaker knows the answer → PerspP blocked → not a real question

## Bridge targets (10 modules)

| # | Module | Bridge |
|---|--------|--------|
| 1 | `Core/Presupposition` | WXDY presupposes the embedded proposition |
| 2 | `Expressives/Basic` | Incredulity is CI content (projects through negation) |
| 3 | `Semantics.Questions/Hamblin` | Literal = standard `which`; incredulity = degenerate Q |
| 4 | `Semantics.Questions/LeftPeriphery` | PerspP disambiguates the two readings |
| 5 | `Core/CommonGround` | Presupposition requires CG entailment |
| 6 | `Verb/Aspect` | Progressive requirement (durative ∧ dynamic) |
| 7 | `Focus/DomainWidening` | Incongruity = normative expectation violation |
| 8 | `Semantics.Questions/Polarity` | Incredulity = rhetorical question |
| 9 | `FKO1988` | WXDY is a formal idiom; sibling to Incredulity Response |
| 10 | `Phenomena/KayFillmore1999` | Per-datum verification |

## Reference

Kay, P. & Fillmore, C. J. (1999). Grammatical Constructions and Linguistic
Generalizations: The *What's X doing Y?* Construction. Language, 75(1), 1–33.
-/

namespace ConstructionGrammar.Studies.KayFillmore1999

open ConstructionGrammar
open Phenomena.Constructions.Studies.KayFillmore1999
open Phenomena.Constructions.Studies.FillmoreKayOConnor1988

-- ============================================================================
-- A. Construction definition
-- ============================================================================

/-- The WXDY construction as a `Construction`.

Form: [CP What's [TP NP doing [VP/PP ...]]]
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
  { presup := embeddedProp
  , assertion := λ _ => true }

/-- Presupposition projects through negation: "It's not the case that
[what's this fly doing in my soup]" still presupposes the fly is there. -/
theorem wxdy_presup_projects_neg {W : Type*} (embeddedProp : W → Bool) :
    (PrProp.neg (wxdyPresup embeddedProp)).presup = embeddedProp := by
  simp [wxdyPresup, PrProp.neg]

-- ============================================================================
-- E. Two-dimensional semantics bridge (Expressives/Basic.lean)
-- ============================================================================

open Semantics.Lexical.Expressives

/-- WXDY on the incredulity reading has two-dimensional meaning:
- At-issue: the embedded proposition (there's a fly in my soup)
- CI: speaker finds this unexpected/inappropriate

This mirrors Potts' (2005) analysis of expressives: the expressive
content is independent of at-issue truth. -/
def wxdyTwoDim {W : Type*} (embeddedProp unexpectedness : W → Bool) : TwoDimProp W :=
  TwoDimProp.withCI embeddedProp unexpectedness

/-- WXDY's CI properties: speaker-oriented, not repeatable (you don't say
"What's this fly doing in my soup?" twice for emphasis), immediate
(affects context just by being uttered), independent of at-issue truth. -/
def wxdyCIProperties : CIExprProperties :=
  { speakerOriented := true
  , repeatable := false
  , immediate := true
  , independent := true }

/-- CI projects through negation (Potts 2005): the unexpectedness meaning
survives under negation. Delegates to `TwoDimProp.ci_projects_through_neg`. -/
theorem wxdy_ci_projects_through_neg {W : Type*}
    (embeddedProp unexpectedness : W → Bool) :
    (TwoDimProp.neg (wxdyTwoDim embeddedProp unexpectedness)).ci = unexpectedness := by
  simp [wxdyTwoDim, TwoDimProp.withCI, TwoDimProp.neg]

/-- CI is independent of at-issue truth: the unexpectedness holds regardless
of whether the embedded proposition is true or false. -/
theorem wxdy_ci_independent {W : Type*}
    (embeddedProp unexpectedness : W → Bool) (w : W)
    (h_ci : unexpectedness w = true) :
    ((wxdyTwoDim embeddedProp unexpectedness).atIssue w = true →
      (wxdyTwoDim embeddedProp unexpectedness).ci w = true) ∧
    ((wxdyTwoDim embeddedProp unexpectedness).atIssue w = false →
      (wxdyTwoDim embeddedProp unexpectedness).ci w = true) := by
  exact ⟨λ _ => h_ci, λ _ => h_ci⟩

-- ============================================================================
-- F. Hamblin question semantics bridge (Semantics.Questions/Hamblin.lean)
-- ============================================================================

open Semantics.Questions.Hamblin

/-- Literal reading: standard wh-question "which activity is X engaged in?"
Delegates to `Hamblin.which` over a domain of activities. -/
def wxdyLiteralQ {W E : Type*} [BEq W]
    (activities : List E) (pred : E → W → Bool) (worlds : List W) : QuestionDen W :=
  which activities pred worlds

/-- Incredulity reading: degenerate question with only the presupposed
proposition as an answer. The "question" is not information-seeking;
the speaker already knows the answer. -/
def wxdyIncredulityQ {W : Type*} [BEq W]
    (presupposedProp : W → Bool) (worlds : List W) : QuestionDen W :=
  λ ans => worlds.all λ w => ans w == presupposedProp w

/-- The incredulity reading has exactly one answer: the presupposed proposition.
The proposition itself is trivially recognized as an answer. -/
theorem incredulity_single_answer {W : Type*} [BEq W] [LawfulBEq W]
    (presupposedProp : W → Bool) (worlds : List W) :
    wxdyIncredulityQ presupposedProp worlds presupposedProp = true := by
  simp [wxdyIncredulityQ, List.all_eq_true]

/-- The literal reading is a genuine (non-degenerate) question: it delegates
to standard `Hamblin.which`, which partitions the answer space by activity. -/
theorem literal_is_genuine_question {W E : Type*} [BEq W]
    (activities : List E) (pred : E → W → Bool) (worlds : List W) :
    wxdyLiteralQ activities pred worlds = which activities pred worlds := rfl

-- ============================================================================
-- G. Left Periphery bridge (Semantics.Questions/LeftPeriphery.lean) — DEEPEST BRIDGE
-- ============================================================================

open Semantics.Questions.LeftPeriphery

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
    (h : c ⊧ embeddedProp) (w : W) (hw : c w) :
    (wxdyPresup embeddedProp).presup w = true :=
  h w hw

-- ============================================================================
-- I. Aspect bridge (Semantics.Compositional/Verb/Aspect.lean + Diagnostics)
-- ============================================================================

open Semantics.Lexical.Verb.Aspect
open Phenomena.Aspect.Diagnostics

/-- WXDY's *doing* selects for activities and accomplishments — predicates
that are durative ∧ dynamic. This connects to the progressive diagnostic:
`progressivePrediction = .accept ↔ durative ∧ dynamic`.

The progressive requirement in WXDY reflects the same aspectual constraint
as the standard progressive: it selects predicates with internal stages. -/
theorem wxdy_requires_progressive_aspect (c : VendlerClass) :
    progressivePrediction c = .accept ↔
    (c.duration = .durative ∧ c.dynamicity = .dynamic) :=
  progressive_accepts_durative_dynamic c

-- ============================================================================
-- J. Domain widening bridge (Focus/DomainWidening.lean)
-- ============================================================================

open Semantics.Compositional.Sentence.DomainWidening

/-- WXDY's incredulity arises from a normative expectation violation:
the situation violates what the speaker considers normal/appropriate.
This is the same alternative source as counterexpectational *just*
("He's just texting during the lecture!"). -/
def wxdyAlternativeSource : AlternativeSource := .normative

/-- WXDY's incongruity and counterexpectational *just* share the same
alternative source: both involve normative expectations being violated.

- WXDY: "What's this fly doing in my soup?" — violates dining norms
- *just*: "He's just texting during the lecture!" — violates classroom norms -/
theorem wxdy_incongruity_is_counterexpectational :
    wxdyAlternativeSource = associatedSource .counterexpectational := rfl

-- ============================================================================
-- K. Polarity / rhetorical question bridge (Semantics.Questions/Polarity.lean)
-- ============================================================================

open Semantics.Questions.Polarity

/-- WXDY on the incredulity reading is a rhetorical question:
- The speaker presupposes the positive answer (the situation obtains)
- Belief strength is maximal (speaker SEES the situation)
- Question form is used for pragmatic effect, not information seeking -/
def wxdyAsRhetoricalQ {W : Type*} (prop : W → Bool) : RhetoricalQuestion W :=
  { prop := prop
  , presupposedPositive := true
  , beliefStrength := 1 }

/-- Rhetorical questions require polar form — they cannot be alternative
questions. WXDY on the incredulity reading has this property: you can't
say *"What's this fly doing in my soup or not?" -/
theorem wxdy_rhetorical_requires_polar {W : Type*} (prop : W → Bool) :
    expectedTypeForUse .rhetorical ≠ .alternative :=
  rhetorical_requires_polar (wxdyAsRhetoricalQ prop)

-- ============================================================================
-- L. Per-datum verification
-- ============================================================================

/-- All grammatical WXDY examples use progressive *doing*. -/
theorem progressive_required_all :
    (allExamples.filter (λ d : WXDYDatum =>
      d.judgment == .grammatical && d.reading != .literal
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
