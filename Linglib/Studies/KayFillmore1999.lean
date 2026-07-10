import Linglib.Studies.FillmoreKayOConnor1988
import Linglib.Syntax.ConstructionGrammar.Basic
import Linglib.Semantics.Presupposition.Basic
import Linglib.Discourse.CommonGround
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Features.Aktionsart
import Linglib.Semantics.Questions.Hamblin
import Linglib.Syntax.Minimalist.LeftPeriphery
import Linglib.Syntax.ConstructionGrammar.IdiomTypology
import Linglib.Features.Aktionsart

/-!
# [kay-fillmore-1999]: *What's X Doing Y?*

"Grammatical Constructions and Linguistic Generalizations: The *What's X
doing Y?* Construction" (Language 75(1):1–33). WXDY has interrogative
*form* but expressive *function* on the incredulity reading; the
form–function mismatch is derived rather than stipulated: the literal
reading is a genuine question (speaker-ignorance satisfies the PerspP
presupposition), the incredulity reading a blocked one (speaker knowledge
contradicts it), with the presupposed proposition and the
unexpectedness CI typed via `PartialProp`/`TwoDimProp`.

The paper's own inheritance hierarchy — WXDY inheriting from the
left-isolation, subject–aux-inversion, and wh-interrogative constructions
of its unification-based grammar — is recorded here only as prose;
assembling it as a checked network awaits verification of the paper's
figures.

## Main declarations

- `KayFillmore1999.wxdyConstruction`: the construction, typed form per
  Figure 12
- `KayFillmore1999.allExamples`: judgment data
- `KayFillmore1999.perspP_disambiguates_wxdy`: the two readings derived
- `KayFillmore1999.wxdyPresup`, `wxdyTwoDim`: typed pragmatics
-/

namespace KayFillmore1999

open FillmoreKayOConnor1988
open Features (Acceptability)

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
  constructor; decide
  constructor; decide
  decide

/-- All judgment types are represented. -/
theorem has_all_judgment_types :
    (allExamples.any (·.judgment == .ok)) = true ∧
    (allExamples.any (·.judgment == .unacceptable)) = true ∧
    (allExamples.any (·.judgment == .marginal)) = true := by
  constructor; decide
  constructor; decide
  decide

/-! ### The construction -/

open ConstructionGrammar

/-- The WXDY construction as a `Construction`.

Form: [CP What's [TP NP doing [VP/PP...]]]
- Interrogative form: wh-fronting, subject-aux inversion, +WH
- *doing* is frozen progressive: licenses the construction
- Complement: locative PP, participial VP, or instrumental PP

The typed form is the flat projection of Figure 12's hierarchical AVM:
X and Y share refIdx 2 (coinstantiation/subject control); WXDY-*what* is
left-isolated ([loc -]) and nonreferential ([ref ∅]); *doing* cannot be
negated ([neg -]). -/
def wxdyConstruction : Construction :=
  { name := "What's X doing Y?"
  , form :=
      [ { filler := .open_ .NOUN, role := some "subject", gf := some .subj
        , refIdx := some 2 }
      , { filler := .headed "be" .AUX, isHead := true }
      , { filler := .headed "doing" .VERB, gf := some .comp
        , constraints := [.negMinus] }
      , { filler := .fixed "what", gf := some .obj
        , constraints := [.locMinus, .refEmpty] }
      , { filler := .open_ .X, role := some "predicate", gf := some .pred
        , refIdx := some 2 } ]
  , meaning := "Incredulity: speaker presupposes embedded prop, expresses surprise; Literal: genuine activity question"
  , pragmaticFunction := "presupposes situation; CI: speaker finds it unexpected/inappropriate" }

/-! ### FKO1988 idiom classification bridge -/

/-- WXDY is a formal idiom in FKO1988's typology: encoding (must learn the
incredulity convention), grammatical (fills proper grammatical slots),
formal (productive open pattern). -/
def wxdyIdiomType : ConstructionGrammar.IdiomType :=
  { interpretability := .encoding
  , grammaticality := .grammatical
  , formality := .formal }

/-- WXDY uses familiar pieces in a familiar arrangement: "what", "doing", etc.
are all standard English items in standard syntactic positions. The
non-compositional meaning (incredulity) is what must be learned. -/
def wxdyFamiliarity : ConstructionGrammar.FamiliarityPattern :=
  .familiarPiecesFamiliarlyArranged

/-- WXDY is a formal idiom: partially open, with pragmatic function. -/
theorem wxdy_is_formal_idiom :
    wxdyIdiomType.formality = .formal ∧
    wxdyConstruction.specificity = .partiallyOpen ∧
    wxdyConstruction.pragmaticFunction.isSome := ⟨rfl, rfl, rfl⟩

/-! ### Presupposition bridge (Core/Presupposition.lean) -/

open Semantics.Presupposition

/-- On the incredulity reading, WXDY presupposes the embedded proposition
(the situation that the speaker finds surprising) and has trivial assertion.

"What's this fly doing in my soup?" presupposes: there is a fly in the soup.
The at-issue assertion is trivial — the point is to express the CI. -/
def wxdyPresup {W : Type*} (embeddedProp : W → Prop) : PartialProp W where
  presup := embeddedProp
  assertion _ := True

/-- Presupposition projects through negation: "It's not the case that
[what's this fly doing in my soup]" still presupposes the fly is there. -/
theorem wxdy_presup_projects_neg {W : Type*} (embeddedProp : W → Prop) :
    ∀ w, (PartialProp.neg (wxdyPresup embeddedProp)).presup w ↔
         embeddedProp w := fun _ => Iff.rfl

/-! ### Two-dimensional semantics bridge (Expressives/Basic.lean) -/

open Pragmatics.Expressives

/-- WXDY on the incredulity reading has two-dimensional meaning:
- At-issue: the embedded proposition (there's a fly in my soup)
- CI: speaker finds this unexpected/inappropriate

This mirrors [potts-2005]'s analysis of expressives: the expressive
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
  , repeatable := false }

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

/-! ### Hamblin question semantics bridge (Semantics/Questions/Hamblin.lean substrate) -/

open Question

/-- Literal reading: standard wh-question "which activity is X engaged in?"
Delegates to substrate `Question.which` over a domain of activities. -/
def wxdyLiteralQ {W E : Type*}
    (activities : Set E) (pred : E → Set W) : Question W :=
  which activities pred

/-- Incredulity reading: degenerate question with only the presupposed
proposition as an answer. The "question" is not information-seeking;
the speaker already knows the answer.

In the substrate, this is the declarative principal ideal of the
presupposed proposition — a single-alternative question. -/
def wxdyIncredulityQ {W : Type*} (presupposedProp : Set W) : Question W :=
  declarative presupposedProp

/-- The incredulity reading has exactly one alternative: the presupposed
proposition. The proposition itself is the unique alternative. -/
theorem incredulity_single_answer {W : Type*}
    (presupposedProp : Set W) :
    alt (wxdyIncredulityQ presupposedProp) = {presupposedProp} :=
  alt_declarative presupposedProp

/-- The literal reading is a genuine (non-degenerate) question: it delegates
to substrate `Question.which`, which yields a Hamblin-style alternative
set indexed by the activity domain. -/
theorem literal_is_genuine_question {W E : Type*}
    (activities : Set E) (pred : E → Set W) :
    wxdyLiteralQ activities pred = which activities pred := rfl

/-! ### Left Periphery bridge (ArgumentStructure.Linking/LeftPeriphery.lean) — DEEPEST BRIDGE -/

open Minimalist.LeftPeriphery

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

/-! ### Common ground bridge (Core/CommonGround.lean) -/

open CommonGround

/-- The WXDY presupposition must be entailed by the common ground.
For "What's this fly doing in my soup?", the CommonGround must already entail
that there is a fly in the soup (the speaker sees it). -/
theorem wxdy_presup_requires_cg {W : Type*}
    (c : ContextSet W) (embeddedProp : W → Prop)
    (h : ContextSet.entails c (wxdyPresup embeddedProp).presup) (w : W) (hw : c w) :
    (wxdyPresup embeddedProp).presup w :=
  h hw

/-! ### Aspect bridge (Semantics.Montague/Verb/Aspect.lean + Diagnostics) -/

open Features
open ArgumentStructure
open Features

/-- WXDY's *doing* selects for activities and accomplishments — predicates
that are durative ∧ dynamic. This connects to the progressive diagnostic:
`progressivePrediction =.accept ↔ durative ∧ dynamic`.

The progressive requirement in WXDY reflects the same aspectual constraint
as the standard progressive: it selects predicates with internal stages. -/
theorem wxdy_requires_progressive_aspect (c : VendlerClass) :
    progressivePrediction c = .accept ↔
    (c.duration = .durative ∧ c.dynamicity = .dynamic) :=
  progressive_accepts_durative_dynamic c

end KayFillmore1999
