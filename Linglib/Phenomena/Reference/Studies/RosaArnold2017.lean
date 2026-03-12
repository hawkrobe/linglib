import Linglib.Theories.Semantics.Events.ThetaRole
import Linglib.Core.Discourse.CoherenceRelation
import Linglib.Core.Discourse.ReferentialForm
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.WordOrder.Studies.ArnoldEtAl2000
import Linglib.Phenomena.Reference.Studies.KehlerRohde2013

/-!
# @cite{rosa-arnold-2017}
@cite{kehler-rohde-2013} @cite{kehler-2002} @cite{arnold-wasow-losongco-ginstrom-2000}

Predictability Affects Production: Thematic Roles Can Affect Reference Form
Selection. *Journal of Memory and Language* 94, 43–60.

## Core Argument

Speakers use more pronouns for **goals** than **sources** of transfer verbs,
across three experimental paradigms (event-retelling, sentence completion × 2).
A rating study confirms that goal characters are more predictable next-mentions
(71% chose the goal as likely next-mention; separately, only 54% chose the
subject, suggesting subjecthood is a weaker predictor of next-mention than
thematic role). This establishes that **thematic roles affect referential form
selection via predictability**, contrary to claims that thematic roles do not
affect form.

## Key Findings

| # | Finding | Status |
|---|---------|--------|
| 1 | Goals get more pronouns than sources (all 3 exps) | data |
| 2 | Subjects get more pronouns than nonsubjects (all 3 exps) | data |
| 3 | Goals are more predictable next-mentions (71% vs 54%) | data |
| 4 | Occasion/Result coherence amplifies goal bias (Exp 2) | data |
| 5 | Goal bias robust across paradigms | data |
| 6 | Transfer verbs assign Goal to indirect object | `rfl` |
| 7 | Occasion/Result is contiguity/causeEffect | `rfl` |
| 8 | Goal > Source mirrors IC next-mention mechanism | cross-study |
| 9 | Form reduction feeds into ordering (Arnold et al. 2000) | cross-study |

## Debate with @cite{kehler-rohde-2013}

Kehler & Rohde decompose pronoun interpretation via Bayes' rule:

  P(referent | pronoun) ∝ P(pronoun | referent) × P(referent)

They propose two independent factors:
- **P(referent)**: coherence-driven next-mention bias (sensitive to thematic roles)
- **P(pronoun | referent)**: centering-driven form bias (sensitive to subjecthood ONLY)

This predicts thematic roles should NOT affect pronominalization rate.
@cite{rosa-arnold-2017} directly challenges this independence: goals get
more pronouns than sources even controlling for grammatical role, showing
P(pronoun | referent) is also sensitive to thematic role predictability.

## Connection to @cite{arnold-wasow-losongco-ginstrom-2000}

The same verb ("give"), the same construction (dative/transfer), but different
dependent variables: Arnold et al. (2000) study **position** (heavy NP shift,
dative alternation), Rosa & Arnold (2017) study **form** (pronoun vs name).
Both are production choices along the same NP weight/reduction dimension.
-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.RosaArnold2017

open Core.Discourse.CoherenceRelation
open Core.Discourse.ReferentialForm
open Core.Prominence

-- ════════════════════════════════════════════════════
-- § 1. Experimental Design
-- ════════════════════════════════════════════════════

/-- Thematic role of the referent in a transfer verb event. -/
inductive TransferRole where
  | goal    -- recipient/endpoint of transfer (e.g., "Lisa gave the pie to *Brendan*")
  | source  -- origin/source of transfer (e.g., "*Lisa* gave the pie to Brendan")
  deriving DecidableEq, Repr, BEq

/-- Grammatical role of the referent in the prior sentence. -/
inductive GramRole where
  | subject      -- grammatical subject of the prior sentence
  | nonsubject   -- nonsubject (object of PP, indirect object)
  deriving DecidableEq, Repr, BEq

/-- Gender match between referents (affects ambiguity of pronouns). -/
inductive GenderContext where
  | sameGender       -- both characters same gender (pronoun ambiguous)
  | differentGender  -- different gender (pronoun unambiguous)
  deriving DecidableEq, Repr, BEq

/-- Experimental paradigm. -/
inductive Paradigm where
  | eventRetelling        -- Exp 1: in-person picture description
  | sentenceCompletion    -- Exp 2: written story continuation
  | renamedCompletion     -- Exp 3: disconnected items (no repeated characters)
  deriving DecidableEq, Repr, BEq

/-- Experimental condition: fully crossed design. -/
structure Condition where
  role : TransferRole
  gram : GramRole
  gender : GenderContext
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Empirical Data — Pronoun Rates (%)
-- ════════════════════════════════════════════════════

/-- Pronoun rate data point: percentage of pronoun use in a condition. -/
structure PronounRate where
  paradigm : Paradigm
  cond : Condition
  percent : Nat  -- integer percentage
  deriving Repr

-- Exp 1: Event retelling (Table 1)
def exp1_goal_subj_diff : PronounRate :=
  ⟨.eventRetelling, ⟨.goal, .subject, .differentGender⟩, 64⟩
def exp1_source_subj_diff : PronounRate :=
  ⟨.eventRetelling, ⟨.source, .subject, .differentGender⟩, 37⟩
def exp1_goal_nonsub_diff : PronounRate :=
  ⟨.eventRetelling, ⟨.goal, .nonsubject, .differentGender⟩, 31⟩
def exp1_source_nonsub_diff : PronounRate :=
  ⟨.eventRetelling, ⟨.source, .nonsubject, .differentGender⟩, 18⟩

-- Exp 2: Sentence completion (Table 4)
def exp2_goal_subj_diff : PronounRate :=
  ⟨.sentenceCompletion, ⟨.goal, .subject, .differentGender⟩, 83⟩
def exp2_source_subj_diff : PronounRate :=
  ⟨.sentenceCompletion, ⟨.source, .subject, .differentGender⟩, 78⟩
def exp2_goal_nonsub_diff : PronounRate :=
  ⟨.sentenceCompletion, ⟨.goal, .nonsubject, .differentGender⟩, 55⟩
def exp2_source_nonsub_diff : PronounRate :=
  ⟨.sentenceCompletion, ⟨.source, .nonsubject, .differentGender⟩, 33⟩

-- Exp 3: Renamed sentence completion (Table 7)
-- Items disconnected: no repeated characters across items.
-- Thematic role effect was strongest in nonsubject + same-gender condition.
def exp3_goal_subj_diff : PronounRate :=
  ⟨.renamedCompletion, ⟨.goal, .subject, .differentGender⟩, 71⟩
def exp3_source_subj_diff : PronounRate :=
  ⟨.renamedCompletion, ⟨.source, .subject, .differentGender⟩, 71⟩
def exp3_goal_nonsub_diff : PronounRate :=
  ⟨.renamedCompletion, ⟨.goal, .nonsubject, .differentGender⟩, 38⟩
def exp3_source_nonsub_diff : PronounRate :=
  ⟨.renamedCompletion, ⟨.source, .nonsubject, .differentGender⟩, 33⟩
def exp3_goal_nonsub_same : PronounRate :=
  ⟨.renamedCompletion, ⟨.goal, .nonsubject, .sameGender⟩, 33⟩
def exp3_source_nonsub_same : PronounRate :=
  ⟨.renamedCompletion, ⟨.source, .nonsubject, .sameGender⟩, 10⟩

-- ════════════════════════════════════════════════════
-- § 3. Rating Study — Next-Mention Bias
-- ════════════════════════════════════════════════════

/-- Next-mention rating: percentage of participants choosing this role
    as the character most likely to be talked about next. -/
structure NextMentionRating where
  role : TransferRole
  percent : Nat
  deriving Repr

/-- 71% of raters chose the goal character as most likely to be mentioned next
    (t(19)=4.91, p<.0001). -/
def nextMention_goal : NextMentionRating := ⟨.goal, 71⟩

/-- 54% of raters chose the subject (not significant, p>.1). -/
def nextMention_subject_pct : Nat := 54

/-- Goals are more predictable next-mentions than sources. -/
theorem goals_more_predictable :
    nextMention_goal.percent > (100 - nextMention_goal.percent) := by
  native_decide

/-- Thematic role (goal: 71%) is a stronger next-mention predictor than
    grammatical role (subject: 54%). This supports the paper's core claim
    that predictability driven by thematic roles matters for production. -/
theorem goal_bias_stronger_than_subj_bias :
    nextMention_goal.percent > nextMention_subject_pct := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. Key Contrasts
-- ════════════════════════════════════════════════════

/-- Goal > Source in pronoun rate: verified in every paradigm.
    Exp 1: 64 vs 37 (subject, different-gender).
    Exp 2: 55 vs 33 (nonsubject, different-gender).
    Exp 3: 33 vs 10 (nonsubject, same-gender — strongest interaction cell). -/
theorem exp1_goal_gt_source_subj :
    exp1_goal_subj_diff.percent > exp1_source_subj_diff.percent := by
  native_decide

theorem exp2_goal_gt_source_nonsub :
    exp2_goal_nonsub_diff.percent > exp2_source_nonsub_diff.percent := by
  native_decide

/-- Exp 3 strongest cell: nonsubject same-gender shows 33% vs 10%. -/
theorem exp3_goal_gt_source_nonsub_same :
    exp3_goal_nonsub_same.percent > exp3_source_nonsub_same.percent := by
  native_decide

/-- Subject > Nonsubject in pronoun rate (orthogonal to thematic role).
    Exp 1: 64 vs 31 for goals. -/
theorem exp1_subj_gt_nonsub :
    exp1_goal_subj_diff.percent > exp1_goal_nonsub_diff.percent := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 5. Coherence Relation Interaction (Exp 2)
-- ════════════════════════════════════════════════════

/-- Coherence relation categories used in Exp 2 coding. -/
inductive CoherenceCategory where
  | occasionResult   -- Occasion or Result continuations (goal-biased)
  | other            -- Elaboration, Explanation, etc. (source-biased or neutral)
  deriving DecidableEq, Repr, BEq

/-- Exp 2 coherence interaction: Goal vs Source effect by coherence category.
    Occasion/Result: β=1.22 (0.40), t=3.06, p=.002 — significant.
    Other: β=0.86 (0.55), t=1.56, p=.12 — not significant. -/
structure CoherenceInteraction where
  category : CoherenceCategory
  goalSourceBeta : Int   -- β estimate × 100 (avoid rationals for simplicity)
  significant : Bool
  deriving Repr

def occasionResult_interaction : CoherenceInteraction :=
  ⟨.occasionResult, 122, true⟩

def other_interaction : CoherenceInteraction :=
  ⟨.other, 86, false⟩

/-- The goal bias is larger for Occasion/Result than Other coherence. -/
theorem coherence_amplifies_goal_bias :
    occasionResult_interaction.goalSourceBeta >
    other_interaction.goalSourceBeta := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 6. Kehler & Rohde Two-Component Model
-- ════════════════════════════════════════════════════

/-- @cite{kehler-rohde-2013}'s independence hypothesis:
    P(pronoun | referent) depends only on grammatical/topichood status,
    NOT on thematic role or coherence-driven predictability.

    This predicts that pronominalization rate should be constant across
    thematic roles when grammatical role is held constant. -/
def kehlerRohdeIndependence
    (pronounGivenReferent : TransferRole → GramRole → Nat)
    (gram : GramRole) : Prop :=
  pronounGivenReferent .goal gram = pronounGivenReferent .source gram

/-- @cite{rosa-arnold-2017}'s challenge: goals get more pronouns than
    sources even in the same grammatical position. This violates the
    independence hypothesis. Verified in Exp 1 subject condition. -/
theorem independence_violated_exp1_subj :
    ¬ kehlerRohdeIndependence
      (fun role gram => match role, gram with
        | .goal, .subject => 64 | .source, .subject => 37
        | .goal, .nonsubject => 31 | .source, .nonsubject => 18)
      .subject := by
  simp [kehlerRohdeIndependence]

-- ════════════════════════════════════════════════════
-- § 7. Fragment Bridge — Transfer Verb Theta Structure
-- ════════════════════════════════════════════════════

/-- Transfer verb next-mention prediction: Goal arguments have higher
    next-mention bias than Source arguments in narrative (Occasion/Result)
    continuations. This maps the ThetaRole distinction to NextMentionBias. -/
def transferNextMention : ThetaRole → NextMentionBias
  | .goal   => .high
  | .source => .low
  | _       => .low   -- other roles: no transfer-specific prediction

/-- Goal → pronoun, Source → name: the predicted referential form for
    transfer verb arguments follows from next-mention bias. -/
theorem goal_predicts_pronoun :
    (transferNextMention .goal).predictedForm = .personalPronoun := rfl

theorem source_predicts_name :
    (transferNextMention .source).predictedForm = .properName := rfl

-- ════════════════════════════════════════════════════
-- § 8. Coherence Bridge
-- ════════════════════════════════════════════════════

/-- Occasion relations focus on the end state of the previous event.
    For transfer verbs, the Goal is the endpoint — the entity in the
    final state after transfer. This is why Occasion/Result coherence
    amplifies the Goal bias.

    Occasion is a contiguity relation; Result is cause–effect.
    Both focus on what happens AFTER the event, favoring the Goal. -/
theorem occasion_is_contiguity :
    CoherenceRelation.occasion.toClass = .contiguity := rfl

theorem result_is_cause_effect :
    CoherenceRelation.result.toClass = .causeEffect := rfl

-- ════════════════════════════════════════════════════
-- § 9. Production–Ordering Bridge
-- ════════════════════════════════════════════════════

/-- The same transfer verb "give" is studied for both referential form
    (@cite{rosa-arnold-2017}) and constituent ordering
    (@cite{arnold-wasow-losongco-ginstrom-2000}). Pronouns are more
    reduced than names on the accessibility scale, and at most as heavy
    by word count. The referential form choice connects to ordering:

    Rosa & Arnold: Goal → pronoun (reduced)
    Arnold et al. 2000: light/reduced NP → early position

    Together: Goal → pronoun → early position. The referential form
    choice mediates between thematic role and syntactic position. -/
theorem pronoun_more_reduced :
    DefinitenessLevel.personalPronoun.rank >
    DefinitenessLevel.properName.rank := by
  native_decide

theorem pronoun_at_most_as_heavy :
    ReferentialForm.typicalWeight .personalPronoun ≤
    ReferentialForm.typicalWeight .properName := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 10. Cross-Study Bridge: @cite{arnold-wasow-losongco-ginstrom-2000}
-- ════════════════════════════════════════════════════

open Phenomena.WordOrder.Studies.ArnoldEtAl2000

/-- The goal argument receives a MORE REDUCED referential form than the
    source argument. This derived contrast — not the individual predictions —
    is the empirical content of @cite{rosa-arnold-2017}.

    The same reduction asymmetry creates a weight asymmetry: goal arguments
    surface as lighter NPs (pronouns) while source arguments surface as
    heavier NPs (names). @cite{arnold-wasow-losongco-ginstrom-2000} prove
    that exactly this weight dimension independently predicts constituent
    ordering in dative constructions with the same verb. So thematic roles
    affect ordering *through* referential form reduction. -/
theorem goal_more_reduced_than_source :
    (transferNextMention .goal).predictedForm.rank >
    (transferNextMention .source).predictedForm.rank := by
  native_decide

/-- @cite{arnold-wasow-losongco-ginstrom-2000} show that heaviness and
    newness BOTH independently predict ordering. @cite{rosa-arnold-2017}
    show thematic roles affect BOTH form (the heaviness dimension) and
    predictability (the newness dimension). Thematic roles therefore have
    a **dual path** to constituent ordering:

    Path 1 (via form): θ-role → form reduction → lighter NP → earlier
    Path 2 (via predictability): θ-role → next-mention bias → given-like → earlier

    This theorem derives the existence of both paths: the goal/source
    contrast produces different predicted forms (Path 1 input), and
    goals are more predictable than sources (Path 2 input). Arnold et al.
    confirm that both receiving dimensions independently matter. -/
theorem dual_path_to_ordering :
    -- Path 1: thematic role creates a form contrast (Rosa & Arnold)
    (transferNextMention .goal).predictedForm ≠
    (transferNextMention .source).predictedForm ∧
    -- Path 2: thematic role creates a predictability contrast (Rosa & Arnold)
    nextMention_goal.percent > (100 - nextMention_goal.percent) ∧
    -- Both receiving dimensions independently predict ordering (Arnold et al.)
    daCorpusResult.heavinessSig ∧ daCorpusResult.newnessSig := by
  refine ⟨by decide, by native_decide, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. Cross-Study Bridge: @cite{kehler-rohde-2013}
-- ════════════════════════════════════════════════════

open Phenomena.Reference.Studies.KehlerRohde2013

/-- @cite{kehler-rohde-2013}'s Bayesian decomposition predicts that
    P(pronoun | referent) depends only on topichood, not on semantic
    factors like thematic role. This study directly violates that
    prediction: goals get more pronouns than sources in the same
    grammatical position (Exp 1: 64% vs 37% for subjects).

    The violation connects to K&R's Table 9 data, which shows that
    P(pronoun | referent) DOES vary with topichood (passive subject
    87% vs active subject 62%). Rosa & Arnold extend this: thematic
    roles also contribute to topichood/predictability, not just
    syntactic construction. -/
theorem independence_violated_bridges_to_KR :
    -- K&R: passive subjects get more pronouns than active subjects
    pron_passive_subj > pron_active_subj ∧
    -- Rosa & Arnold: goals get more pronouns than sources (same position)
    exp1_goal_subj_diff.percent > exp1_source_subj_diff.percent := by
  exact ⟨by native_decide, by native_decide⟩

/-- K&R's Table 2 shows that Occasion and Result are Goal-biased
    (18% and 8% Source respectively). This study's Exp 2 coherence
    interaction confirms: Occasion/Result continuations amplify the
    goal bias (β=1.22, p=.002), while Other coherence (including
    Explanation, which K&R show is Source-biased at 80%) does not
    reach significance (β=0.86, p=.12). The coherence-specific
    biases from K&R's passage completion data predict the interaction
    pattern in this study's sentence completion data. -/
theorem coherence_interaction_matches_KR_biases :
    -- K&R: Occasion is Goal-biased, Explanation is Source-biased
    cr_occasion.sourceGivenCR < 50 ∧
    cr_explanation.sourceGivenCR > 50 ∧
    -- Rosa & Arnold: Occasion/Result amplifies goal bias
    occasionResult_interaction.significant = true ∧
    -- Rosa & Arnold: Other (Explanation-heavy) does not
    other_interaction.significant = false := by
  exact ⟨by native_decide, by native_decide, rfl, rfl⟩

end Phenomena.Reference.Studies.RosaArnold2017
