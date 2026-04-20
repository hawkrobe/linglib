import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Phenomena.Presupposition.ProjectiveContent
import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2022
import Linglib.Fragments.German.Predicates
import Linglib.Core.Discourse.AtIssueness

/-!
# Solstad & Bott (2024): The occasion verb presupposition

@cite{solstad-bott-2024} @cite{tonhauser-beaver-roberts-simons-2013} @cite{heim-1983} @cite{schlenker-2008} @cite{schlenker-2009}

Formalizes the experimental evidence from S&P 17:11 establishing occasion
verbs as a distinct class of presupposition trigger.

## The occasion verb presupposition

**Occasion verbs** (German: *bestrafen* "punish", *kritisieren* "criticise",
*loben* "praise", *danken* "thank", ...) are interpersonal action verbs
whose agent performs an action in response to a prior eventuality involving
the object. This prior eventuality — the **occasion** — is presupposed.

Example: "The judge punished Peter"
  - At-issue: the judge performed a punishing action
  - Presupposed: Peter did something wrong (the occasion)

## Experimental evidence (3 experiments)

**Exp 1** (occasion verbs only, N=71):
- Block 1 (contextual felicity): occasion verbs are rated better in
  anaphoric (β=22.37) and cataphoric (β=17.95) than neutral contexts.
  Cataphoric resolution is unique to occasion verbs — pronouns and
  demonstratives show NO cataphoric improvement.
- Block 2 (projectivity/at-issueness): mean projectivity 0.79 (range
  0.73–0.87), mean at-issueness 0.32 (range 0.17–0.57).

**Exp 2** (occasion + SE + ES psych verbs, N=60):
- Block 2: occasion verbs (0.69 proj) separate from SE (0.54) and ES
  (0.52). k-means k=3 separates {occasion} from {psych verbs}.
  H6 (SE = occasion) REJECTED; H7 (ES ≠ occasion) CONFIRMED.

**Exp 3** (filtering, N=58):
- Occasion verbs: trigger-first and trigger-last NOT significantly
  different (β=−1.97, t=−1.05) → **symmetric** filtering.
- Mandelkern items (factives/aspectuals): trigger-first >> trigger-last
  (β=−30.16, t=−16.33) → **asymmetric** filtering.

## Tonhauser et al. (2013) classification

Occasion verbs are **Class C** (SCF=no, OLE=yes), alongside factives
(*know*) and change-of-state verbs (*stop*). However, they are
distinguished by their **bidirectional** context resolution (both
m-anaphoric and m-cataphoric) and **symmetric filtering** — they
constitute "a cage of their own" within the trigger taxonomy.
-/

namespace SolstadBott2024

open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.OntologicalPreconditions
open Phenomena.Presupposition.ProjectiveContent
open SolstadBott2022
open Fragments.German.Predicates
open Core.Presupposition
open Core.CommonGround
open Core.Discourse.AtIssueness

-- ════════════════════════════════════════════════════
-- § 1. Filtering Direction and Context Resolution
-- ════════════════════════════════════════════════════

/-- Filtering direction for presupposition triggers.
    @cite{solstad-bott-2024} Exp 3 shows occasion verbs allow symmetric
    filtering, while factives and change-of-state verbs only allow
    left-to-right filtering. -/
inductive FilteringDirection where
  | leftToRight    -- Standard asymmetric: only prior material resolves
  | symmetric      -- Both prior and subsequent material can resolve
  deriving DecidableEq, Repr

/-- Context resolution direction for presupposition triggers.
    Refines @cite{tonhauser-beaver-roberts-simons-2013}'s "m-positive"
    into finer-grained categories based on where the resolving material
    can appear. -/
inductive ContextPolarity where
  | mNeutral       -- Felicitous without any supporting context
  | mAnaphoric     -- Requires preceding material for resolution
  | mCataphoric    -- Requires subsequent material for resolution
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Occasion Verbs are Class C Triggers
-- ════════════════════════════════════════════════════

/-- Occasion verbs are Class C in the @cite{tonhauser-beaver-roberts-simons-2013} taxonomy:
    SCF=no (can be informative), OLE=yes (attributed to attitude holder). -/
theorem occasion_verb_is_classC :
    ProjectiveTrigger.occasion_verb.toClass = .classC := rfl

/-- Class C triggers do not require prior establishment in context. -/
theorem classC_no_scf :
    ProjectiveClass.classC.scf = .noRequires := rfl

/-- Class C triggers have obligatory local effect under belief embedding. -/
theorem classC_has_ole :
    ProjectiveClass.classC.ole = .obligatory := rfl

/-- Occasion verbs pattern with *stop* and *know* — all Class C. -/
theorem occasion_verb_patterns_with_stop_know :
    ProjectiveTrigger.occasion_verb.toClass =
    ProjectiveTrigger.stop_prestate.toClass ∧
    ProjectiveTrigger.occasion_verb.toClass =
    ProjectiveTrigger.know_complement.toClass := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. German Occasion Verb Inventory
-- ════════════════════════════════════════════════════

/-- The 16 German occasion verbs tested in @cite{solstad-bott-2024},
    derived from Fragment entries with `.occasion` sense tag. -/
def occasionVerbEntries : List GermanVerbEntry :=
  [bestrafen, belohnen, loben, kritisieren, danken,
   verklagen, gratulieren, zurechtweisen,
   anzeigen, auszeichnen, belangen, ehren, entlassen,
   raechen, revanchieren, zurVerantwortungZiehen]

/-- 16 occasion verbs were tested. -/
theorem occasion_verb_count : occasionVerbEntries.length = 16 := by native_decide

/-- All entries in the occasion verb list use the `.occasion` sense tag. -/
theorem all_occasion_entries_tagged :
    occasionVerbEntries.all (·.senseTag == .occasion) = true := by native_decide

/-- All entries in the occasion verb list are soft presupposition triggers. -/
theorem all_occasion_entries_soft_trigger :
    occasionVerbEntries.all (·.presupType == some .softTrigger) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Exp 1: Contextual Felicity and Projectivity (N=71)
-- ════════════════════════════════════════════════════

/-- Exp 1 Block 1 regression estimates (Table 1 of @cite{solstad-bott-2024}).
    Intercept = occasion verb in neutral context.
    Other coefficients are treatment contrasts.
    N=71 participants (16 occasion verbs × 3 context conditions). -/
structure Exp1Regression where
  /-- Intercept: occasion verb, neutral context (0–100 scale) -/
  intercept : ℚ
  /-- Neutral → anaphoric improvement (occasion verbs) -/
  neutral_to_anaphoric : ℚ
  /-- Neutral → cataphoric improvement (occasion verbs) -/
  neutral_to_cataphoric : ℚ
  deriving Repr

/-- Exp 1, Table 1 fixed effects. -/
def exp1_regression : Exp1Regression where
  intercept := 5081/100            -- 50.81
  neutral_to_anaphoric := 2237/100 -- 22.37
  neutral_to_cataphoric := 1795/100 -- 17.95

/-- Occasion verbs improve in both anaphoric AND cataphoric contexts.
    This bidirectional improvement is unique to occasion verbs — pronouns
    and demonstratives show no cataphoric improvement. -/
theorem occasion_verb_bidirectional_resolution :
    exp1_regression.neutral_to_anaphoric > 0 ∧
    exp1_regression.neutral_to_cataphoric > 0 := by
  refine ⟨?_, ?_⟩ <;> norm_num [exp1_regression]

/-- The cataphoric improvement is substantial (>10 points on 0–100 scale),
    not a marginal effect. -/
theorem cataphoric_resolution_substantial :
    exp1_regression.neutral_to_cataphoric > 10 := by
  norm_num [exp1_regression]

/-- Exp 1 Block 2: projectivity and at-issueness ratings (0–1 scale).
    Gradient measures following @cite{tonhauser-beaver-degen-2018}. -/
structure ProjectivityDatum where
  projectivity : ℚ   -- Mean projectivity (0–1)
  atIssueness : ℚ    -- Mean at-issueness (0–1)
  projLow : ℚ        -- Projectivity range low
  projHigh : ℚ       -- Projectivity range high
  deriving Repr

/-- Occasion verb projectivity/at-issueness from Exp 1 Block 2. -/
def exp1_occasion_proj : ProjectivityDatum where
  projectivity := 79/100   -- 0.79
  atIssueness := 32/100    -- 0.32
  projLow := 73/100        -- 0.73
  projHigh := 87/100       -- 0.87

/-- Occasion verbs have high projectivity (≥ 0.70). -/
theorem exp1_high_projectivity :
    exp1_occasion_proj.projectivity ≥ 70/100 := by
  norm_num [exp1_occasion_proj]

/-- Occasion verb content is not at-issue (at-issueness < 0.50). -/
theorem exp1_not_at_issue :
    exp1_occasion_proj.atIssueness < 50/100 := by
  norm_num [exp1_occasion_proj]

-- ════════════════════════════════════════════════════
-- § 5. Exp 2: Psych Verbs Do Not Cluster with Occasion Verbs (N=60)
-- ════════════════════════════════════════════════════

/-- Exp 2 verb classes correspond to @cite{solstad-bott-2022} verb classes.
    Occasion verbs = agent-evocator, SE = stimulus-experiencer, ES = experiencer-stimulus. -/
def exp2VerbClasses : List VerbClass := [.agentEvocator, .stimExp, .expStim]

/-- Exp 2 Block 2: projectivity by verb class.
    N=60 participants. 16 occasion verbs, 9 SE verbs, 9 ES verbs.
    The key finding: psych verbs have LOWER projectivity than occasion
    verbs, and k-means k=3 clustering separates them. -/
structure Exp2ProjectivityDatum where
  verbClass : VerbClass
  projectivity : ℚ   -- Mean projectivity (0–1)
  atIssueness : ℚ    -- Mean at-issueness (0–1)
  deriving Repr

def exp2_occasion_proj : Exp2ProjectivityDatum := ⟨.agentEvocator, 69/100, 35/100⟩
def exp2_stimExp_proj  : Exp2ProjectivityDatum := ⟨.stimExp, 54/100, 52/100⟩
def exp2_expStim_proj  : Exp2ProjectivityDatum := ⟨.expStim, 52/100, 46/100⟩

/-- H6 REJECTED: If the occasion implication were shared by all IC verbs,
    we would expect SE verbs to pattern with occasion verbs. They do not:
    occasion verbs (0.69) >> SE verbs (0.54). -/
theorem h6_rejected_se_not_occasion :
    exp2_occasion_proj.projectivity > exp2_stimExp_proj.projectivity := by
  norm_num [exp2_occasion_proj, exp2_stimExp_proj]

/-- H7 CONFIRMED: ES verbs do not cluster with occasion verbs either.
    Occasion verbs (0.69) >> ES verbs (0.52). -/
theorem h7_confirmed_es_not_occasion :
    exp2_occasion_proj.projectivity > exp2_expStim_proj.projectivity := by
  norm_num [exp2_occasion_proj, exp2_expStim_proj]

/-- SE and ES psych verbs cluster together rather than with occasion verbs:
    the gap between occasion and SE (0.15) >> gap between SE and ES (0.02). -/
theorem psych_verbs_cluster_together :
    exp2_occasion_proj.projectivity - exp2_stimExp_proj.projectivity >
    exp2_stimExp_proj.projectivity - exp2_expStim_proj.projectivity := by
  norm_num [exp2_occasion_proj, exp2_stimExp_proj, exp2_expStim_proj]

-- ════════════════════════════════════════════════════
-- § 6. Exp 3: Symmetric vs Asymmetric Filtering (Table 3, N=58)
-- ════════════════════════════════════════════════════

/-- Trigger position conditions in Exp 3 (filtering experiment).
    Items are conjunctions in the antecedent of a conditional. -/
inductive TriggerPosition where
  | triggerFirst  -- Trigger in first conjunct, resolver in second
  | triggerLast   -- Trigger in second conjunct, resolver in first
  | triggerOnly   -- Trigger alone (no resolver; baseline)
  deriving DecidableEq, Repr

/-- Trigger class conditions in Exp 3. Separate regression analyses
    were run for each class. -/
inductive Exp3TriggerClass where
  | occasionVerb  -- Analysis B: 16 German occasion verbs (24 items)
  | mandelkern    -- Analysis C: factives + aspectuals (4 Mandelkern et al. items)
  deriving DecidableEq, Repr

/-- Exp 3 regression results from Table 3 of @cite{solstad-bott-2024}.
    N=58 (75 recruited, 17 excluded). Fixed-effect estimates from
    mixed-effects regression; reference level is trigger-first. -/
structure Exp3RegressionDatum where
  triggerClass : Exp3TriggerClass
  /-- Intercept (trigger-first condition, the reference level) -/
  intercept : ℚ
  /-- Contrast: trigger-only minus trigger-first -/
  trigOnly_vs_trigFirst : ℚ
  /-- Contrast: trigger-last minus trigger-first (KEY test for symmetry) -/
  trigLast_vs_trigFirst : ℚ
  /-- t-value for the trigger-last vs trigger-first contrast -/
  tValue : ℚ
  deriving Repr

/-- Analysis B: occasion verb filtering. Trigger-first ≈ trigger-last. -/
def exp3_occasion : Exp3RegressionDatum where
  triggerClass := .occasionVerb
  intercept := 4621/100         -- 46.21
  trigOnly_vs_trigFirst := 2372/100  -- 23.72
  trigLast_vs_trigFirst := -197/100  -- -1.97
  tValue := -105/100            -- -1.05

/-- Analysis C: Mandelkern items (factives/aspectuals).
    Trigger-first << trigger-last. -/
def exp3_mandelkern : Exp3RegressionDatum where
  triggerClass := .mandelkern
  intercept := 8185/100         -- 81.85
  trigOnly_vs_trigFirst := 353/100   -- 3.53
  trigLast_vs_trigFirst := -3016/100 -- -30.16
  tValue := -1633/100           -- -16.33

/-- SYMMETRIC FILTERING for occasion verbs: trigger-first ≈ trigger-last.
    The estimate (−1.97) is small and not statistically significant
    (|t| = 1.05 < 2). Occasion verbs filter equally well regardless of
    whether the resolver precedes or follows the trigger. -/
theorem exp3_occasion_symmetric :
    exp3_occasion.trigLast_vs_trigFirst > -5 ∧
    exp3_occasion.trigLast_vs_trigFirst < 5 ∧
    exp3_occasion.tValue > -2 ∧
    exp3_occasion.tValue < 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [exp3_occasion]

/-- ASYMMETRIC FILTERING for Mandelkern items (factives/aspectuals):
    trigger-first << trigger-last. The estimate (−30.16) is large and
    highly significant (|t| = 16.33 >> 2). These triggers filter much
    better when the resolver precedes the trigger (left-to-right only). -/
theorem exp3_mandelkern_asymmetric :
    exp3_mandelkern.trigLast_vs_trigFirst < -20 ∧
    exp3_mandelkern.tValue < -10 := by
  refine ⟨?_, ?_⟩ <;> norm_num [exp3_mandelkern]

/-- The filtering asymmetry distinguishes occasion verbs from factives/
    aspectuals — the Mandelkern effect is >10× larger. -/
theorem filtering_distinguishes_trigger_classes :
    exp3_mandelkern.trigLast_vs_trigFirst <
    10 * exp3_occasion.trigLast_vs_trigFirst := by
  norm_num [exp3_mandelkern, exp3_occasion]

/-- H8 (interaction hypothesis): occasion verbs pattern with factives/
    aspectuals for left-to-right filtering (both show the trigger-only
    vs trigger-last contrast), but differ qualitatively for right-to-left
    filtering (trigger-first condition). Occasion verbs: trigger-first ≈
    trigger-last. Factives/aspectuals: trigger-first >> trigger-last. -/
theorem h8_interaction :
    -- Both trigger classes show reduced projectivity in trigger-last
    -- vs trigger-only (left-to-right filtering available for both)
    exp3_occasion.trigOnly_vs_trigFirst > 10 ∧
    exp3_mandelkern.trigOnly_vs_trigFirst > 0 ∧
    -- But they diverge on trigger-last vs trigger-first:
    -- occasion verbs ≈ 0 (symmetric), Mandelkern << 0 (asymmetric)
    exp3_occasion.trigLast_vs_trigFirst > -5 ∧
    exp3_mandelkern.trigLast_vs_trigFirst < -20 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [exp3_occasion, exp3_mandelkern]

-- ════════════════════════════════════════════════════
-- § 7. "A Cage of Their Own"
-- ════════════════════════════════════════════════════

/-- Profile characterizing a presupposition trigger's behavior across the
    dimensions tested by @cite{solstad-bott-2024}. Uses types from the
    library's projective content taxonomy and the filtering/polarity
    types defined in this file. -/
structure TriggerProfile where
  projectiveClass : ProjectiveClass
  contextPolarities : List ContextPolarity
  filteringDirection : FilteringDirection
  deriving DecidableEq, Repr

/-- Occasion verb trigger profile: Class C, bidirectional resolution,
    symmetric filtering. -/
def occasionVerbProfile : TriggerProfile where
  projectiveClass := .classC
  contextPolarities := [.mAnaphoric, .mCataphoric]
  filteringDirection := .symmetric

/-- Factive/aspectual trigger profile: Class C, no SCF constraint
    (neutral ≈ anaphoric in Exp 1 data), left-to-right filtering. -/
def factiveProfile : TriggerProfile where
  projectiveClass := .classC
  contextPolarities := []  -- No SCF: factives don't require prior context
  filteringDirection := .leftToRight

/-- Occasion verbs share Class C with factives. -/
theorem same_projective_class :
    occasionVerbProfile.projectiveClass = factiveProfile.projectiveClass := rfl

/-- Despite sharing Class C, occasion verbs differ from factives in both
    context resolution and filtering — the "cage of their own" result. -/
theorem cage_of_their_own :
    occasionVerbProfile ≠ factiveProfile := by decide

/-- The distinguishing features are filtering direction and bidirectionality,
    not the projective class assignment. -/
theorem distinguished_by_filtering_not_class :
    occasionVerbProfile.filteringDirection ≠ factiveProfile.filteringDirection ∧
    occasionVerbProfile.contextPolarities ≠ factiveProfile.contextPolarities := by
  decide

-- ════════════════════════════════════════════════════
-- § 8. Occasion Verb Presupposition as EventPhase
-- ════════════════════════════════════════════════════

/-- Model an occasion verb's presupposition as an EventPhase.

    Example: "The judge punished Peter"
    - precondition = Peter did something wrong (the occasion)
    - eventOccurs = the judge's punishing action
    - consequence = Peter is punished

    The precondition (occasion) is what projects. -/
def occasionEventPhase {W : Type*}
    (occasion : W → Prop)     -- The occasioning eventuality
    (engagement : W → Prop)   -- The agent's action
    (outcome : W → Prop)      -- Result state
    : EventPhase W where
  precondition := occasion
  eventOccurs := engagement
  consequence := outcome

/-- Occasion presupposition projects through negation.
    "The judge didn't punish Peter" still presupposes Peter did something wrong. -/
theorem occasion_presup_projects {W : Type*}
    (occasion engagement outcome : W → Prop) :
    (affirmative (occasionEventPhase occasion engagement outcome)).presupposition =
    (negative (occasionEventPhase occasion engagement outcome)).presupposition := rfl

-- ════════════════════════════════════════════════════
-- § 9. Asymmetric Filtering (@cite{heim-1983})
-- ════════════════════════════════════════════════════

/-- Under Heim's asymmetric filtering, the local context at the antecedent
    of a conditional is just the global context — no material from the
    consequent is available. So if the occasion verb is in the antecedent,
    its presupposition PROJECTS (is not filtered).

    "If the judge punishes Peter, he was convicted."
    At "punishes" (antecedent): local context = global context.
    Presupposition "Peter did something wrong" is NOT entailed → projects. -/
theorem heim_antecedent_projects {W : Type*}
    (c : ContextSet W) (trigger _consequence : PrProp W)
    (h : ∃ w, c w ∧ ¬trigger.presup w) :
    presupProjects (initialLocalCtx c) trigger := by
  obtain ⟨w, hw_in, hpresup_false⟩ := h
  intro hfilter
  exact hpresup_false (hfilter hw_in)

-- ════════════════════════════════════════════════════
-- § 10. Symmetric Filtering (@cite{schlenker-2008}, @cite{schlenker-2009})
-- ════════════════════════════════════════════════════

/-- Under symmetric filtering, material from the consequent IS available
    to resolve presuppositions in the antecedent. We model this by
    providing the consequent's assertion to the local context at the
    antecedent position.

    "If the judge punishes Peter, he was convicted."
    Symmetric local context at "punishes": c + [Peter was convicted].
    Presupposition "Peter did something wrong" IS entailed → filtered. -/
def symmetricLocalCtxAntecedent {W : Type*}
    (c : LocalCtx W) (consequent : PrProp W) : LocalCtx W :=
  { worlds := ContextSet.update c.worlds consequent.assertion
  , position := c.position
  , depth := c.depth }

/-- When the consequent entails the occasion presupposition,
    symmetric filtering predicts the presupposition is filtered. -/
theorem symmetric_filters_when_consequent_entails {W : Type*}
    (c : LocalCtx W) (trigger consequent : PrProp W)
    (h : ∀ w, c.worlds w → consequent.assertion w → trigger.presup w) :
    presupFiltered (symmetricLocalCtxAntecedent c consequent) trigger := by
  intro w hw
  have ⟨hw_in, hcons⟩ := hw
  exact h w hw_in hcons

-- ════════════════════════════════════════════════════
-- § 11. Bridge to @cite{solstad-bott-2022}
-- ════════════════════════════════════════════════════

/-- Occasion verbs correspond to the agent-evocator class from
    @cite{solstad-bott-2022}. The "occasion" presupposition is the same
    underspecified eventuality that drives the NP2 IC bias: the evocator's
    prior behavior triggers the agent's interpersonal response. -/
theorem occasion_is_agent_evocator_bias :
    VerbClass.agentEvocator.predictedBias = .np2 := rfl

/-- Despite sharing IC properties with psych verbs, occasion verbs have
    higher projectivity (Exp 2). The IC bias and the presupposition are
    distinct phenomena: IC bias tracks which argument is explained in
    "because" continuations, while the presupposition is a projective
    content that survives embedding under negation, questions, and modals. -/
theorem ic_and_presupposition_dissociate :
    -- Occasion verbs have NP2 IC bias (same as ExpStim psych verbs)
    VerbClass.agentEvocator.predictedBias = VerbClass.expStim.predictedBias ∧
    -- But occasion verbs have HIGHER projectivity than either psych verb class
    exp2_occasion_proj.projectivity > exp2_stimExp_proj.projectivity ∧
    exp2_occasion_proj.projectivity > exp2_expStim_proj.projectivity := by
  refine ⟨rfl, ?_, ?_⟩ <;> norm_num [exp2_occasion_proj, exp2_stimExp_proj, exp2_expStim_proj]

-- ════════════════════════════════════════════════════
-- § 12. Gradient Projection Principle Bridge
-- ════════════════════════════════════════════════════

/-- Occasion verb projectivity/at-issueness from Exp 1 as a GradientPair,
    bridging to the @cite{tonhauser-beaver-degen-2018} infrastructure. -/
def exp1_occasion_gpp : GradientPair where
  atIssueness := exp1_occasion_proj.atIssueness
  projectivity := exp1_occasion_proj.projectivity

/-- Occasion verb GradientPair from Exp 2. -/
def exp2_occasion_gpp : GradientPair where
  atIssueness := exp2_occasion_proj.atIssueness
  projectivity := exp2_occasion_proj.projectivity

/-- SE psych verb GradientPair from Exp 2. -/
def exp2_stimExp_gpp : GradientPair where
  atIssueness := exp2_stimExp_proj.atIssueness
  projectivity := exp2_stimExp_proj.projectivity

/-- ES psych verb GradientPair from Exp 2. -/
def exp2_expStim_gpp : GradientPair where
  atIssueness := exp2_expStim_proj.atIssueness
  projectivity := exp2_expStim_proj.projectivity

/-- Pearson r for the correlation between at-issueness and projectivity,
    aggregated over trigger types.

    Exp 1 (8 trigger types including occasion verbs):
      r = −0.70, t(6) = −2.37, p = .06 (marginally significant)

    Exp 2 (9 trigger types including occasion + psych verbs):
      r = −0.90, t(7) = −5.33, p < .01 (significant)

    These correspond to @cite{tonhauser-beaver-degen-2018}'s positive
    correlations between not-at-issueness and projectivity (r = .85, .99),
    since at-issueness = 1 − not-at-issueness flips the sign. -/
def exp1_gpp_r : ℚ := -70/100
def exp2_gpp_r : ℚ := -90/100

/-- The GPP anti-correlation strengthens from Exp 1 to Exp 2,
    with more trigger types included. -/
theorem exp2_gpp_stronger : exp2_gpp_r < exp1_gpp_r := by
  norm_num [exp1_gpp_r, exp2_gpp_r]

/-- Occasion verbs satisfy the GPP: high projectivity paired with
    low at-issueness in both experiments. -/
theorem occasion_verbs_satisfy_gpp :
    exp1_occasion_gpp.projectivity > 1/2 ∧
    exp1_occasion_gpp.atIssueness < 1/2 ∧
    exp2_occasion_gpp.projectivity > 1/2 ∧
    exp2_occasion_gpp.atIssueness < 1/2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [exp1_occasion_gpp, exp2_occasion_gpp,
              exp1_occasion_proj, exp2_occasion_proj]

/-- Psych verbs are mid-range on both dimensions: neither clearly
    projective nor clearly at-issue, placing them outside the GPP
    pattern that occasion verbs and other triggers follow. -/
theorem psych_verbs_midrange :
    exp2_stimExp_gpp.projectivity > 40/100 ∧
    exp2_stimExp_gpp.projectivity < 60/100 ∧
    exp2_stimExp_gpp.atIssueness > 40/100 ∧
    exp2_stimExp_gpp.atIssueness < 60/100 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [exp2_stimExp_gpp, exp2_stimExp_proj]

/-- The GPP orders occasion verbs and psych verbs correctly:
    occasion verbs have higher projectivity AND lower at-issueness. -/
theorem gpp_orders_occasion_vs_psych :
    exp2_occasion_gpp.projectivity > exp2_stimExp_gpp.projectivity ∧
    exp2_occasion_gpp.atIssueness < exp2_stimExp_gpp.atIssueness ∧
    exp2_occasion_gpp.projectivity > exp2_expStim_gpp.projectivity ∧
    exp2_occasion_gpp.atIssueness < exp2_expStim_gpp.atIssueness := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [exp2_occasion_gpp, exp2_stimExp_gpp, exp2_expStim_gpp,
              exp2_occasion_proj, exp2_stimExp_proj, exp2_expStim_proj]

end SolstadBott2024
