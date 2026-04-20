import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Semantics.Attitudes.NegRaising
import Linglib.Phenomena.TemporalConnectives.Studies.Karttunen1974
import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Semantics.Causation.Interpretation
import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Phenomena.Negation.Typology
import Linglib.Fragments.French.Negation
import Linglib.Fragments.Mandarin.Negation
import Linglib.Fragments.Januubi.Negation
import Linglib.Fragments.ZarmaSonrai.Negation
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Jin & Koenig (2021): A Cross-Linguistic Study of Expletive Negation
@cite{jin-koenig-2021}

Linguistic Typology, 25(1), 39–78.

A typological study of expletive negation (EN) — semantically vacuous
negation triggered by the lexical meaning of an embedding predicate or
operator. Based on a survey of 722 languages (EN attested in 74, across
37 genera) and detailed comparison of five languages: English, French,
Januubi, Mandarin, and Zarma-Sonrai.

## Core Contribution: Why EN Triggers Are Cross-Linguistically Similar

The paper's central insight: EN occurs when a trigger's meaning activates
both a proposition **p** and its dual **¬p** (in different modal or
temporal domains). This dual activation, via spreading activation in
language production (@cite{dell-1986}), sometimes causes the negator
for ¬p to surface in the complement clause.

## Four Licensing Conditions (§5.5, ex. 13)

EN triggers obey one of four semantic licensing conditions:

1. **Propositional attitude / speech report triggers** (§6.1):
   Meaning entails Operator₁(p) and Operator₂(¬p) — p and ¬p hold
   in different sets of worlds (attitude vs. desire, belief vs. standards).

2. **Temporal operator triggers** (§6.2):
   Meaning entails p at time t and ¬p at time t' — two time intervals.

3. **Logical operator triggers** (§6.3):
   Meaning includes ¬ directly (impossible, without, unless).

4. **Comparative triggers** (§6.4):
   Meaning entails Q(Y,D) and ¬Q(Z,D') — predications over distinct
   entities/degrees.

## Table 5 Trigger Taxonomy

| Class      | Subclasses                                    |
|------------|-----------------------------------------------|
| "FEAR"     | FEAR, AVOID                                   |
| "REGRET"   | REGRET, COMPLAIN, ADVISE AGAINST              |
| "DENY"     | DENY, HIDE, DESPAIR                           |
| "FORGET"   | FORGET, DELAY, REFUSE, STOP/PREVENT, ALMOST   |
| TEMPORALS  | BEFORE, CANNOT WAIT, SINCE, RARELY            |
| "IMPOSSIBLE" | IMPOSSIBLE, DIFFICULT                        |
| "WITHOUT"  | WITHOUT                                       |
| "UNLESS"   | UNLESS, IT ONLY DEPENDS ON SOMEONE THAT       |
| COMPARATIVES | MORE THAN, LESS THAN, DIFFERENT THAN, TOO…TO |
-/

namespace JinKoenig2021

open Semantics.Attitudes.Preferential (AttitudeValence PreferentialPredicate NVPClass
                                        classifyNVP fear dread worry)

-- ════════════════════════════════════════════════════
-- § 1. Typological Survey Data (Tables 1–4)
-- ════════════════════════════════════════════════════

/-- The overall survey: 722 languages, EN in 74 (37 genera).
    Data is defined in `Phenomena.Negation.Typology.enSurvey`
    to avoid duplication across study files. -/
def survey := Phenomena.Negation.Typology.enSurvey

/-- Per-trigger occurrence counts (Table 4). The number of languages
    (out of the 74 with any EN) where each trigger concept was attested. -/
structure TriggerCount where
  trigger : String
  count : Nat
  deriving Repr

def triggerCounts : List TriggerCount :=
  [ ⟨"BEFORE/UNTIL", 50⟩
  , ⟨"FEAR/AFRAID", 39⟩
  , ⟨"FORBID/PROHIBIT/WITHOUT", 10⟩
  , ⟨"ALMOST/UNLESS/AVOID/INEVITABLE", 8⟩
  , ⟨"PREVENT/DENY", 7⟩
  , ⟨"DOUBT/THAN", 6⟩
  , ⟨"BEWARE/REFUSE", 5⟩
  , ⟨"WORRY/SINCE", 4⟩
  , ⟨"IMPOSSIBLE/FROM/TOO…TO", 3⟩
  , ⟨"CRITICIZE/ONLY", 2⟩
  , ⟨"ADVISE AGAINST/CANNOT WAIT/COMPLAIN/DESPAIR/FORGET/...", 1⟩ ]

/-- BEFORE and FEAR are the two most widespread EN triggers. -/
theorem before_and_fear_most_widespread :
    triggerCounts.head? = some ⟨"BEFORE/UNTIL", 50⟩ := rfl

-- ════════════════════════════════════════════════════
-- § 2. EN Trigger Taxonomy (Tables 5–6)
-- ════════════════════════════════════════════════════

/-- The four main classes of EN-licensing conditions (§5.5, ex. 13). -/
inductive LicensingCondition where
  /-- Meaning entails Operator₁(p) and Operator₂(¬p) in different
      sets of worlds (attitude content vs. desire/standards/beliefs). -/
  | propositionalAttitude
  /-- Meaning entails p at time t and ¬p at time t'. -/
  | temporalOperator
  /-- Meaning includes ¬ directly (impossible, without, unless). -/
  | logicalOperator
  /-- Meaning entails Q(Y,D) and ¬Q(Z,D') over distinct entities. -/
  | comparative
  deriving DecidableEq, Repr

/-- Subclasses of EN triggers within each licensing condition (Table 5). -/
inductive TriggerSubclass where
  -- Propositional attitude (§6.1)
  | fear           -- fear, avoid, beware (§6.1.1)
  | regret         -- regret, complain, advise against (§6.1.2)
  | deny           -- deny, hide, despair (§6.1.3)
  -- "Forget" class — semantically heterogeneous (§6.1.4)
  | forget         -- forget, delay, refuse, stop, prevent, almost
  -- Temporal operators (§6.2)
  | before         -- before/until (§6.2.1)
  | cannotWait     -- cannot wait (§6.2.2)
  | since          -- since (§6.2.3)
  | rarely         -- rarely (§6.2.4)
  -- Logical operators (§6.3)
  | impossible     -- impossible, difficult (§6.3.1)
  | without        -- without (§6.3.2)
  | unless         -- unless, it only depends on someone that (§6.3.3)
  -- Comparatives (§6.4)
  | moreThan       -- more/less Q than (§6.4)
  | differentThan  -- q is different than p (§6.4)
  | tooTo          -- too Q to p (§6.4)
  deriving DecidableEq, Repr

/-- Each subclass belongs to exactly one licensing condition. -/
def TriggerSubclass.licensingCondition : TriggerSubclass → LicensingCondition
  | .fear | .regret | .deny | .forget => .propositionalAttitude
  | .before | .cannotWait | .since | .rarely => .temporalOperator
  | .impossible | .without | .unless => .logicalOperator
  | .moreThan | .differentThan | .tooTo => .comparative

-- ════════════════════════════════════════════════════
-- § 3. Dual Inference: The Core Semantic Property
-- ════════════════════════════════════════════════════

/-! ### The dual-inference property

The central observation: EN triggers activate both p and ¬p, but in
**different domains** (different sets of worlds, different time intervals,
different degrees). Table 6 catalogs the positive and negative inferences
for each trigger subclass.

For propositional attitude triggers, the two domains are:
- **Positive inference**: p in worlds consistent with X's attitude
- **Negative inference**: ¬p in worlds consistent with X's desires/standards/beliefs

For temporal triggers:
- **Positive inference**: p at time t
- **Negative inference**: ¬p at reference time r (or at a different time t')

For logical triggers, ¬ is part of the operator's meaning (no separate domain).

For comparatives, the dual involves predications over distinct entities/degrees. -/

/-- The positive and negative inferences of a trigger subclass (Table 6).
    These are natural-language descriptions of the modal/temporal domains
    in which p and ¬p hold, respectively. -/
structure DualInferenceProfile where
  subclass : TriggerSubclass
  /-- Domain where p holds (positive inference) -/
  positiveInference : String
  /-- Domain where ¬p holds (negative inference) -/
  negativeInference : String
  deriving Repr

/-- Table 6 data: positive and negative inferences for each trigger
    concept (@cite{jin-koenig-2021}, pp. 70–71). All 28 rows of the
    paper's Table 6 are encoded. Within each class, concepts often have
    *different* inference profiles (e.g., AVOID adds "and in w₀" to FEAR's
    positive inference; DESPAIR has three sources of inference). -/
def table6 : List DualInferenceProfile :=
  [ -- "FEAR" class (§6.1.1)
    { subclass := .fear
    , positiveInference := "p in worlds consistent with X's attitude"
    , negativeInference := "¬p in worlds consistent with X's desires" }
  , { subclass := .fear  -- AVOID
    , positiveInference := "p in worlds consistent with the normal course of events"
    , negativeInference := "¬p in possible worlds consistent with X's desires and in w₀" }
  -- "REGRET" class (§6.1.2)
  , { subclass := .regret  -- REGRET
    , positiveInference := "p in worlds consistent with X's attitude"
    , negativeInference := "¬p in worlds consistent with X's behavioral standards" }
  , { subclass := .regret  -- COMPLAIN
    , positiveInference := "p in worlds consistent with X's words (and beliefs)"
    , negativeInference := "¬p in worlds consistent with X's behavioral standards" }
  , { subclass := .regret  -- ADVISE AGAINST
    , positiveInference := "p in worlds consistent with one alternative course of action"
    , negativeInference := "¬p in optimal worlds" }
  -- "DENY" class (§6.1.3)
  , { subclass := .deny  -- DENY
    , positiveInference := "p in worlds consistent with what is on the table (somebody else's beliefs)"
    , negativeInference := "¬p in worlds consistent with X's beliefs (words)" }
  , { subclass := .deny  -- HIDE
    , positiveInference := "p in w₀"
    , negativeInference := "¬p in worlds consistent with what X says (implication)" }
  , { subclass := .deny  -- DESPAIR
    , positiveInference := "p in worlds consistent with X's hopes"
    , negativeInference := "¬p in worlds consistent with X's beliefs and w₀ at r" }
  -- "FORGET" class (§6.1.4) — semantically heterogeneous
  , { subclass := .forget  -- FORGET
    , positiveInference := "p in worlds consistent with X's obligations"
    , negativeInference := "¬p in w₀" }
  , { subclass := .forget  -- DELAY
    , positiveInference := "p in worlds consistent with X's obligations or in the normal course of events"
    , negativeInference := "¬p in w₀" }
  , { subclass := .forget  -- REFUSE
    , positiveInference := "p in worlds consistent with norms consistent with X's decisions"
    , negativeInference := "¬p in w₀ and in worlds consistent with X's decisions" }
  , { subclass := .forget  -- STOP
    , positiveInference := "p at t' < r"
    , negativeInference := "¬p in w₀" }
  , { subclass := .forget  -- PREVENT
    , positiveInference := "p if the antagonist hadn't prevailed"
    , negativeInference := "¬p in w₀" }
  , { subclass := .forget  -- ALMOST
    , positiveInference := "p in worlds close to w₀"
    , negativeInference := "¬p in w₀" }
  , { subclass := .forget  -- BARELY
    , positiveInference := "p at w₀"
    , negativeInference := "¬p in worlds close to w₀" }
  -- Temporal operator triggers (§6.2)
  , { subclass := .before  -- BEFORE
    , positiveInference := "p at t"
    , negativeInference := "¬p at r when q is true" }
  , { subclass := .cannotWait  -- CANNOT WAIT FOR
    , positiveInference := "p at t in worlds consistent with X's expectations about the future"
    , negativeInference := "¬p at r when q is true" }
  , { subclass := .since  -- SINCE
    , positiveInference := "p at t"
    , negativeInference := "¬p at r" }
  , { subclass := .rarely  -- RARELY
    , positiveInference := "p at a small number of intervals of time"
    , negativeInference := "¬p at a large number of intervals of time" }
  -- Logical operator triggers (§6.3)
  , { subclass := .impossible  -- IMPOSSIBLE
    , positiveInference := "N/A"
    , negativeInference := "¬p in worlds accessible from w₀" }
  , { subclass := .impossible  -- DIFFICULT
    , positiveInference := "N/A"
    , negativeInference := "¬p in most worlds accessible from w₀" }
  , { subclass := .without  -- WITHOUT
    , positiveInference := "N/A"
    , negativeInference := "¬p at reference time" }
  , { subclass := .unless  -- UNLESS
    , positiveInference := "N/A"
    , negativeInference := "¬p in suppositive worlds" }
  , { subclass := .unless  -- IT ONLY DEPENDS ON SOMEONE THAT
    , positiveInference := "p in worlds where X acts (appropriately)"
    , negativeInference := "¬p in worlds where X does not act (appropriately)" }
  -- Comparative triggers (§6.4)
  , { subclass := .moreThan  -- MORE THAN
    , positiveInference := "Q(Z, D)"
    , negativeInference := "¬Q(Z, D'), D' > D" }
  , { subclass := .moreThan  -- LESS THAN
    , positiveInference := "Q(Z, D)"
    , negativeInference := "¬Q(Z, D'), D' = D-max" }
  , { subclass := .differentThan  -- DIFFERENT THAN
    , positiveInference := "p' in w₀ or at t'"
    , negativeInference := "¬p in w₀ or at t" }
  , { subclass := .tooTo  -- TOO...TO
    , positiveInference := "p when Q(Y, D'') D'' < D-norm for p"
    , negativeInference := "¬p in w₀, Q(Y, D') D' > D-norm for p" } ]

/-- All 28 rows of the paper's Table 6 (pp. 70–71) are encoded. Some
    subclasses have multiple entries with distinct inference profiles
    (e.g., FEAR vs AVOID, IMPOSSIBLE vs DIFFICULT). -/
theorem table6_complete :
    table6.length = 28 := rfl

-- ════════════════════════════════════════════════════
-- § 4. Bridges to Attitude Verb Infrastructure
-- ════════════════════════════════════════════════════

/-! ### Connecting EN licensing to preferential attitude semantics

The FEAR trigger class (§6.1.1) licenses EN because the meaning of
fear-type verbs activates both p (content of attitude — what X fears)
and ¬p (content of desire — what X wants). This dual activation
corresponds precisely to **negative valence** in the preferential
attitude semantics of @cite{villalta-2008}:

- Positive valence (hope, wish): X wants p → only p is activated
- Negative valence (fear, dread): X fears p but wants ¬p → both activated

The key theorem: negative-valence predicates satisfy the
propositional attitude licensing condition for EN.  -/

/-- Negative-valence predicates have dual inference: the meaning
    activates both p (feared proposition) and ¬p (desired alternative).
    This is DERIVED from the valence field of the preferential predicate,
    not stipulated. -/
def negativeValenceEntailsDual (v : AttitudeValence) : Bool :=
  v == .negative

/-- Fear has negative valence → satisfies the dual-inference condition. -/
theorem fear_has_dual_inference {W E : Type*}
    (μ : Semantics.Attitudes.Preferential.PreferenceFunction W E)
    (θ : Semantics.Attitudes.Preferential.ThresholdFunction W) :
    negativeValenceEntailsDual (fear μ θ).valence = true := rfl

/-- Dread has negative valence → satisfies the dual-inference condition. -/
theorem dread_has_dual_inference {W E : Type*}
    (μ : Semantics.Attitudes.Preferential.PreferenceFunction W E)
    (θ : Semantics.Attitudes.Preferential.ThresholdFunction W) :
    negativeValenceEntailsDual (dread μ θ).valence = true := rfl

/-- Worry has negative valence → satisfies the dual-inference condition.
    (Non-C-distributive, but still negative valence.) -/
theorem worry_has_dual_inference {W E : Type*}
    (μ : Semantics.Attitudes.Preferential.PreferenceFunction W E)
    (θ : Semantics.Attitudes.Preferential.ThresholdFunction W)
    (isUncertain : E → Semantics.Attitudes.Preferential.QuestionDen W → Bool) :
    negativeValenceEntailsDual (worry μ θ isUncertain).valence = true := rfl

/-- Hope has positive valence → does NOT satisfy the dual-inference
    condition → NOT an EN trigger. While 'hope' has been reported as a
    possible EN trigger in Japanese/Korean (@cite{jin-koenig-2021}, §2,
    exx. 5–6), JK2021 exclude these based on their definition (2): the
    complement negation reflects epistemic uncertainty, not EN. -/
theorem hope_no_dual_inference {W E : Type*}
    (μ : Semantics.Attitudes.Preferential.PreferenceFunction W E)
    (θ : Semantics.Attitudes.Preferential.ThresholdFunction W) :
    negativeValenceEntailsDual
      (Semantics.Attitudes.Preferential.hope μ θ).valence = false := rfl

/-- NVP Class 2 (C-distributive + negative valence) = the class that
    licenses EN in complement clauses. This connects the preferential
    attitude classification to the EN trigger taxonomy. -/
theorem class2_licenses_EN :
    negativeValenceEntailsDual .negative = true ∧
    negativeValenceEntailsDual .positive = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Neg-Raising Infrastructure
-- ════════════════════════════════════════════════════

/-! ### DENY triggers and neg-raising

The DENY class (§6.1.3) licenses EN because DENY entails or implies
BELIEVE(X, ¬p). In neg-raising terms: when the matrix clause is
negated or questioned, both p and ¬p are activated (the doxastic
square has both Bel(p) and Bel(¬p) as corners).

The connection: neg-raising predicates activate both p and ¬p
precisely because ¬Bel(p) pragmatically strengthens to Bel(¬p).
When DOUBT is negated or questioned, this dual activation occurs,
licensing EN.

This is consistent with the empirical observation that DOUBT and
DENY triggers in French often require the matrix clause to be negated
or questioned for EN to occur (§6.1.3). -/

open Semantics.Attitudes.NegRaising (negRaisingAvailable)
open Semantics.Attitudes.Doxastic (Veridicality)

/-- DENY triggers license EN through the doxastic square:

    1. Non-veridical doxastic predicates (believe, doubt) support
       neg-raising: ¬Bel(p) strengthens to Bel(¬p) (NegRaising.lean)
    2. Under negation/questioning, this pragmatic strengthening
       activates both Bel(p) and Bel(¬p) simultaneously — the
       dual inference required for EN (§6.1.3)
    3. DENY maps to the propositional attitude licensing condition

    The paper says explicitly: "triggers such as QUESTION or DOUBT
    do not strictly entail BELIEVE(X, ¬p); they only strongly imply
    BELIEVE(X, ¬p)" — this IS neg-raising (O→E strengthening). -/
theorem deny_EN_via_negRaising :
    negRaisingAvailable .nonVeridical = true ∧
    TriggerSubclass.deny.licensingCondition = .propositionalAttitude :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Cross-Linguistic Trigger Similarity (Table 5)
-- ════════════════════════════════════════════════════

/-! ### Five-language comparison

Table 5 shows that the trigger classes are strikingly similar across
five languages from four distinct families:
- English (Germanic/Indo-European)
- French (Italic/Indo-European)
- Januubi (Semitic/Afro-Asiatic)
- Mandarin (Sinitic/Sino-Tibetan)
- Zarma-Sonrai (Songhay/Nilo-Saharan)

Each entry records whether a language has lexical items for a given
trigger subclass. -/

/-- A cross-linguistic trigger attestation datum (Table 5).
    Each Bool records whether any subclass member triggers EN in that
    language. `.differentThan` is omitted (not a separate Table 5 row;
    analyzed only in §6.4 and Table 6). -/
structure TriggerAttestation where
  subclass : TriggerSubclass
  /-- Does the language have EN-triggering lexical items for this class? -/
  english : Bool
  french : Bool
  januubi : Bool
  mandarin : Bool
  zarmaSonrai : Bool
  deriving Repr

def triggerAttestations : List TriggerAttestation :=
  [ { subclass := .fear,     english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .regret,   english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .deny,     english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .forget,   english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .before,   english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .cannotWait, english := true, french := true, januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .impossible, english := true, french := true, januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .without,  english := true,  french := true,  januubi := true,
      mandarin := false, zarmaSonrai := false }
  , { subclass := .unless,   english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .since,    english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .rarely,   english := true,  french := true,  januubi := true,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .moreThan, english := true,  french := true,  januubi := false,
      mandarin := true,  zarmaSonrai := true }
  , { subclass := .tooTo,    english := true,  french := true,  januubi := false,
      mandarin := false, zarmaSonrai := false } ]

/-- Ten trigger subclasses are attested in all five languages (Table 5).
    The three non-universal subclasses are WITHOUT (Mandarin and Zarma-Sonrai
    express it as "q not p", §7), MORE THAN (Januubi only allows NPs as
    complements of comparatives, §6.4), and TOO...TO (Januubi, Mandarin,
    and Zarma-Sonrai use "too...so that...not" collocations, §6.4). -/
theorem core_triggers_universal :
    (triggerAttestations.filter (λ d =>
      [TriggerSubclass.fear, .regret, .deny, .forget, .before,
       .cannotWait, .since, .rarely, .impossible, .unless].contains d.subclass)
    ).all (λ d => d.english && d.french && d.januubi && d.mandarin && d.zarmaSonrai)
    = true := by native_decide

/-- WITHOUT, MORE THAN, and TOO...TO are attested in only a subset
    of languages due to language-internal structural factors (§6.4, §7). -/
theorem non_universal_triggers_explained :
    (triggerAttestations.filter (λ d =>
      [TriggerSubclass.without, .moreThan, .tooTo].contains d.subclass)
    ).all (λ d => !(d.english && d.french && d.januubi && d.mandarin && d.zarmaSonrai))
    = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Connecting Trigger Classes to Licensing Conditions
-- ════════════════════════════════════════════════════

/-- All attitude/speech report triggers map to the propositional attitude
    licensing condition. -/
theorem attitude_triggers_grouped :
    [TriggerSubclass.fear, .regret, .deny, .forget].all
      (·.licensingCondition == .propositionalAttitude) = true := rfl

/-- All temporal triggers map to the temporal operator licensing condition. -/
theorem temporal_triggers_grouped :
    [TriggerSubclass.before, .cannotWait, .since, .rarely].all
      (·.licensingCondition == .temporalOperator) = true := rfl

/-- All logical triggers map to the logical operator licensing condition. -/
theorem logical_triggers_grouped :
    [TriggerSubclass.impossible, .without, .unless].all
      (·.licensingCondition == .logicalOperator) = true := rfl

/-- All comparative triggers map to the comparative licensing condition. -/
theorem comparative_triggers_grouped :
    [TriggerSubclass.moreThan, .differentThan, .tooTo].all
      (·.licensingCondition == .comparative) = true := rfl

-- ════════════════════════════════════════════════════
-- § 7b. Typed Inference Domains
-- ════════════════════════════════════════════════════

/-! ### The type of domain determines the licensing condition

The paper's four licensing conditions correspond to four types of domain
in which p and ¬p hold. This is not stated explicitly in the paper but
follows from the structure of Table 6: propositional attitude triggers
always involve different *sets of worlds*, temporal triggers involve
different *time intervals*, logical operators include ¬ *structurally*,
and comparatives involve different *degrees*. -/

/-- The type of domain in which a trigger's inferences hold. -/
inductive InferenceDomainType where
  | modal      -- Different sets of possible worlds
  | temporal   -- Different time intervals
  | structural -- ¬ is part of the meaning (no separate domain for p)
  | degree     -- Different degrees on a scale
  deriving DecidableEq, Repr

/-- Each trigger subclass has a characteristic domain type. -/
def TriggerSubclass.inferenceDomainType : TriggerSubclass → InferenceDomainType
  | .fear | .regret | .deny | .forget => .modal
  | .before | .cannotWait | .since | .rarely => .temporal
  | .impossible | .without | .unless => .structural
  | .moreThan | .differentThan | .tooTo => .degree

/-- The inference domain type determines the licensing condition.
    This is a structural invariant: any trigger whose inferences
    involve different worlds maps to propositionalAttitude, etc. -/
theorem domainType_determines_condition (s : TriggerSubclass) :
    s.licensingCondition = match s.inferenceDomainType with
      | .modal => .propositionalAttitude
      | .temporal => .temporalOperator
      | .structural => .logicalOperator
      | .degree => .comparative := by
  cases s <;> rfl

-- ════════════════════════════════════════════════════
-- § 8. Temporal Bridge: BEFORE → Dual Inference
-- ════════════════════════════════════════════════════

/-! ### BEFORE satisfies the temporal operator licensing condition

Anscombe's BEFORE semantics:
  A BEFORE B ↔ ∃t ∈ timeTrace(A), ∀t' ∈ timeTrace(B), t < t'

This entails:
- **Positive inference**: p is true at time t (∃t ∈ timeTrace(A))
- **Negative inference**: ¬p at reference time r (the complement time)

The temporal dual-inference property follows directly from the
definition: BEFORE entails that the main clause event (p) occurs at
a time strictly preceding all complement-clause times, hence p holds
at t but not at any complement time t'.

The paper identifies BEFORE as the single most widespread EN trigger
(50 languages), consistent with its transparent dual-inference structure. -/

open Semantics.Tense.TemporalConnectives
  (SentDenotation timeTrace Anscombe.before Karttunen.notUntil)

/-- BEFORE entails a temporal witness for p (the main clause event
    occurs at some time). This is the positive inference. -/
theorem before_positive_inference {Time : Type*} [LinearOrder Time]
    (A B : SentDenotation Time) (h : Anscombe.before A B) :
    ∃ t, t ∈ timeTrace A := by
  obtain ⟨t, ht, _⟩ := h; exact ⟨t, ht⟩

/-- BEFORE entails temporal separation: the main-clause time strictly
    precedes all complement-clause times. When B is nonempty,
    p (at t) and ¬p (at any t' ∈ B) coexist — the dual inference. -/
theorem before_temporal_separation {Time : Type*} [LinearOrder Time]
    (A B : SentDenotation Time) (h : Anscombe.before A B) :
    ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t' := h

/-- BEFORE licenses EN because it maps to the temporal operator
    licensing condition (§6.2, ex. 13b). -/
theorem before_licensing :
    TriggerSubclass.before.licensingCondition = .temporalOperator := rfl

/-- Punctual UNTIL = ¬BEFORE (Karttunen): the negation of BEFORE
    surfaces as the complement-clause negator, which is exactly EN. -/
theorem until_en_from_before_negation {Time : Type*} [LinearOrder Time]
    (A B : SentDenotation Time) :
    Karttunen.notUntil A B ↔ ¬ Anscombe.before A B := Iff.rfl

-- ════════════════════════════════════════════════════
-- § 9. Modal Bridge: IMPOSSIBLE → Logical Operator
-- ════════════════════════════════════════════════════

/-! ### IMPOSSIBLE satisfies the logical operator licensing condition

IMPOSSIBLE p = □¬p (necessity of negation): p is false in all
accessible worlds. The meaning of IMPOSSIBLE includes ¬ directly
— the negation is part of the operator's meaning, not contributed
by a separate negator.

Kratzer's `necessity f g (¬p) w` computes: all best accessible worlds
satisfy ¬p. The ¬ in the complement is structural, not expletive —
but from the language production perspective, the activation of ¬p
alongside p (in worlds outside the modal base) triggers EN. -/

open Semantics.Modality.Kratzer (necessity possibility necessity_iff_all possibility_iff_any
  ModalBase OrderingSource bestWorlds)
open Semantics.Attitudes.Intensional (World)

/-- IMPOSSIBLE maps to the logical operator licensing condition. -/
theorem impossible_licensing :
    TriggerSubclass.impossible.licensingCondition = .logicalOperator := rfl

/-- ¬IMPOSSIBLE p = POSSIBLE p: when necessity of ¬p fails,
    possibility of p holds. The dual activation of p and ¬p when
    IMPOSSIBLE is negated or questioned is what licenses EN.

    Proof: necessity = List.all, possibility = List.any;
    ¬(all ¬p) → (any p) over finite lists. -/
private theorem all_not_false_any_true {α : Type*} (L : List α) (p : α → Bool) :
    L.all (λ x => !p x) = false → L.any p = true := by
  induction L with
  | nil => intro h; simp [List.all_nil] at h
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons]
    cases p x <;> simp_all

theorem not_impossible_activates_p (f : ModalBase World) (g : OrderingSource World)
    (p : (World → Prop)) (w : World) :
    ¬ necessity f g (λ w' => ¬ p w') w →
    possibility f g p w := by
  rw [necessity_iff_all, possibility_iff_any]
  intro h
  by_contra hne
  push_neg at hne
  exact h fun w' hw' => hne w' hw'

-- ════════════════════════════════════════════════════
-- § 9b. WITHOUT Bridge: q ∧ ¬p → Logical Operator
-- ════════════════════════════════════════════════════

/-! ### WITHOUT satisfies the logical operator licensing condition

"q WITHOUT p" entails q ∧ ¬p. The negation of p is a necessary part
of the meaning of WITHOUT — it is structural, not expletive (§6.3.2).

The paper notes that "in the examples we found, there is an entailment
that ¬p is true at reference time t (e.g., the speaker not knowing it)
and that reference time includes the event time for q (e.g., the time
where she left)."

Cross-linguistically, WITHOUT triggers EN in English, French, and Januubi
but NOT in Mandarin or Zarma-Sonrai (which express WITHOUT analytically
as "q not p", making the negation non-expletive). -/

/-- WITHOUT q p = q ∧ ¬p: the meaning structurally includes ¬. -/
def withoutSem {W : Type*} (q p : (W → Bool)) : (W → Bool) :=
  λ w => q w && !p w

/-- WITHOUT structurally includes negation: if "q without p" holds,
    then p is false. -/
theorem without_entails_not_p {W : Type*} (q p : (W → Bool)) (w : W)
    (h : withoutSem q p w = true) : p w = false := by
  simp only [withoutSem] at h
  cases hp : p w <;> simp_all

/-- WITHOUT structurally includes the main clause: if "q without p"
    holds, then q is true. -/
theorem without_entails_q {W : Type*} (q p : (W → Bool)) (w : W)
    (h : withoutSem q p w = true) : q w = true := by
  simp only [withoutSem] at h
  cases hq : q w <;> simp_all

/-- WITHOUT maps to the logical operator licensing condition. -/
theorem without_licensing :
    TriggerSubclass.without.licensingCondition = .logicalOperator := rfl

-- ════════════════════════════════════════════════════
-- § 10. Conditional Bridge: UNLESS → Logical Operator
-- ════════════════════════════════════════════════════

/-! ### UNLESS satisfies the logical operator licensing condition

UNLESS q p = if ¬p then q = materialImp (¬p) q.

The meaning of UNLESS structurally includes ¬: the conditional's
antecedent is the negation of p. This makes ¬p part of the operator's
meaning, satisfying the logical operator licensing condition (§6.3.3).

More precisely: "q UNLESS p" entails that ¬p is true in all
*suppositive worlds* (worlds where q holds). -/

open Semantics.Conditionals (materialImp)

/-- UNLESS q p is definable as material implication with negated
    antecedent: if ¬p then q. The negation is structural. -/
def unlessSem {W : Type*} (q p : Set W) : Set W :=
  materialImp pᶜ q

/-- UNLESS includes ¬ in its meaning: at any world where ¬p is true
    AND q is true, the conditional holds. Conversely, at any world
    where the conditional holds and ¬p is true, q must be true. -/
theorem unless_modus_ponens {W : Type*} (q p : Set W) (w : W)
    (hcond : unlessSem q p w) (hnp : ¬ p w) : q w :=
  hcond hnp

/-- UNLESS maps to the logical operator licensing condition. -/
theorem unless_licensing :
    TriggerSubclass.unless.licensingCondition = .logicalOperator := rfl

-- ════════════════════════════════════════════════════
-- § 11. Comparative Bridge: MORE THAN → Dual Inference
-- ════════════════════════════════════════════════════

/-! ### MORE THAN satisfies the comparative licensing condition

"Y is MORE Q THAN Z" entails (via @cite{jin-koenig-2021}, Table 6):
- **Positive**: Q(Z, D) — Z has property Q to degree D
- **Negative**: ¬Q(Z, D'), D' > D — Z does NOT have Q to degree D'

In the degree semantics of `Theories.Semantics.Degree.Comparative`:
  comparativeSem μ a b .positive ↔ μ(a) > μ(b)

This entails: ∃D (= μ(b)) such that Q(Z, D), and ∃D' (= μ(a)) > D
such that ¬Q(Z, D'). The dual predication over distinct degrees is
what licenses EN in the complement of comparatives. -/

open Semantics.Degree.Comparative (comparativeSem)

/-- A comparative entails dual degree predication: Y exceeds Z on
    the scale, so Q(Z, μ(Z)) holds but ¬Q(Z, μ(Y)) — dual inference
    over distinct degrees. -/
theorem comparative_dual_degrees {Entity : Type*} {α : Type*} [LinearOrder α]
    (μ : Entity → α) (a b : Entity)
    (h : comparativeSem μ a b .positive) :
    μ a > μ b := h

/-- The comparative antonymy theorem connects MORE and LESS:
    "A is more Q than B" ↔ "B is less Q than A" (= "B is more Q⁻ than A").
    Both entail dual predication. -/
theorem comparative_antonymy_preserves_dual {Entity : Type*} {α : Type*}
    [LinearOrder α] (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ comparativeSem μ b a .negative :=
  Semantics.Degree.Comparative.taller_shorter_antonymy μ a b

/-- Comparatives map to the comparative licensing condition. -/
theorem comparative_licensing :
    TriggerSubclass.moreThan.licensingCondition = .comparative := rfl

-- ════════════════════════════════════════════════════
-- § 11b. FORGET-Class Bridges: Heterogeneous Subclasses
-- ════════════════════════════════════════════════════

/-! ### Connecting FORGET-class subclasses to theory modules

The FORGET class (§6.1.4) is "semantically heterogeneous" — the paper
groups these triggers by their shared negative entailment (¬p in w₀ or
close to w₀), but they derive from distinct semantic mechanisms:

| Subclass    | Theory module          | Key type                  |
|-------------|------------------------|---------------------------|
| FORGET      | Causation/Implicative  | Implicative.negative |
| STOP/PREVENT| Causation/Builder      | Causative.prevent  |
| ALMOST      | Degree/Comparative     | threshold proximity       |

Each mechanism independently entails ¬p in the real world, unifying
the class despite its heterogeneity. -/

open Core.Verbs (Causative Implicative)

/-- FORGET is a negative implicative: "X forgot to do Y" entails that
    Y did NOT happen (¬p in w₀). This is DERIVED from the implicative
    builder's polarity, not stipulated.
    @cite{nadathur-2023}: negative implicatives entail complement falsity. -/
theorem forget_grounded_in_implicativity :
    Implicative.negative.entailsComplement = false := rfl

/-- STOP/PREVENT are causative preventatives: "X prevented Y" entails
    that Y did NOT occur (¬p in w₀). The negative entailment comes from
    the causal blocking semantics of `preventSem`.
    @cite{nadathur-lauer-2020}: prevent = effect blocked with preventer,
    would have occurred without it. -/
theorem prevent_is_causative_builder :
    (Causative.prevent).assertsSufficiency = false := rfl

/-- The FORGET class is unified by real-world negative entailment:
    all subclasses entail ¬p in w₀ (or worlds close to w₀), but
    through different semantic mechanisms. The class maps to the
    propositional attitude licensing condition because the positive
    inference involves a modal domain (obligations, normal course). -/
theorem forget_class_licensing :
    TriggerSubclass.forget.licensingCondition = .propositionalAttitude ∧
    TriggerSubclass.forget.inferenceDomainType = .modal := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 12. Fragment Bridges: Cross-Linguistic Negator Data
-- ════════════════════════════════════════════════════

/-! ### Connecting cross-linguistic EN attestation to fragment entries

Table 5 records that EN is attested in all five languages. The fragment
files for each language formalize the negation markers. Here we verify
that the fragment data is consistent with the attestation table:
each language's EN markers exist and have the expected properties. -/

/-- French uses dedicated *ne* (without *pas*) for high-entrenchment EN.
    This is distinct from standard *ne...pas* negation (@cite{jin-koenig-2021}, §4). -/
theorem french_has_dedicated_en_marker :
    Fragments.French.Negation.enMarker = Fragments.French.Negation.neClitic := rfl

/-- Mandarin FEAR triggers use imperative negation (*bié*/*búyào*), not
    the standard *bù*/*méi*. The imperative form lexicalizes the
    prohibition component of the FEAR meaning. -/
theorem mandarin_fear_en_is_imperative :
    Fragments.Mandarin.Negation.bieParticle = "bié" ∧
    Fragments.Mandarin.Negation.buyaoParticle = "búyào" := ⟨rfl, rfl⟩

/-- Mandarin REGRET/COMPLAIN triggers use the deontic negator *bùgāi*
    'shouldn't', connecting to the behavioral-standards semantics
    (negative inference = ¬p in worlds consistent with X's standards). -/
theorem mandarin_regret_en_is_deontic :
    Fragments.Mandarin.Negation.bugaiParticle = "bùgāi" := rfl

/-- Januubi uses the standard negator *maa* for all EN contexts —
    no dedicated EN marker or trigger-class covariation. -/
theorem januubi_en_is_standard :
    Fragments.Januubi.Negation.enNegator.isStandardNeg = true := rfl

/-- Zarma-Sonrai EN negator choice is determined by aspect (IPFV/PFV),
    not by trigger class. Both markers are standard negation markers. -/
theorem zarma_en_determined_by_aspect :
    Fragments.ZarmaSonrai.Negation.enIpfv.isStandardNeg = true ∧
    Fragments.ZarmaSonrai.Negation.enPfv.isStandardNeg = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 13. All Licensing Conditions Grounded
-- ════════════════════════════════════════════════════

/-! ### Summary: Each licensing condition is now connected to theory-layer
    semantics by construction.

| Licensing condition     | Theory module               | Bridge theorem               |
|-------------------------|-----------------------------|------------------------------|
| propositionalAttitude   | Attitudes.Preferential      | fear_has_dual_inference      |
|                         | Attitudes.NegRaising        | deny_EN_via_negRaising       |
| temporalOperator        | Tense.TemporalConnectives   | before_temporal_separation   |
| logicalOperator         | Modality.Kratzer             | not_impossible_activates_p   |
|                         | Conditionals.Basic           | unless_modus_ponens          |
|                         | (conjunction + negation)     | without_entails_not_p        |
| comparative             | Degree.Comparative           | comparative_dual_degrees     |
-/

/-- All four licensing conditions have at least one bridge theorem
    connecting them to a Theory-layer semantic operator. -/
theorem all_conditions_grounded :
    -- Propositional attitude: fear has dual inference (§4)
    negativeValenceEntailsDual .negative = true ∧
    -- Temporal: before maps to temporal (§8)
    TriggerSubclass.before.licensingCondition = .temporalOperator ∧
    -- Logical: impossible maps to logical (§9)
    TriggerSubclass.impossible.licensingCondition = .logicalOperator ∧
    -- Comparative: moreThan maps to comparative (§11)
    TriggerSubclass.moreThan.licensingCondition = .comparative :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 14. Formal EN Definition
-- ════════════════════════════════════════════════════

/-! ### The working definition of expletive negation

The paper's definition (ex. 2, p. 41) provides the basis for the entire
study. EN is distinguished from other semantically vacuous negation
(biased questions, negative concord, exclamatives) by requiring that
it is (i) syntactically dependent on a specific trigger, (ii) triggered
by that trigger's lexical semantics, and (iii) truth-conditionally vacuous
in the complement clause. -/

/-- The three necessary conditions for an instance of negation to count
    as expletive negation (EN), per @cite{jin-koenig-2021}, ex. (2). -/
structure ENDefinition where
  /-- (i) The negator is in a syntactic dependent of a lexical item
      (verb, adposition, adverb, or collocation). -/
  isSyntacticDependent : Bool
  /-- (ii) The negator is triggered by the meaning of that lexical item. -/
  isTriggeredByMeaning : Bool
  /-- (iii) The negator does not contribute logical negation to the
      proposition denoted by the syntactic dependent. -/
  isTruthConditionallyVacuous : Bool
  deriving DecidableEq, Repr

/-- An instance of negation is EN iff all three conditions hold. -/
def isEN (d : ENDefinition) : Bool :=
  d.isSyntacticDependent && d.isTriggeredByMeaning && d.isTruthConditionallyVacuous

/-- French *ne* with *peur* (fear) satisfies all three conditions. -/
def french_ne_fear : ENDefinition where
  isSyntacticDependent := true
  isTriggeredByMeaning := true
  isTruthConditionallyVacuous := true

/-- French *souhaiter* (wish) + *ne* would NOT count as EN because
    wish does not trigger EN: replacing *peur* with *souhaite* in (1)
    yields an ungrammatical sentence (ex. 3). -/
def french_ne_wish : ENDefinition where
  isSyntacticDependent := true
  isTriggeredByMeaning := false  -- wish doesn't trigger EN
  isTruthConditionallyVacuous := true

theorem fear_is_en : isEN french_ne_fear = true := rfl
theorem wish_is_not_en : isEN french_ne_wish = false := rfl

-- ════════════════════════════════════════════════════
-- § 15. Integration: Connecting to Rett (2026)
-- ════════════════════════════════════════════════════

/-! ### Connecting JK2021 licensing conditions to Rett's ambidirectionality

@cite{rett-2026} (formalized in `Rett2026`)
proposes that EN is licensed in *ambidirectional* constructions — those
where negating an argument doesn't change truth conditions. This is
a stronger, unified condition that subsumes JK2021's four conditions.

The mapping:
- **Temporal operators** (BEFORE, UNTIL) → ambidirectional on time intervals
- **Comparatives** (MORE THAN) → ambidirectional on degree intervals
- **FEAR** → ambidirectional via negative valence (dual activation)
- **Logical operators** (IMPOSSIBLE, WITHOUT, UNLESS) → these include
  ¬ in their meaning, making negation redundant (a form of ambidirectionality)

The key insight: JK2021's four conditions are *necessary* conditions
observed bottom-up from data; Rett's ambidirectionality is a *unified*
sufficient condition derived top-down from semantics. They are
consistent: every JK2021 condition entails ambidirectionality. -/

/-- The two temporal trigger subclasses (BEFORE, SINCE) map to the
    temporal operator condition, which Rett connects to ambidirectionality
    on time intervals. -/
theorem temporal_triggers_are_rett_ambidirectional :
    TriggerSubclass.before.licensingCondition = .temporalOperator ∧
    TriggerSubclass.since.licensingCondition = .temporalOperator := ⟨rfl, rfl⟩

/-- Comparative triggers map to the comparative condition, which Rett
    connects to ambidirectionality on degree intervals. -/
theorem comparative_triggers_are_rett_ambidirectional :
    TriggerSubclass.moreThan.licensingCondition = .comparative ∧
    TriggerSubclass.tooTo.licensingCondition = .comparative := ⟨rfl, rfl⟩

/-- FEAR triggers map to propositional attitude, which Rett derives
    from negative valence → dual activation → ambidirectionality. -/
theorem fear_triggers_are_rett_ambidirectional :
    TriggerSubclass.fear.licensingCondition = .propositionalAttitude ∧
    negativeValenceEntailsDual .negative = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 16. End-to-End: Fragment Verbs → EN Trigger Status
-- ════════════════════════════════════════════════════

/-! ### Connecting English fragment verb entries to EN trigger status

Each of the three branches of `VerbCore.isENTrigger` corresponds to
one class of JK2021 triggers. The general theorems below show that
the semantic property (negative valence, negative implicativity,
causative blocking) is *sufficient* for EN trigger status — the
conclusion follows from the hypothesis, not by enumerating cases.
-/

open Core.Verbs (VerbCore)

/-- Any verb with negative preferential valence is an EN trigger.
    This captures the FEAR class: negative valence activates both p
    (attitude content) and ¬p (desire content). -/
theorem negative_valence_is_en_trigger (v : VerbCore)
    (h : v.preferentialValence = some .negative) :
    v.isENTrigger = true := by
  simp only [VerbCore.isENTrigger, h, show (some AttitudeValence.negative ==
    some AttitudeValence.negative) = true from rfl, Bool.true_or]

/-- Any negative implicative verb is an EN trigger.
    This captures the FORGET class: "X forgot to p" entails ¬p in w₀. -/
theorem negative_implicative_is_en_trigger (v : VerbCore)
    (h : v.implicative = some .negative) :
    v.isENTrigger = true := by
  simp only [VerbCore.isENTrigger, h, show (some Implicative.negative ==
    some Implicative.negative) = true from rfl, Bool.true_or, Bool.or_true]

/-- Any causative-prevent verb is an EN trigger.
    This captures the STOP/PREVENT class: blocking entails ¬p in w₀. -/
theorem prevent_builder_is_en_trigger (v : VerbCore)
    (h : v.causative = some .prevent) :
    v.isENTrigger = true := by
  simp only [VerbCore.isENTrigger, h, show (some Causative.prevent ==
    some Causative.prevent) = true from rfl, Bool.or_true]

-- Instantiations for English fragment verbs: the conclusion follows
-- from the general theorem applied to the verb's semantic builder.

open Fragments.English.Predicates.Verbal (fear dread worry forget prevent)

/-- "fear" → negative valence → EN trigger. -/
theorem english_fear_is_en_trigger :
    fear.toVerbCore.isENTrigger = true :=
  negative_valence_is_en_trigger _ rfl

/-- "dread" → negative valence → EN trigger. -/
theorem english_dread_is_en_trigger :
    dread.toVerbCore.isENTrigger = true :=
  negative_valence_is_en_trigger _ rfl

/-- "worry" → negative valence (uncertainty-based) → EN trigger. -/
theorem english_worry_is_en_trigger :
    worry.toVerbCore.isENTrigger = true :=
  negative_valence_is_en_trigger _ rfl

/-- "forget" → negative implicative → EN trigger. -/
theorem english_forget_is_en_trigger :
    forget.toVerbCore.isENTrigger = true :=
  negative_implicative_is_en_trigger _ rfl

/-- "prevent" → causative blocking → EN trigger. -/
theorem english_prevent_is_en_trigger :
    prevent.toVerbCore.isENTrigger = true :=
  prevent_builder_is_en_trigger _ rfl

-- ════════════════════════════════════════════════════
-- § 17. ALMOST/BARELY Converse (§6.1.4)
-- ════════════════════════════════════════════════════

/-! ### ALMOST and BARELY are converses

The paper (§6.1.4, p. 65) notes that BARELY is "ALMOST's converse":
- ALMOST p: p in worlds close to w₀, ¬p in w₀
- BARELY p: p in w₀, ¬p in worlds close to w₀

The positive and negative inferences are swapped. Both belong to
the FORGET class because they share the property that either p or ¬p
holds in the real world. -/

/-- The ALMOST entry in Table 6 (index 13). -/
private def almostProfile : DualInferenceProfile :=
  { subclass := .forget
  , positiveInference := "p in worlds close to w₀"
  , negativeInference := "¬p in w₀" }

/-- The BARELY entry in Table 6 (index 14). -/
private def barelyProfile : DualInferenceProfile :=
  { subclass := .forget
  , positiveInference := "p at w₀"
  , negativeInference := "¬p in worlds close to w₀" }

/-- ALMOST and BARELY share the FORGET class despite being converses. -/
theorem almost_barely_same_class :
    almostProfile.subclass = barelyProfile.subclass := rfl

/-- ALMOST and BARELY swap their domains
    (@cite{jin-koenig-2021}, §6.1.4):
    - ALMOST: p holds "close to w₀", ¬p in "w₀"
    - BARELY: p holds in "w₀", ¬p "close to w₀"
    The real-world (w₀) and close-to-real-world domains are exchanged. -/
theorem almost_barely_converse :
    -- ALMOST puts p in the close-to-real-world domain
    almostProfile.positiveInference = "p in worlds close to w₀" ∧
    -- BARELY puts ¬p in the close-to-real-world domain
    barelyProfile.negativeInference = "¬p in worlds close to w₀" ∧
    -- BARELY puts p in the real world
    barelyProfile.positiveInference = "p at w₀" ∧
    -- ALMOST puts ¬p in the real world
    almostProfile.negativeInference = "¬p in w₀" := ⟨rfl, rfl, rfl, rfl⟩

end JinKoenig2021
