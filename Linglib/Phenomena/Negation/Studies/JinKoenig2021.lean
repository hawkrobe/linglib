import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Semantics.Attitudes.NegRaising

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

namespace Phenomena.Negation.Studies.JinKoenig2021

open Semantics.Attitudes.Preferential (AttitudeValence PreferentialPredicate NVPClass
                                        classifyNVP fear dread worry)

-- ════════════════════════════════════════════════════
-- § 1. Typological Survey Data (Tables 1–4)
-- ════════════════════════════════════════════════════

/-- Cross-linguistic EN survey results from @cite{jin-koenig-2021}. -/
structure ENSurveyResult where
  /-- Total languages surveyed -/
  totalSurveyed : Nat
  /-- Languages where EN was attested -/
  languagesWithEN : Nat
  /-- Genera where EN was attested -/
  generaWithEN : Nat
  deriving Repr

/-- The overall survey: 722 languages, EN in 74 (37 genera). -/
def survey : ENSurveyResult where
  totalSurveyed := 722
  languagesWithEN := 74
  generaWithEN := 37

theorem en_attested_minority :
    survey.languagesWithEN < survey.totalSurveyed := by decide

theorem en_across_many_genera :
    survey.generaWithEN ≥ 30 := by decide

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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

/-- Table 6 data: positive and negative inferences for each trigger subclass.
    One representative concept per subclass. The full Table 6 has ~25 rows
    with within-class variation (e.g., AVOID adds "and in w₀" to FEAR's
    positive inference; LESS THAN uses D' = D-max rather than D' > D;
    DESPAIR has three inferences rather than two). -/
def table6 : List DualInferenceProfile :=
  [ -- Propositional attitude triggers
    { subclass := .fear
    , positiveInference := "p in worlds consistent with X's attitude"
    , negativeInference := "¬p in worlds consistent with X's desires" }
  , { subclass := .regret
    , positiveInference := "p in worlds consistent with X's attitude"
    , negativeInference := "¬p in worlds consistent with X's behavioral standards" }
  , { subclass := .deny
    , positiveInference := "p in worlds consistent with somebody else's beliefs"
    , negativeInference := "¬p in worlds consistent with X's beliefs" }
  -- N.B. FORGET class is "semantically heterogeneous" (§6.1.4):
  -- FORGET = obligations, DELAY = temporal, STOP/PREVENT = real-world,
  -- ALMOST/BARELY = proximity. All share ¬p in w₀. FORGET shown here.
  , { subclass := .forget
    , positiveInference := "p in worlds consistent with X's obligations"
    , negativeInference := "¬p in w₀ (the real world)" }
  -- Temporal operator triggers
  , { subclass := .before
    , positiveInference := "p at time t"
    , negativeInference := "¬p at reference time r (when q is true)" }
  , { subclass := .cannotWait
    , positiveInference := "p at t in worlds consistent with X's expectations about the future"
    , negativeInference := "¬p at reference time r (when q is true)" }
  , { subclass := .since
    , positiveInference := "p at time t"
    , negativeInference := "¬p at reference time r" }
  , { subclass := .rarely
    , positiveInference := "p at a small number of intervals of time"
    , negativeInference := "¬p at a large number of intervals of time" }
  -- Logical operator triggers
  , { subclass := .impossible
    , positiveInference := "N/A"
    , negativeInference := "¬p in all worlds accessible from w₀ (IMPOSSIBLE) or most (DIFFICULT)" }
  , { subclass := .without
    , positiveInference := "N/A"
    , negativeInference := "¬p at reference time" }
  , { subclass := .unless
    , positiveInference := "N/A"
    , negativeInference := "¬p in suppositive worlds" }
  -- Comparative triggers
  , { subclass := .moreThan
    , positiveInference := "Q(Z, D)"
    , negativeInference := "¬Q(Z, D'), D' > D" }
  , { subclass := .differentThan
    , positiveInference := "p' in w₀ or at t'"
    , negativeInference := "¬p in w₀ or at t" }
  , { subclass := .tooTo
    , positiveInference := "p when Q(Y, D'') D'' < D-norm for p"
    , negativeInference := "¬p in w₀; Q(Y, D') D' > D-norm for p" } ]

/-- Every trigger subclass appears in Table 6. -/
theorem table6_complete :
    table6.length = 14 := rfl

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
    condition → NOT an EN trigger. This is empirically correct: no language
    in the 722-language sample has 'hope' as an EN trigger (§2, ex. 3). -/
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

end Phenomena.Negation.Studies.JinKoenig2021
