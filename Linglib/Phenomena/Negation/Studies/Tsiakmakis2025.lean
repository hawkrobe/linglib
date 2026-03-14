import Linglib.Phenomena.Negation.Studies.JinKoenig2021
import Linglib.Theories.Semantics.Modality.Kratzer
import Linglib.Fragments.Greek.Negation
import Linglib.Fragments.Italian.Negation

/-!
# Tsiakmakis (2025): On the Non-Homogeneity of Expletive Negation
@cite{tsiakmakis-2025}

Linguistics (2025). DOI: 10.1515/ling-2024-0063.

Expletive negation (EN) is not a uniform phenomenon. Greek distinguishes
two negation markers that appear in EN environments: the indicative
negator *dhen* (NEG₁) and the modal/subjunctive negator *min* (NEG₂).
These correspond to two fundamentally different kinds of EN:

1. **NEG₁ / Apparent EN hosts**: The negator is standard sentential
   negation (⟦NEG₁⟧ = λp.¬p). Its negative semantics is masked by
   independent factors — rhetoricity, verbal aspect, negative concord,
   or the semantics of the embedding operator.

2. **NEG₂ / EN hosts proper**: The negator is a biased epistemic modal.
   It retains the modal component of its negative counterpart but lacks
   negation: ⟦NEG₂⟧^g(w) = λp. ∀w' ∈ Best_g(w) : p(w').

The paper argues this bipartite classification extends cross-linguistically:
even in languages without overt morphological distinction (French *ne*,
Italian *non*), the two types can be diagnosed by NCI licensing,
co-occurrence with canonical negation, and syntactic position.

## Diagnostics for NEG₁ vs NEG₂

| Property                        | NEG₁ (apparent) | NEG₂ (proper) |
|---------------------------------|-----------------|----------------|
| Licenses NCIs (*tipota*)        | ✓               | ✗              |
| Co-occurs with canonical neg    | ✗ (double neg)  | ✓ (*min dhen*) |
| Syntactic position              | TP-internal     | Left periphery |
| Has modal semantic component    | ✗               | ✓ (Best worlds)|
| Negative truth-conditions       | ✓ (masked)      | ✗ (intrinsic)  |

## Revised EN Host Inventory (§5.12, ex. 95)

**Apparent EN hosts** (NEG₁):
i. Temporal expressions (*before*, *until*, *since*)
ii. Negative adverbials (*without*)
iii. Comparatives (*more ... than*)
iv. Optionally biased polar questions
v. Rhetorical questions
vi. Exclamatives

**EN hosts proper** (NEG₂):
i. Emotive doxastic predicates (*fear*, *worry*)
ii. Negative predicates (*forbid*, *deny*)
iii. Dubitative predicates (*doubt*)
iv. Biased questions
v. (Conditionals)
vi. (Free relatives — tentative)

## Connection to @cite{jin-koenig-2021}

The bipartite classification cross-cuts Jin & Koenig's trigger taxonomy:
their propositional attitude triggers (FEAR, DENY) map to NEG₂ (modal
semantics), while temporal and logical operator triggers (BEFORE,
WITHOUT, UNLESS) map to NEG₁ (standard negation masked). Comparative
triggers are classified as NEG₁ (negation is a spell-out of the
comparative operator's built-in negation). The FORGET class is
heterogeneous — some members pattern with NEG₂ (modal), others with
NEG₁ (factual ¬p in w₀).

## Connection to Kratzer Modality

NEG₂ is formally a Kratzer necessity operator with an ordering source:
⟦NEG₂⟧^g(w) = λp. ∀w' ∈ Best_g(w) : p(w'). The ordering source varies
by host:
- Fear predicates: deontic ordering (speaker's preferences)
- Negative predicates (*forbid*): deontic ordering (norms)
- Dubitative predicates: epistemic ordering (speaker's beliefs)
- Conditionals: circumstantial + deontic ordering
- Biased questions: epistemic ordering (speaker's bias)
-/

namespace Phenomena.Negation.Studies.Tsiakmakis2025

open Phenomena.Negation.Studies.JinKoenig2021
  (LicensingCondition TriggerSubclass DualInferenceProfile negativeValenceEntailsDual)
open Semantics.Attitudes.Intensional (World)
open Core.Proposition (BProp)
open Semantics.Modality.Kratzer
  (bestWorlds necessity ModalBase OrderingSource)
open Core.Modality (ModalFlavor)

-- ════════════════════════════════════════════════════
-- § 1. The NEG₁ / NEG₂ Distinction
-- ════════════════════════════════════════════════════

/-- The two types of expletive negation markers.

    Greek overtly distinguishes these: *dhen* = NEG₁, *min* = NEG₂.
    Other languages (French, Italian, Spanish) use the same surface
    form for both, but the distinction can be diagnosed by NCI
    licensing, co-occurrence with canonical negation, and
    syntactic position. -/
inductive NegatorType where
  /-- Standard sentential negation whose negative semantics is masked
      by independent factors (rhetoricity, aspect, NC, operator semantics).
      ⟦NEG₁⟧ = λp.¬p -/
  | neg1
  /-- Biased epistemic modal retaining the modal component of negative
      *min* but lacking negation.
      ⟦NEG₂⟧^g(w) = λp. ∀w' ∈ Best_g(w) : p(w') -/
  | neg2
  deriving DecidableEq, BEq, Repr

/-- NEG₁ semantics: standard sentential negation.

    ⟦NEG₁⟧ = λp.¬p (eq. 37, 70, 73, 79, 88, 91, 93) -/
def neg1Sem (p : World → Bool) : World → Bool :=
  λ w => !p w

/-- NEG₂ semantics: Kratzer necessity over Best worlds.

    ⟦NEG₂⟧^g(w) = λp. ∀w' ∈ Best_g(w) : p(w')  (eq. 58, 60, 63, 66, 94)

    This is exactly Kratzer's `necessity` operator. The ordering source
    varies by host (deontic for fear/forbid, epistemic for doubt/questions). -/
def neg2Sem (f : ModalBase) (g : OrderingSource) (p : BProp World)
    (w : World) : Bool :=
  necessity f g p w

/-- NEG₂ is formally identical to Kratzer necessity. -/
theorem neg2_is_kratzer_necessity (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    neg2Sem f g p w = necessity f g p w := rfl

-- ════════════════════════════════════════════════════
-- § 2. Diagnostics
-- ════════════════════════════════════════════════════

/-- Diagnostic properties that distinguish NEG₁ from NEG₂.

    Based on Greek evidence (§§2–4) and cross-linguistic extension (§5). -/
structure NegatorDiagnostics where
  negType : NegatorType
  /-- Can the marker license Negative Concord Items (NCIs)?
      NEG₁ (*dhen*) can license *tipota* 'nothing'; NEG₂ (*min*) cannot.
      (§4.1, ex. 40 vs 41; §4.2, ex. 46; §4.3, ex. 52) -/
  licensesNCIs : Bool
  /-- Can the marker co-occur with canonical sentential negation?
      NEG₂ (*min*) co-occurs with *dhen* (ex. 39, 41, 47, 53);
      NEG₁ (*dhen*) alone IS the canonical negation. -/
  cooccursWithCanonicalNeg : Bool
  /-- Is the marker merged in the left periphery (outside TP)?
      NEG₂ (*min*) merges high — informationally unmarked subjects
      cannot precede it (ex. 44, 48, 54).
      NEG₁ (*dhen*) is TP-internal. -/
  mergesInLeftPeriphery : Bool
  /-- Does the marker have a modal semantic component?
      NEG₂ involves an ordering source and Best worlds;
      NEG₁ is pure truth-functional negation. -/
  hasModalComponent : Bool
  deriving Repr

/-- Diagnostic profile for NEG₁ (Greek *dhen*). -/
def neg1Diagnostics : NegatorDiagnostics where
  negType := .neg1
  licensesNCIs := true
  cooccursWithCanonicalNeg := false
  mergesInLeftPeriphery := false
  hasModalComponent := false

/-- Diagnostic profile for NEG₂ (Greek *min*). -/
def neg2Diagnostics : NegatorDiagnostics where
  negType := .neg2
  licensesNCIs := false
  cooccursWithCanonicalNeg := true
  mergesInLeftPeriphery := true
  hasModalComponent := true

/-- NEG₁ and NEG₂ differ on every diagnostic. -/
theorem diagnostics_fully_distinguish :
    neg1Diagnostics.licensesNCIs ≠ neg2Diagnostics.licensesNCIs ∧
    neg1Diagnostics.cooccursWithCanonicalNeg ≠ neg2Diagnostics.cooccursWithCanonicalNeg ∧
    neg1Diagnostics.mergesInLeftPeriphery ≠ neg2Diagnostics.mergesInLeftPeriphery ∧
    neg1Diagnostics.hasModalComponent ≠ neg2Diagnostics.hasModalComponent :=
  ⟨by decide, by decide, by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Cross-Classification with Jin & Koenig 2021
-- ════════════════════════════════════════════════════

/-! ### Mapping trigger subclasses to negator types

Each of @cite{jin-koenig-2021}'s trigger subclasses is classified as
hosting NEG₁ or NEG₂. This cross-cuts their licensing condition
taxonomy: the propositional attitude condition spans both types
(FEAR → NEG₂, but FORGET members vary). -/

/-- Assign each trigger subclass to its negator type.

    **NEG₂ (proper EN)**: Triggers whose complement involves a modal
    ordering source (fear, regret, deny).

    **NEG₁ (apparent EN)**: Triggers where standard negation is masked
    (temporals, logical operators, comparatives).

    **FORGET**: Classified as NEG₁ because the negative inference is
    "¬p in w₀" (the real world) — factual negation, not modal.
    (§6.1.4 of @cite{jin-koenig-2021}: "semantically heterogeneous";
    §5.12 of @cite{tsiakmakis-2025}: not listed as a proper EN host.) -/
def negatorType : TriggerSubclass → NegatorType
  -- Propositional attitude triggers with modal ordering → NEG₂
  | .fear       => .neg2    -- deontic ordering (speaker's desires; §5.1, eq. 60)
  | .regret     => .neg2    -- deontic ordering (behavioral standards; §6.1.2 of @cite{jin-koenig-2021})
  | .deny       => .neg2    -- deontic ordering (speaker's beliefs; §5.2, eq. 63)
  -- FORGET: factual ¬p in w₀ → NEG₁
  | .forget     => .neg1
  -- Temporal operators: standard negation masked by aspect → NEG₁
  | .before     => .neg1
  | .cannotWait => .neg1
  | .since      => .neg1
  | .rarely     => .neg1
  -- Logical operators: standard negation is part of meaning → NEG₁
  | .impossible => .neg1
  | .without    => .neg1
  | .unless     => .neg1
  -- Comparatives: negation is spell-out of comparative operator → NEG₁
  | .moreThan    => .neg1
  | .differentThan => .neg1
  | .tooTo       => .neg1

-- ════════════════════════════════════════════════════
-- § 4. The Revised Host Inventory (§5.12, ex. 95)
-- ════════════════════════════════════════════════════

/-- EN host categories from the revised inventory (§5.12, ex. 95).

    "Apparent" hosts feature NEG₁ (standard negation masked);
    "proper" hosts feature NEG₂ (modal, intrinsically non-negative). -/
inductive ENHostCategory where
  -- Apparent EN hosts (NEG₁)
  | temporalExpressions      -- before, until, since (§5.4)
  | negativeAdverbials        -- without, almost (§5.5)
  | comparatives              -- more...than (§5.7)
  | optionallyBiasedPolarQs   -- optionally biased polar questions (§5.8)
  | rhetoricalQuestions        -- rhetorical questions (§5.9)
  | exclamatives               -- negative exclamatives (§5.10)
  -- EN hosts proper (NEG₂)
  | emotiveDoxasticPredicates  -- fear, worry (§5.1)
  | negativePredicates         -- forbid, deny (§5.2)
  | dubitativePredicates       -- doubt (§5.3)
  | biasedQuestions            -- biased polar questions (§5.8)
  | conditionals               -- if-conditionals (§5.6, tentative)
  | freeRelatives              -- free relatives (§5.11, tentative)
  deriving DecidableEq, BEq, Repr

/-- Each host category's negator type. -/
def ENHostCategory.negatorType : ENHostCategory → NegatorType
  | .temporalExpressions    => .neg1
  | .negativeAdverbials     => .neg1
  | .comparatives           => .neg1
  | .optionallyBiasedPolarQs => .neg1
  | .rhetoricalQuestions    => .neg1
  | .exclamatives           => .neg1
  | .emotiveDoxasticPredicates => .neg2
  | .negativePredicates     => .neg2
  | .dubitativePredicates   => .neg2
  | .biasedQuestions        => .neg2
  | .conditionals           => .neg2
  | .freeRelatives          => .neg2

/-- All apparent hosts are NEG₁. -/
theorem apparent_hosts_are_neg1 :
    [ENHostCategory.temporalExpressions, .negativeAdverbials, .comparatives,
     .optionallyBiasedPolarQs, .rhetoricalQuestions, .exclamatives].all
      (·.negatorType == .neg1) = true := rfl

/-- All proper hosts are NEG₂. -/
theorem proper_hosts_are_neg2 :
    [ENHostCategory.emotiveDoxasticPredicates, .negativePredicates,
     .dubitativePredicates, .biasedQuestions, .conditionals,
     .freeRelatives].all
      (·.negatorType == .neg2) = true := rfl

-- ════════════════════════════════════════════════════
-- § 5. Cross-Linguistic Evidence
-- ════════════════════════════════════════════════════

/-! ### Negator classification across languages

The NEG₁/NEG₂ distinction is overt in Greek (*dhen* vs *min*) and
Classical Greek (*ou(k)* vs *me:*). In other languages, the same
surface form may instantiate either type depending on context.

Cross-linguistic evidence from §5:
- **French**: *ne* is NEG₁ in temporals/comparatives, NEG₂ in
  fear-predicate complements (@cite{tahar-2022})
- **Italian**: *non* is NEG₁ in *finché*-clauses (§5.4) and
  comparatives (§5.7), NEG₂ tentatively in fear contexts
- **Spanish**: *no* is NEG₁ in comparatives, NEG₂ in *dudar* complements
- **Classical Greek**: *ou(k)* = NEG₁, *me:* = NEG₂ (§5.1, §5.3)
- **Latin**: *non* = NEG₁ in questions (§5.8), *-ne* = NEG₂ in
  questions (§5.8, ex. 84) -/

/-- A cross-linguistic EN negator datum. -/
structure NegatorDatum where
  /-- Language -/
  language : String
  /-- Surface form of the negator -/
  form : String
  /-- NEG₁ or NEG₂ -/
  negType : NegatorType
  /-- EN host category where this negator appears -/
  hostCategory : ENHostCategory
  /-- Brief description of the construction -/
  construction : String
  deriving Repr

/-- Greek *dhen* in exclamatives: ⟦dhen⟧ = λp.¬p, masked by extreme-degree
    semantics (§3.1, ex. 22–24). -/
def greekDhenExclamative : NegatorDatum :=
  { language := "Greek", form := Fragments.Greek.Negation.dhen.form, negType := .neg1
  , hostCategory := .exclamatives
  , construction := "negative exclamatives (§3.1, ex. 22–24)" }

/-- Greek *dhen* in negative rhetorical questions: ⟦dhen⟧ = λp.¬p,
    masked by rhetoricity / polarity reversal (§3.2, ex. 26–29; eq. 30). -/
def greekDhenRhetoricalQ : NegatorDatum :=
  { language := "Greek", form := Fragments.Greek.Negation.dhen.form, negType := .neg1
  , hostCategory := .rhetoricalQuestions
  , construction := "negative rhetorical questions (§3.2, ex. 26–29)" }

/-- Greek *dhen* in preposed negation questions: ⟦dhen⟧ = λp.¬p,
    masked by speaker's epistemic bias (§3.3, ex. 31–36; eq. 36–37). -/
def greekDhenPolarQ : NegatorDatum :=
  { language := "Greek", form := Fragments.Greek.Negation.dhen.form, negType := .neg1
  , hostCategory := .optionallyBiasedPolarQs
  , construction := "preposed negation questions (§3.3, ex. 31–36)" }

def greekMinFear : NegatorDatum :=
  { language := "Greek", form := Fragments.Greek.Negation.min.form, negType := .neg2
  , hostCategory := .emotiveDoxasticPredicates
  , construction := "fear-predicate complements (§4.1, ex. 38)" }

def greekMinConditional : NegatorDatum :=
  { language := "Greek", form := Fragments.Greek.Negation.min.form, negType := .neg2
  , hostCategory := .conditionals
  , construction := "conditional antecedents (§4.2, ex. 45)" }

def greekMinQuestion : NegatorDatum :=
  { language := "Greek", form := Fragments.Greek.Negation.min.form, negType := .neg2
  , hostCategory := .biasedQuestions
  , construction := "biased polar questions (§4.3, ex. 51)" }

def frenchNeFear : NegatorDatum :=
  { language := "French", form := "ne", negType := .neg2
  , hostCategory := .emotiveDoxasticPredicates
  , construction := "fear-predicate complements: craindre que...ne (§5.1, ex. 59)" }

def frenchNeForbid : NegatorDatum :=
  { language := "French", form := "ne", negType := .neg2
  , hostCategory := .negativePredicates
  , construction := "negative-predicate complements: défendre que...ne (§5.2, ex. 62)" }

def italianNonTemporal : NegatorDatum :=
  { language := "Italian", form := Fragments.Italian.Negation.negMarker, negType := .neg1
  , hostCategory := .temporalExpressions
  , construction := "finché non (until; §5.4, ex. 68)" }

def italianNonComparative : NegatorDatum :=
  { language := "Italian", form := Fragments.Italian.Negation.negMarker, negType := .neg1
  , hostCategory := .comparatives
  , construction := "più...di quanto non (more...than; §5.7, ex. 77)" }

def spanishNoDubitative : NegatorDatum :=
  { language := "Spanish", form := "no", negType := .neg2
  , hostCategory := .dubitativePredicates
  , construction := "dudar que...no (doubt that; §5.3, ex. 65)" }

def classicalGreekMeDubitative : NegatorDatum :=
  { language := "Classical Greek", form := "me:", negType := .neg2
  , hostCategory := .dubitativePredicates
  , construction := "apisteis me: (you doubt; §5.3, ex. 67)" }

def hebrewLoFear : NegatorDatum :=
  { language := "Hebrew", form := "lo", negType := .neg2
  , hostCategory := .emotiveDoxasticPredicates
  , construction := "paxadeti še-lo (I feared that; §5.1, ex. 61)" }

def latinNeQuestion : NegatorDatum :=
  { language := "Latin", form := "-ne", negType := .neg2
  , hostCategory := .biasedQuestions
  , construction := "non -ne animadvertis? (don't you observe?; §5.8, ex. 84)" }

def allNegatorData : List NegatorDatum :=
  [ greekDhenExclamative, greekDhenRhetoricalQ, greekDhenPolarQ
  , greekMinFear, greekMinConditional, greekMinQuestion
  , frenchNeFear, frenchNeForbid
  , italianNonTemporal, italianNonComparative
  , spanishNoDubitative, classicalGreekMeDubitative
  , hebrewLoFear, latinNeQuestion ]

/-- Greek *min* always corresponds to NEG₂. -/
theorem greek_min_is_neg2 :
    (allNegatorData.filter (·.form == "min")).all
      (·.negType == .neg2) = true := by native_decide

/-- Greek *dhen* always corresponds to NEG₁. -/
theorem greek_dhen_is_neg1 :
    (allNegatorData.filter (·.form == "dhen")).all
      (·.negType == .neg1) = true := by native_decide

/-- Italian *non* in temporals and comparatives is NEG₁. -/
theorem italian_non_is_neg1 :
    (allNegatorData.filter (·.form == "non")).all
      (·.negType == .neg1) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 6. Bridge Theorems
-- ════════════════════════════════════════════════════

/-! ### Connecting negator types to licensing conditions

The central structural claim: NEG₂ hosts correspond to
@cite{jin-koenig-2021}'s propositional attitude licensing condition,
while NEG₁ hosts correspond to temporal, logical, and comparative
conditions. -/

/-- All NEG₂ trigger subclasses have the propositional attitude
    licensing condition. This is non-trivial: it shows that the
    negator-type classification aligns with the licensing-condition
    classification for the modal (NEG₂) cases. -/
theorem neg2_triggers_are_propositional_attitude :
    [TriggerSubclass.fear, .regret, .deny].all
      (λ t => negatorType t == .neg2 && t.licensingCondition == .propositionalAttitude)
    = true := rfl

/-- All temporal triggers are NEG₁. -/
theorem temporal_triggers_are_neg1 :
    [TriggerSubclass.before, .cannotWait, .since, .rarely].all
      (fun t => negatorType t == .neg1) = true := rfl

/-- All logical operator triggers are NEG₁. -/
theorem logical_triggers_are_neg1 :
    [TriggerSubclass.impossible, .without, .unless].all
      (fun t => negatorType t == .neg1) = true := rfl

/-- All comparative triggers are NEG₁. -/
theorem comparative_triggers_are_neg1 :
    [TriggerSubclass.moreThan, .differentThan, .tooTo].all
      (fun t => negatorType t == .neg1) = true := rfl

/-- NEG₁ triggers are exactly the non-propositional-attitude triggers
    plus FORGET (the heterogeneous attitude class). -/
theorem neg1_iff_not_core_attitude (t : TriggerSubclass) :
    negatorType t = .neg1 ↔
    (t.licensingCondition ≠ .propositionalAttitude ∨ t = .forget) := by
  cases t <;> simp [negatorType, TriggerSubclass.licensingCondition]

-- ════════════════════════════════════════════════════
-- § 7. NEG₂ Ordering Sources by Host
-- ════════════════════════════════════════════════════

/-! ### Modal flavor of NEG₂ across hosts

All NEG₂ hosts share the formal semantics ⟦NEG₂⟧ = λp. ∀w' ∈ Best_g(w) : p(w'),
but the **ordering source** g varies:

- Fear predicates: deontic (desires/preferences) — p worlds are ranked
  higher than ¬p worlds by the speaker's preferences (§5.1, eq. 60)
- Negative predicates (*forbid*): deontic (norms/standards) — p worlds
  ranked higher by social/moral norms (§5.2, eq. 63: "deontically modal")
- Dubitative predicates (*doubt*): epistemic (beliefs) — p worlds ranked
  higher by the speaker's epistemic state (§5.3, eq. 66)
- Conditionals: circumstantial + habit/norm (§4.2, eq. 50) — p worlds
  ranked by what has happened before
- Biased questions: epistemic (speaker's prior belief) — p worlds
  ranked higher by positive speaker bias (§4.3, eq. 56) -/

/-- Each proper EN host category maps to a Kratzer modal flavor.

    NEG₂'s ordering source varies by host; the flavor tag is exactly
    `Core.Modality.ModalFlavor`, reused here rather than duplicated.
    "Habitual" (conditionals) maps to `.circumstantial` — both concern
    facts and what has happened, following Kratzer's subsumption. -/
def ENHostCategory.orderingFlavor : ENHostCategory → Option ModalFlavor
  | .emotiveDoxasticPredicates => some .deontic         -- desires/preferences (§5.1)
  | .negativePredicates        => some .deontic         -- norms/standards (§5.2)
  | .dubitativePredicates      => some .epistemic       -- beliefs (§5.3)
  | .biasedQuestions           => some .epistemic       -- speaker's prior (§4.3)
  | .conditionals              => some .circumstantial  -- habitual/factual (§4.2)
  | .freeRelatives             => some .epistemic       -- tentative
  -- Apparent hosts have no ordering source
  | .temporalExpressions       => none
  | .negativeAdverbials        => none
  | .comparatives              => none
  | .optionallyBiasedPolarQs   => none
  | .rhetoricalQuestions        => none
  | .exclamatives              => none

/-- NEG₂ hosts always have an ordering flavor; NEG₁ hosts never do. -/
theorem ordering_flavor_iff_neg2 (h : ENHostCategory) :
    h.orderingFlavor.isSome = (h.negatorType == .neg2) := by
  cases h <;> rfl

-- ════════════════════════════════════════════════════
-- § 8. Masking Mechanisms for NEG₁
-- ════════════════════════════════════════════════════

/-! ### Why NEG₁ appears expletive

NEG₁ has genuine negative semantics (λp.¬p), but its negativity is
**masked** — obscured by independent factors. The masking mechanism
differs by host type (§3.4, §5.4, §5.5, §5.7, §5.9, §5.10):

- Temporal expressions: negation obscured by verbal aspect (achievement
  verbs make the endpoint coincide, so the *non*-variant and the bare
  variant are truth-conditionally equivalent; @cite{tovena-1996}, §5.4)
- Negative adverbials (*without*): Negative Concord between the
  adverbial and the EN marker (§5.5)
- Comparatives: negation is a spell-out of the comparative operator's
  built-in negation (∃d. tall(G,d) ∧ ¬tall(P,d); §5.7)
- Rhetorical questions: polarity reversal from rhetoricity is
  independent of the negation marker (§5.9)
- Exclamatives: polarity reversal from extreme-degree semantics (§5.10)
- Optionally biased polar questions: speaker's epistemic bias masks
  the negative meaning (§3.3) -/

/-- The mechanism that masks NEG₁'s negative semantics. -/
inductive MaskingMechanism where
  /-- Verbal aspect makes negated/non-negated variants equivalent
      (temporal expressions with achievement verbs; @cite{tovena-1996}) -/
  | verbalAspect
  /-- Negative Concord between embedding operator and NEG₁
      (negative adverbials; §5.5) -/
  | negativeConcord
  /-- Negation is spell-out of operator's built-in negation
      (comparatives: ∃d. Q(Y,d) ∧ ¬Q(Z,d); §5.7) -/
  | operatorSpellOut
  /-- Polarity reversal from rhetoricity
      (rhetorical questions; §5.9) -/
  | rhetoricity
  /-- Extreme-degree semantics triggers reversal
      (exclamatives; §5.10) -/
  | extremeDegree
  /-- Speaker's epistemic bias overrides negative reading
      (optionally biased polar questions; §3.3) -/
  | speakerBias
  deriving DecidableEq, BEq, Repr

/-- Each apparent (NEG₁) host has a specific masking mechanism. -/
def ENHostCategory.maskingMechanism : ENHostCategory → Option MaskingMechanism
  | .temporalExpressions     => some .verbalAspect
  | .negativeAdverbials      => some .negativeConcord
  | .comparatives            => some .operatorSpellOut
  | .rhetoricalQuestions     => some .rhetoricity
  | .exclamatives            => some .extremeDegree
  | .optionallyBiasedPolarQs => some .speakerBias
  -- Proper EN hosts have no masking mechanism (NEG₂ is intrinsically non-negative)
  | .emotiveDoxasticPredicates => none
  | .negativePredicates       => none
  | .dubitativePredicates     => none
  | .biasedQuestions          => none
  | .conditionals             => none
  | .freeRelatives            => none

/-- NEG₁ hosts always have a masking mechanism; NEG₂ hosts never do.
    This is the structural complement of `ordering_flavor_iff_neg2`. -/
theorem masking_mechanism_iff_neg1 (h : ENHostCategory) :
    h.maskingMechanism.isSome = (h.negatorType == .neg1) := by
  cases h <;> rfl

/-- The two classifications are complementary: every host has either
    an ordering flavor (NEG₂) or a masking mechanism (NEG₁), never both. -/
theorem neg1_neg2_complementary (h : ENHostCategory) :
    h.orderingFlavor.isSome = !h.maskingMechanism.isSome := by
  cases h <;> rfl

-- ════════════════════════════════════════════════════
-- § 9. Bridge to Rett 2026
-- ════════════════════════════════════════════════════

/-! ### Non-homogeneity refines ambidirectionality

The ambidirectionality generalization (formalized in `Rett2026.lean`)
predicts EN licensing at the construction level. The non-homogeneity
claim here refines this by distinguishing the *nature* of the negation:

- In **NEG₁** hosts (before, than), ambidirectionality explains why
  standard negation is truth-conditionally vacuous → appears "expletive"
- In **NEG₂** hosts (fear, doubt), the marker is not negation at all
  but a modal — so "ambidirectionality" applies to the modal component
  (both p and ¬p worlds are relevant to the ordering)

The two accounts are compatible: the ambidirectionality generalization
covers the distributional pattern (where EN appears), while the
non-homogeneity distinction explains the mechanism (what kind of
marker appears).

**Note**: The formal bridge theorem mapping `ENConstruction` to
`ENHostCategory` lives in `Rett2026.lean` (chronological direction:
Rett 2026 can reference Tsiakmakis 2025, not vice versa). -/

-- ════════════════════════════════════════════════════
-- § 10. Bridge to Preferential Attitudes
-- ════════════════════════════════════════════════════

/-! ### Fear predicates: negative valence → dual inference → NEG₂

The connection between NEG₂ classification of fear predicates and
@cite{villalta-2008}'s negative valence, mediated by @cite{jin-koenig-2021}:

1. Fear has negative valence (Preferential.lean)
2. Negative valence → dual inference (@cite{jin-koenig-2021} §5.5, §6.1.1)
3. Propositional attitude licensing condition (@cite{jin-koenig-2021} (13a))
4. NEG₂ classification with deontic ordering (@cite{tsiakmakis-2025} §5.1, eq. 60)

This is a four-layer argumentation chain connecting attitude semantics
to the negator-type classification. -/

/-- Fear predicates: the full chain from negative valence to NEG₂.

    1. `negativeValenceEntailsDual .negative = true` (valence → dual inference)
    2. `fear.licensingCondition = .propositionalAttitude` (J&K licensing)
    3. `negatorType .fear = .neg2` (Tsiakmakis classification)
    4. `emotiveDoxasticPredicates.orderingFlavor = some .deontic` (modal flavor) -/
theorem fear_neg2_from_negative_valence :
    negativeValenceEntailsDual .negative = true ∧
    TriggerSubclass.fear.licensingCondition = .propositionalAttitude ∧
    negatorType .fear = .neg2 ∧
    ENHostCategory.emotiveDoxasticPredicates.orderingFlavor = some .deontic :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Deny predicates: NEG₂ with deontic ordering.

    DENY triggers entail that X believes ¬p or says ¬p
    (@cite{jin-koenig-2021} §6.1.3). This propositional attitude
    licensing condition maps to NEG₂ with a deontic ordering source
    (the speaker's beliefs about what the denier believes). -/
theorem deny_neg2_with_deontic_ordering :
    negatorType .deny = .neg2 ∧
    TriggerSubclass.deny.licensingCondition = .propositionalAttitude ∧
    ENHostCategory.negativePredicates.orderingFlavor = some .deontic :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. Summary Consistency Checks
-- ════════════════════════════════════════════════════

/-- The cross-linguistic data is internally consistent: each datum's
    host category matches its negator type. -/
theorem data_consistent_with_classification :
    allNegatorData.all (λ d => d.negType == d.hostCategory.negatorType)
    = true := by native_decide

/-- Every trigger subclass is classified (total function check). -/
theorem negatorType_total :
    [TriggerSubclass.fear, .regret, .deny, .forget,
     .before, .cannotWait, .since, .rarely,
     .impossible, .without, .unless,
     .moreThan, .differentThan, .tooTo].length = 14 := rfl

/-- The 14 trigger subclasses split 3 NEG₂ + 11 NEG₁. -/
theorem negatorType_counts :
    ([TriggerSubclass.fear, .regret, .deny, .forget,
      .before, .cannotWait, .since, .rarely,
      .impossible, .without, .unless,
      .moreThan, .differentThan, .tooTo].filter
        (fun t => negatorType t == .neg2)).length = 3 ∧
    ([TriggerSubclass.fear, .regret, .deny, .forget,
      .before, .cannotWait, .since, .rarely,
      .impossible, .without, .unless,
      .moreThan, .differentThan, .tooTo].filter
        (fun t => negatorType t == .neg1)).length = 11 := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════
-- § 12. NEG₂ / NEG₁ Decomposition
-- ════════════════════════════════════════════════════

/-! ### Negative *min* = modal ∘ negation

The paper's central formal insight: negative *min* (eq. 13) differs from
expletive *min* (eq. 58) only by the presence of negation inside the modal.

- ⟦min_negative⟧(p)(w) = ∀w' ∈ Best. **¬**p(w') = NEG₂(NEG₁(p))(w)
- ⟦min_expletive⟧(p)(w) = ∀w' ∈ Best. p(w') = NEG₂(p)(w)

Expletive *min* is therefore negative *min* with the negation stripped out.
Equivalently, feeding ¬p to negative *min* cancels the double negation
and yields expletive *min*'s semantics. -/

/-- Negative *min*: modal necessity over ¬p (eq. 13). -/
def negativeMinSem (f : ModalBase) (g : OrderingSource) (p : BProp World)
    (w : World) : Bool :=
  neg2Sem f g (neg1Sem p) w

/-- Negative *min* decomposes as NEG₂ ∘ NEG₁. -/
theorem negative_min_is_modal_of_negation (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    negativeMinSem f g p w = neg2Sem f g (neg1Sem p) w := rfl

/-- Expletive *min* = negative *min* with double negation cancelled:
    ⟦NEG₂⟧(p) = negativeMin(¬p). Feeding ¬p into negative *min*
    cancels the inner negation (!!p = p), recovering expletive semantics. -/
theorem expletive_from_negative_double_neg (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    neg2Sem f g p w = negativeMinSem f g (neg1Sem p) w := by
  simp only [negativeMinSem, neg2Sem, necessity]
  congr 1; ext w'; exact (Bool.not_not (p w')).symm

-- ════════════════════════════════════════════════════
-- § 13. Fragment Grounding
-- ════════════════════════════════════════════════════

/-! ### Greek and Italian data derive from fragment entries

The `NegatorDatum` records for Greek and Italian derive their surface
forms from `Fragments.Greek.Negation` and `Fragments.Italian.Negation`
respectively — the connection is true by construction, not by bridge
theorem. -/

/-- Greek *dhen* data derives its form from the Greek negation fragment. -/
theorem greek_dhen_form_grounded :
    greekDhenExclamative.form = Fragments.Greek.Negation.dhen.form := rfl

/-- Greek *min* data derives its form from the Greek negation fragment. -/
theorem greek_min_form_grounded :
    greekMinFear.form = Fragments.Greek.Negation.min.form := rfl

/-- Italian *non* data derives its form from the Italian negation fragment. -/
theorem italian_non_form_grounded :
    italianNonTemporal.form = Fragments.Italian.Negation.negMarker := rfl

end Phenomena.Negation.Studies.Tsiakmakis2025
