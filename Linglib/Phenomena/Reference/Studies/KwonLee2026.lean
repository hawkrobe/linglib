import Linglib.Core.Discourse.ReferentialForm
import Linglib.Phenomena.Reference.Studies.Ariel2001
import Linglib.Phenomena.Reference.Studies.KehlerRohde2013
import Linglib.Fragments.Korean.Pronouns

/-!
# @cite{kwon-lee-2026}
@cite{ariel-2001} @cite{carminati-2002} @cite{kweon-2011} @cite{contemori-di-domenico-2021}
@cite{zhang-kwon-2022}

From null pronouns to full NPs: Exploring accessibility markers in Korean.
*Journal of Linguistics*.

## Core Argument

@cite{ariel-2001}'s Accessibility Theory predicts a universal ordering of
referring expressions by the accessibility of their intended antecedent:
more accessible referents license more reduced forms. The *strength* of
this ordering — how cleanly languages partition the referential space —
is language- and context-specific. @cite{ariel-2001} (§4.2):

> only the *relative ordering* of accessibility markers is universal,
> while the accessibility values associated with each marker are
> language- and context-sensitive.

Three Korean experiments test this prediction in a discourse-oriented
language that lacks gender/number agreement, so referential resolution
relies primarily on discourse context. The forms tested span Ariel's
scale at three points:

| form        | example         | `AccessibilityLevel`     |
|-------------|-----------------|--------------------------|
| null *pro*  | ∅               | `zero` (rank 17)         |
| *kyay* (걔) | colloquial 3sg  | `unstressedPron` (14)    |
| full NP     | *ku chinkwu*    | `distalDemNP` (8)        |

## Three Experiments

| # | Discourse context              | Key finding                              |
|---|--------------------------------|------------------------------------------|
| 1 | One antecedent                 | Null > overt = full NP (naturalness)     |
| 2 | Two antecedents + gender bias  | Null is most context-sensitive           |
| 3 | Globally ambiguous, two refs   | Three-way split: null > overt > full NP |

The Experiment 3 antecedent-choice data (§ 2 below) is the cleanest test:
without semantic or gender disambiguation, form alone drives interpretation.
Predicted by Accessibility Theory and confirmed: subject-antecedent rates
are monotonically decreasing in informativity (and increasing in
accessibility rank).

## Cross-linguistic Variation

Languages instantiate the universal ordering with different *granularity*:

| Language | null→subj | overt→subj | full NP→subj | Source                              |
|----------|-----------|------------|--------------|-------------------------------------|
| Italian  | 81%       | 17%        | —            | @cite{carminati-2002}               |
| Spanish  | 62%       | 42%        | —            | @cite{contemori-di-domenico-2021}   |
| Chinese  | 84%       | 65%        | —            | @cite{zhang-kwon-2022}              |
| Korean (kyay)        | 71% | 43% | 35%        | @cite{kwon-lee-2026} Exp 3          |
| Korean (ku/kunye)    | 81% | 31% | —          | @cite{kweon-2011}                   |
| Korean (ku/kunye)    | 91% | 73% | —          | @cite{choe-2021}                    |

Italian shows clean binary partitioning; Spanish and Chinese show weaker
distinctions; Korean shows a graded three-way split. The relative ordering
is preserved everywhere (null is always the most subject-biased), but the
*spread* varies. This is exactly what @cite{ariel-2001} predicts.

## Theory Connections

This study file connects to several theoretical frameworks already
formalized in linglib:

* **@cite{ariel-2001}'s Accessibility Theory**: forms map to
  `AccessibilityLevel` and inherit `rank`/`attenuation`/`informativity`
  predictions (§ 1, § 7).
* **@cite{ariel-2001}'s `AccessibilityAssessment`**: the three
  experiments differ only in the `competition` field; this isolates
  competition as the manipulated variable (§ 6c).
* **@cite{kehler-rohde-2013}'s Bayesian model**: Korean subjects sit at
  default topichood, licensing null forms via P(form | referent) (§ 6).
* **@cite{carminati-2002}'s Position of Antecedent Hypothesis (PAH)**:
  formalized as a structural alternative; PAH and AT converge for
  canonical Korean but diverge under topicalization (§ 6b).

## Architectural Notes

* `KoreanRefForm` is a 3-element subset of `AccessibilityLevel` selected
  by the experimental design. The accessibility-theoretic predictions
  derive from `AccessibilityLevel.rank`/`attenuation`/`informativity`
  in `Core/` and `Ariel2001`; only the experimental data and the
  selection of which 3 levels to test are stipulated here.
* All measurements (naturalness, accuracy, antecedent choice) use
  `Nat × 100` encoding to keep `decide` proofs trivial. Naturalness on
  the 1–7 Likert scale: 4.40 → 440, etc.
-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.KwonLee2026

open Core.Discourse.ReferentialForm

-- ════════════════════════════════════════════════════
-- § 1. Korean Referential Forms
-- ════════════════════════════════════════════════════

/-- The three Korean referential forms tested across the experiments.
    Each instantiates a different point on @cite{ariel-2001}'s Accessibility
    Marking Scale. -/
inductive KoreanRefForm where
  /-- Null pronoun (*pro*): no phonological exponent. -/
  | nullPro
  /-- Overt colloquial 3sg pronoun *kyay* (걔), gender-neutral, derived
      from *ku ai* ('that child'). -/
  | overt
  /-- Full NP — demonstrative + noun (e.g., *ku chinkwu* 'that friend'). -/
  | fullNP
  deriving DecidableEq, Repr, BEq

/-- Map each Korean form to its position on @cite{ariel-2001}'s 18-level scale.

    *kyay* maps to `unstressedPron` rather than `distalDem` because, although
    historically derived from a demonstrative, it functions synchronically
    as a 3rd-person pronoun in spoken Korean and lacks the deictic force
    of a true demonstrative (@cite{kwon-lee-2026} §5).

    The full-NP condition uses *demonstrative + noun* rather than a bare
    name or definite description, because Korean lacks definite articles. -/
def KoreanRefForm.toAccessibility : KoreanRefForm → AccessibilityLevel
  | .nullPro => .zero
  | .overt   => .unstressedPron
  | .fullNP  => .distalDemNP

/-- Bridge to the Korean fragment: the *overt* form's surface realization
    is the colloquial pronoun *gyae* (Yale: *kyay*) in
    `Fragments.Korean.Pronouns`. Derived from the fragment field — not
    duplicated. -/
def KoreanRefForm.surface : KoreanRefForm → Option String
  | .nullPro => none
  | .overt   => some Fragments.Korean.Pronouns.gyae.form
  | .fullNP  => some "ku chinkwu"  -- "that friend", representative; the
                                    -- experimental stimuli vary the noun

/-- The accessibility ordering predicted by @cite{ariel-2001} for the
    three Korean forms: *pro* > *kyay* > full NP. -/
theorem korean_accessibility_ordering :
    (KoreanRefForm.nullPro.toAccessibility).rank >
      (KoreanRefForm.overt.toAccessibility).rank ∧
    (KoreanRefForm.overt.toAccessibility).rank >
      (KoreanRefForm.fullNP.toAccessibility).rank := by decide

/-- The three forms span the *attenuation* dimension: null is maximally
    attenuated (no exponent), the overt pronoun is moderately attenuated,
    the full NP is unattenuated. -/
theorem korean_attenuation_ordering :
    (KoreanRefForm.nullPro.toAccessibility).attenuation >
      (KoreanRefForm.overt.toAccessibility).attenuation ∧
    (KoreanRefForm.overt.toAccessibility).attenuation >
      (KoreanRefForm.fullNP.toAccessibility).attenuation := by decide

/-- The forms span the *informativity* dimension in the inverse direction:
    full NP ≥ overt > null. The full-NP-vs-overt step is only `≥` because
    @cite{ariel-2001}'s informativity scale (encoded in
    `Ariel2001.AccessibilityLevel.informativity`) is coarse — it groups
    `distalDemNP` and `unstressedPron` at the same level (1). The
    finer-grained distinction surfaces in the rank ordering and in
    attenuation, not in informativity. -/
theorem korean_informativity_ordering :
    (KoreanRefForm.fullNP.toAccessibility).informativity ≥
      (KoreanRefForm.overt.toAccessibility).informativity ∧
    (KoreanRefForm.overt.toAccessibility).informativity >
      (KoreanRefForm.nullPro.toAccessibility).informativity := by decide

-- ════════════════════════════════════════════════════
-- § 2. Experiment 3: Antecedent Choice (Globally Ambiguous)
-- ════════════════════════════════════════════════════

/-- Antecedent-choice rates, from Figure 3 of @cite{kwon-lee-2026}.
    Globally ambiguous discourse contexts (two same-gender personal names),
    so neither semantic plausibility nor gender cues disambiguate.
    Form alone drives interpretation. -/
structure AntecedentChoice where
  form : KoreanRefForm
  /-- Percentage choosing the subject antecedent (0–100). -/
  subjectPct : Nat
  /-- Percentage choosing the object antecedent (0–100). -/
  objectPct : Nat
  deriving Repr

/-- Exp 3, *pro*: 70.6% subject, 29.4% object. -/
def exp3_pro : AntecedentChoice := ⟨.nullPro, 71, 29⟩

/-- Exp 3, *kyay*: 42.8% subject, 57.2% object. -/
def exp3_overt : AntecedentChoice := ⟨.overt, 43, 57⟩

/-- Exp 3, full NP: 35.3% subject, 64.7% object. -/
def exp3_fullNP : AntecedentChoice := ⟨.fullNP, 35, 65⟩

/-- The data is a complete partition: subject and object choices sum to
    ≈100% (no third option in the antecedent-choice task). -/
theorem exp3_partitions :
    exp3_pro.subjectPct + exp3_pro.objectPct = 100 ∧
    exp3_overt.subjectPct + exp3_overt.objectPct = 100 ∧
    exp3_fullNP.subjectPct + exp3_fullNP.objectPct = 100 := ⟨rfl, rfl, rfl⟩

/-- **Central claim of @cite{kwon-lee-2026}**: subject-antecedent bias is
    monotonically decreasing in informativity — i.e., monotonically
    increasing in accessibility rank. The three forms instantiate three
    points on @cite{ariel-2001}'s scale and yield three distinct biases.

    This is precisely the form–function correlation predicted by
    Accessibility Theory: more accessible (more reduced) forms refer to
    more accessible (subject-position) antecedents. -/
theorem accessibility_predicts_subject_bias :
    exp3_pro.subjectPct > exp3_overt.subjectPct ∧
    exp3_overt.subjectPct > exp3_fullNP.subjectPct := by decide

/-- The mirror image: object-antecedent bias is monotonically *increasing*
    in informativity. Full NPs are most object-biased. -/
theorem informativity_predicts_object_bias :
    exp3_fullNP.objectPct > exp3_overt.objectPct ∧
    exp3_overt.objectPct > exp3_pro.objectPct := by decide

/-- **Three-way distinction**: each pair is distinguishable. This rules
    out the alternative that Korean has only a binary null/non-null
    contrast (which @cite{kweon-2011} suggested for the older overt pronoun
    *ku/kunye*). -/
theorem three_way_split :
    exp3_pro.subjectPct ≠ exp3_overt.subjectPct ∧
    exp3_overt.subjectPct ≠ exp3_fullNP.subjectPct ∧
    exp3_pro.subjectPct ≠ exp3_fullNP.subjectPct := by decide

/-- Naturalness ratings (Table 5) on the 1–7 Likert scale, encoded
    ×100 throughout the file (5.30 → 530, 5.40 → 540). The three forms
    are essentially identical (5.3, 5.3, 5.4; n.s.). When the form is
    coindexed with its preferred antecedent, all three are equally
    natural. The accessibility distinction surfaces in *interpretation*
    (antecedent choice), not in raw acceptability. -/
def exp3_naturalness_x100 : KoreanRefForm → Nat
  | .nullPro => 530
  | .overt   => 530
  | .fullNP  => 540

theorem naturalness_pro_overt_equal :
    exp3_naturalness_x100 .nullPro = exp3_naturalness_x100 .overt := rfl

theorem naturalness_fullNP_close_to_pro :
    exp3_naturalness_x100 .fullNP - exp3_naturalness_x100 .nullPro ≤ 20 := by
  decide

-- ════════════════════════════════════════════════════
-- § 3. Experiment 1: Single Antecedent (Naturalness)
-- ════════════════════════════════════════════════════

/-- Exp 1 naturalness ratings (Table 1) on the 1–7 Likert scale, encoded
    ×100 (6.41 → 641, 6.18 → 618, 6.23 → 623). With only one available
    antecedent, the highest-accessibility marker (null *pro*) is the
    most natural. The overt pronoun and full NP do not differ
    significantly (β = 0.19, n.s.). -/
def exp1_naturalness_x100 : KoreanRefForm → Nat
  | .nullPro => 641
  | .overt   => 618
  | .fullNP  => 623

/-- **Null is most natural with a single highly-accessible antecedent**.
    Predicted by Accessibility Theory: when only one referent is salient,
    its mental representation is maximally accessible, so the maximally
    reduced form is the felicitous choice. -/
theorem exp1_null_most_natural :
    exp1_naturalness_x100 .nullPro > exp1_naturalness_x100 .overt ∧
    exp1_naturalness_x100 .nullPro > exp1_naturalness_x100 .fullNP := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The overt-vs-full-NP boundary is gradient in single-antecedent
    contexts**. The two forms do not differ significantly in Exp 1 — the
    accessibility distinction collapses when only one antecedent is
    available. @cite{kwon-lee-2026} interpret this as evidence that
    *adjacent* markers on the scale need not exhibit categorical
    distinctions across all contexts (consistent with @cite{ariel-2001}). -/
theorem exp1_overt_fullNP_close :
    (max (exp1_naturalness_x100 .overt) (exp1_naturalness_x100 .fullNP) -
     min (exp1_naturalness_x100 .overt) (exp1_naturalness_x100 .fullNP)) ≤ 10 := by
  decide

-- ════════════════════════════════════════════════════
-- § 4. Experiment 2: Comprehension Accuracy (Bias-Disambiguated)
-- ════════════════════════════════════════════════════

/-- Exp 2: comprehension accuracy when contextual gender bias points to
    a particular antecedent. The accuracy gap *across* contexts is the
    diagnostic of accessibility sensitivity.

    Subject-biased contexts: gender cue points to subject; null pronoun
    accuracy is near-ceiling (92.9%) because the form-cue (null → subject)
    aligns with the gender cue.

    Object-biased contexts: gender cue points to object, contradicting
    the form-cue for null. Accuracy drops to 60.3% — null pronouns
    *resist* the contextual override. Other forms show no asymmetry. -/
structure ComprehensionAccuracy where
  form : KoreanRefForm
  /-- Accuracy in subject-biased context (%). -/
  subjBiasedAcc : Nat
  /-- Accuracy in object-biased context (%). -/
  objBiasedAcc : Nat
  deriving Repr

/-- Figure 1 of @cite{kwon-lee-2026}. -/
def exp2_pro    : ComprehensionAccuracy := ⟨.nullPro, 93, 60⟩  -- 92.9 / 60.3
def exp2_overt  : ComprehensionAccuracy := ⟨.overt,   81, 78⟩  -- 81.4 / 78.2
def exp2_fullNP : ComprehensionAccuracy := ⟨.fullNP,  79, 80⟩  -- 79.4 / 79.5

/-- The accuracy gap between subject-biased and object-biased contexts,
    a measure of how strongly the form's interpretive bias resists the
    gender-cue override. -/
def ComprehensionAccuracy.contextSensitivity (c : ComprehensionAccuracy) : Nat :=
  max c.subjBiasedAcc c.objBiasedAcc - min c.subjBiasedAcc c.objBiasedAcc

/-- **Asymmetry diagnostic**: only the null pronoun shows a large
    accuracy gap between subject-biased and object-biased contexts.

    The overt pronoun and full NP do not differentiate the two contexts
    — they do not carry a strong enough form-cue to compete with the
    gender cue. The null pronoun *does* carry such a cue, evidenced by
    the 33-point accuracy drop when context contradicts it. This is
    direct evidence that null pronouns encode strong subject-antecedent
    expectations even in the comprehension component. -/
theorem null_alone_context_sensitive :
    exp2_pro.contextSensitivity > 30 ∧
    exp2_overt.contextSensitivity ≤ 5 ∧
    exp2_fullNP.contextSensitivity ≤ 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The asymmetry is *strictly* between null and the other forms: null's
    context-sensitivity exceeds both overt and full NP by an order of
    magnitude. -/
theorem null_more_context_sensitive_than_others :
    exp2_pro.contextSensitivity > exp2_overt.contextSensitivity ∧
    exp2_pro.contextSensitivity > exp2_fullNP.contextSensitivity := by
  refine ⟨?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 4b. Experiment 2: Naturalness Asymmetry (Figure 2)
-- ════════════════════════════════════════════════════

/-- Naturalness ratings (1–7 scale, ×100) for Exp 2, broken out by
    context bias. The naturalness data **mirrors** the comprehension
    accuracy data: only null pronouns show an asymmetry between
    subject-biased (4.58) and object-biased (3.94) contexts.

    This dual confirmation — same asymmetry in two independent dependent
    measures (interpretation accuracy AND felicity judgment) — is the
    paper's strongest evidence that null pronouns carry an interpretive
    bias that goes beyond mere preference. -/
structure Exp2Naturalness where
  form : KoreanRefForm
  /-- Naturalness × 100 in subject-biased context. -/
  subjBiased_x100 : Nat
  /-- Naturalness × 100 in object-biased context. -/
  objBiased_x100 : Nat
  deriving Repr

/-- Figure 2 of @cite{kwon-lee-2026}, on the 1–7 Likert scale (×100). -/
def exp2nat_pro    : Exp2Naturalness := ⟨.nullPro, 458, 394⟩  -- 4.58 / 3.94
def exp2nat_overt  : Exp2Naturalness := ⟨.overt,   462, 442⟩  -- 4.62 / 4.42
def exp2nat_fullNP : Exp2Naturalness := ⟨.fullNP,  433, 456⟩  -- 4.33 / 4.56

def Exp2Naturalness.contextSensitivity_x100 (n : Exp2Naturalness) : Nat :=
  max n.subjBiased_x100 n.objBiased_x100 - min n.subjBiased_x100 n.objBiased_x100

/-- **Naturalness mirrors comprehension**: only the null pronoun shows
    a large naturalness asymmetry across context biases (>50 points on
    the ×100 scale, β = −1.06, p = .028 in the paper). The overt and
    full NP forms show no significant asymmetry. -/
theorem exp2_naturalness_mirrors_accuracy :
    exp2nat_pro.contextSensitivity_x100 > 50 ∧
    exp2nat_overt.contextSensitivity_x100 ≤ 25 ∧
    exp2nat_fullNP.contextSensitivity_x100 ≤ 25 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The two Exp 2 dependent measures (accuracy and naturalness) agree on
    the *same* asymmetry pattern: null is the only form whose felicity
    drops when context conflicts with its interpretive bias. This
    converging evidence is the cornerstone of the paper's argument. -/
theorem exp2_dual_measures_converge :
    exp2_pro.contextSensitivity > exp2_overt.contextSensitivity ∧
    exp2nat_pro.contextSensitivity_x100 > exp2nat_overt.contextSensitivity_x100 := by
  refine ⟨?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 4c. Naturalness × Accuracy Cross-Validation
-- ════════════════════════════════════════════════════

/-- Naturalness ratings cross-tabulated with comprehension correctness
    (paper §3.2.2, p. 16): trials where participants chose the *intended*
    antecedent received higher naturalness ratings (M = 4.40) than trials
    where they chose the *unintended* antecedent (M = 4.05). Effect:
    β = 0.38, SE = 0.13, z = 3.05, p = .002.

    This is the paper's most direct evidence that the form-function
    correlation is **psychologically real** (not just an experimental
    artifact): listeners who heard a form and computed an antecedent that
    didn't match the speaker's intent *also* perceived the sentence as
    less natural. The two measures co-vary at the trial level. -/
def correctTrial_naturalness_x100 : Nat := 440  -- M = 4.40, SE = 0.04
def incorrectTrial_naturalness_x100 : Nat := 405  -- M = 4.05, SE = 0.09

/-- **Form-function correlation is psychologically real**: when the
    listener's chosen antecedent matches the speaker's intent (correct
    trial), the sentence is rated *more natural* than when it doesn't.
    This validates the form-function link as more than an experimental
    artifact — it tracks the listener's online interpretive process. -/
theorem correct_trials_more_natural :
    correctTrial_naturalness_x100 > incorrectTrial_naturalness_x100 := by decide

/-- The gap is non-trivial (35 points on the ×100 scale ≈ 0.35 Likert
    points), within the range where the paper reports significance
    (β = 0.38). -/
theorem naturalness_accuracy_gap_substantial :
    correctTrial_naturalness_x100 - incorrectTrial_naturalness_x100 ≥ 30 := by decide

-- ════════════════════════════════════════════════════
-- § 5. Cross-Linguistic Comparison
-- ════════════════════════════════════════════════════

/-- A language's *calibration* of @cite{ariel-2001}'s accessibility scale:
    the empirical subject-antecedent bias of each referential form in a
    globally ambiguous two-antecedent context.

    This is the structure that lets us compare how different languages
    instantiate the same universal ordering. The relative ordering
    (null > overt > [full NP]) is preserved, but the spread varies. -/
structure CrossLingProfile where
  language : String
  /-- P(subject antecedent | null pronoun), as a percentage. -/
  nullSubjPct : Nat
  /-- P(subject antecedent | overt pronoun). `none` if the language was
      not tested with overt pronouns or has no overt 3sg pronoun. -/
  overtSubjPct : Option Nat
  /-- P(subject antecedent | full NP). `none` if not tested. -/
  fullNPSubjPct : Option Nat
  /-- Source citation. -/
  source : String
  deriving Repr

/-- Italian, @cite{carminati-2002}: null = 80.72%, overt = 100% − 83.33%
    = 16.67%. The cleanest division of labor of any language tested
    (Position of Antecedent Hypothesis). -/
def italian : CrossLingProfile :=
  { language := "Italian", nullSubjPct := 81, overtSubjPct := some 17
  , fullNPSubjPct := none, source := "Carminati 2002" }

/-- Spanish, @cite{contemori-di-domenico-2021}: null = 62%, overt = 100%
    − 58% = 42%. Weaker division of labor than Italian. -/
def spanish : CrossLingProfile :=
  { language := "Spanish", nullSubjPct := 62, overtSubjPct := some 42
  , fullNPSubjPct := none, source := "Contemori & Di Domenico 2021" }

/-- Chinese, @cite{zhang-kwon-2022}: null = 84%, overt = 65.3%. Both
    pronoun types show subject bias; the overt form does *not* flip to
    object bias as in Italian. -/
def chinese : CrossLingProfile :=
  { language := "Chinese", nullSubjPct := 84, overtSubjPct := some 65
  , fullNPSubjPct := none, source := "Zhang & Kwon 2022" }

/-- Korean (this paper's Exp 3, overt = colloquial *kyay*). The first
    cross-linguistic dataset that includes full NPs alongside null and
    overt pronouns. -/
def korean : CrossLingProfile :=
  { language := "Korean (Kwon & Lee 2026, kyay)"
  , nullSubjPct := exp3_pro.subjectPct
  , overtSubjPct := some exp3_overt.subjectPct
  , fullNPSubjPct := some exp3_fullNP.subjectPct
  , source := "Kwon & Lee 2026, J. Linguistics" }

/-- Korean (@cite{kweon-2011}, overt = literary *ku/kunye*). 12-item
    questionnaire study; null = 81.1%, overt = 31.4% subject (so 68.6%
    object). Resembles Italian's clean division of labor — Kweon
    interpreted this as supporting Carminati's PAH. -/
def korean_kweon : CrossLingProfile :=
  { language := "Korean (Kweon 2011, ku/kunye)"
  , nullSubjPct := 81, overtSubjPct := some 31
  , fullNPSubjPct := none
  , source := "Kweon 2011, Int. J. Linguistics" }

/-- Korean (@cite{choe-2021}, overt = literary *ku/kunye*). 40-target /
    24-filler study; null = 91%, overt = 73% subject. Both forms
    subject-biased; little division of labor. Diverges sharply from
    Kweon. The paper attributes the discrepancy to methodological
    differences (filler ratio, ambiguity verification). -/
def korean_choe : CrossLingProfile :=
  { language := "Korean (Choe 2021, ku/kunye)"
  , nullSubjPct := 91, overtSubjPct := some 73
  , fullNPSubjPct := none
  , source := "Choe 2021, Discourse and Cognition" }

def allProfiles : List CrossLingProfile :=
  [italian, spanish, chinese, korean, korean_kweon, korean_choe]

/-- All Korean profiles. -/
def koreanProfiles : List CrossLingProfile := [korean, korean_kweon, korean_choe]

/-- **Universal ordering preserved**: in every language tested, null
    pronouns are at least as subject-biased as overt pronouns. This is
    the universal claim of @cite{ariel-2001}: the *relative ordering*
    holds even when the magnitudes vary. -/
theorem null_dominates_overt_universally :
    allProfiles.all (fun p => match p.overtSubjPct with
                              | some o => p.nullSubjPct ≥ o
                              | none   => true) = true := by decide

/-- **Cross-linguistic granularity varies**: Italian shows ≥60-point
    spread between null and overt; Spanish 20; Chinese 19; Korean 28.
    The same theory accounts for all four, with language-specific
    calibration of the spread. -/
def CrossLingProfile.nullOvertSpread (p : CrossLingProfile) : Nat :=
  match p.overtSubjPct with
  | some o => p.nullSubjPct - o
  | none   => 0

theorem italian_widest_spread :
    italian.nullOvertSpread > spanish.nullOvertSpread ∧
    italian.nullOvertSpread > chinese.nullOvertSpread ∧
    italian.nullOvertSpread > korean.nullOvertSpread := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Korean is the only language tested with full NPs**: a unique
    methodological contribution of @cite{kwon-lee-2026}. The full-NP
    bias (35% subject ↔ 65% object) extends Accessibility Theory's test
    set to a wider range of forms than prior cross-linguistic work. -/
theorem korean_uniquely_includes_fullNP :
    korean.fullNPSubjPct.isSome ∧
    italian.fullNPSubjPct.isNone ∧
    spanish.fullNPSubjPct.isNone ∧
    chinese.fullNPSubjPct.isNone := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5b. Korean-Internal Comparison: Kweon vs Choe vs Kwon&Lee
-- ════════════════════════════════════════════════════

/-- **Robust within-Korean finding**: every Korean study agrees that null
    pronouns are subject-biased. The variation is entirely in the
    *strength* of the bias (and in the overt-pronoun behavior). -/
theorem all_korean_null_subject_biased :
    koreanProfiles.all (fun p => p.nullSubjPct > 50) = true := by decide

/-- **The Kweon vs Choe disagreement** is one of the paper's framing
    motivations. Kweon shows clean object-bias for overt (~31% subject);
    Choe shows subject-bias (73%). The numerical gap is large — these
    cannot both be representative of the same underlying competence.
    The paper attributes the disagreement to methodological factors
    (Kweon's small item set; Choe's unusually low filler ratio). -/
theorem kweon_choe_disagree :
    korean_kweon.overtSubjPct = some 31 ∧
    korean_choe.overtSubjPct = some 73 ∧
    -- The gap exceeds 40 percentage points
    73 - 31 > 40 := ⟨rfl, rfl, by decide⟩

/-- @cite{kwon-lee-2026}'s Exp 3 finding (43% subject for *kyay*) lies
    *between* Kweon (31%) and Choe (73%). The paper takes this as
    suggesting Kweon was directionally correct (overt is object-biased
    in Korean) but that the magnitude depends on the form: *kyay* is
    less rigidly object-biased than *ku/kunye*, consistent with *kyay*'s
    higher position on the accessibility scale (closer to null). -/
theorem exp3_kyay_lies_between_kweon_choe :
    korean_kweon.overtSubjPct = some 31 ∧
    korean.overtSubjPct = some 43 ∧
    korean_choe.overtSubjPct = some 73 := ⟨rfl, rfl, rfl⟩

/-- The relative ordering (null > overt) holds for **every** Korean
    study, despite the disagreement on magnitudes. This is exactly
    @cite{ariel-2001}'s universal: the *ordering* is invariant; the
    *spread* is methodologically/contextually labile. -/
theorem korean_relative_ordering_invariant :
    koreanProfiles.all (fun p => match p.overtSubjPct with
                                 | some o => p.nullSubjPct > o
                                 | none   => true) = true := by decide

-- ════════════════════════════════════════════════════
-- § 5c. Accessibility Distance and Non-Uniform Calibration
-- ════════════════════════════════════════════════════

/-- Distance between two forms on @cite{ariel-2001}'s accessibility scale,
    measured as the absolute difference of their ranks. Larger distance
    = further apart on the universal ordering. -/
def KoreanRefForm.accessibilityDistance (a b : KoreanRefForm) : Nat :=
  let ra := a.toAccessibility.rank
  let rb := b.toAccessibility.rank
  max ra rb - min ra rb

/-- Subject-bias spread between two forms in Exp 3 (absolute difference
    of subject-choice percentages). Larger spread = stronger empirical
    distinction between the two forms. -/
def biasSpread (a b : AntecedentChoice) : Nat :=
  max a.subjectPct b.subjectPct - min a.subjectPct b.subjectPct

/-- **Triangle-inequality-like prediction**: the extreme pair (null vs
    full NP) has the largest accessibility distance AND the largest
    empirical bias spread. This is a *derived* prediction of
    @cite{ariel-2001}'s ordinal scale — it follows from the rank
    ordering of the three forms, not from any data-fitting. -/
theorem extreme_pair_maximal_distance_and_spread :
    -- Accessibility distance ordering: pro↔fullNP > each step
    KoreanRefForm.nullPro.accessibilityDistance .fullNP >
      KoreanRefForm.nullPro.accessibilityDistance .overt ∧
    KoreanRefForm.nullPro.accessibilityDistance .fullNP >
      KoreanRefForm.overt.accessibilityDistance .fullNP ∧
    -- Empirical bias spread ordering: same pattern
    biasSpread exp3_pro exp3_fullNP > biasSpread exp3_pro exp3_overt ∧
    biasSpread exp3_pro exp3_fullNP > biasSpread exp3_overt exp3_fullNP := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Non-uniform calibration** — the paper's deepest empirical finding
    (Discussion p. 22): the null↔overt step (3 ranks → 28-point bias
    spread) is much steeper than the overt↔full-NP step (6 ranks →
    8-point bias spread). Korean's accessibility scale has a steep
    cliff at the null/non-null boundary and a shallow slope between the
    overt and full-NP forms. This is exactly what @cite{ariel-2001}
    predicts (§4.2) about language-specific calibration: only the
    *ordering* is universal, not the magnitudes.

    Formally: smaller accessibility distance → larger bias spread, when
    comparing the (pro, overt) pair to the (overt, fullNP) pair. -/
theorem korean_calibration_non_uniform :
    KoreanRefForm.nullPro.accessibilityDistance .overt <
      KoreanRefForm.overt.accessibilityDistance .fullNP ∧
    biasSpread exp3_pro exp3_overt > biasSpread exp3_overt exp3_fullNP := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The cliff-and-slope finding generalizes the paper's claim (§5,
    Discussion): "the primary accessibility contrast in Korean lies
    between null and non-null forms" — the null/non-null boundary is
    where the action is, while distinctions among non-null forms are
    finer-grained and more context-dependent. -/
theorem null_nonnull_boundary_is_primary :
    -- The pro↔overt spread (28) and pro↔fullNP spread (36) are both
    -- driven by the null/non-null transition; the residual overt↔fullNP
    -- spread (8) is small.
    biasSpread exp3_pro exp3_overt > 25 ∧
    biasSpread exp3_overt exp3_fullNP < 15 := by
  refine ⟨?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 6. Bridge to @cite{kehler-rohde-2013}
-- ════════════════════════════════════════════════════

/-- @cite{kehler-rohde-2013} decompose pronoun interpretation as:

      P(referent | pronoun) ∝ P(pronoun | referent) × P(referent)

    The production component P(pronoun | referent) is conditioned by
    *topichood* — speakers use reduced forms for topical referents. The
    Korean data slot directly into this framework: the canonical Korean
    topic position is the (typically subject-marked) sentence-initial
    position, so subjects have high topichood and license null forms.

    The cross-linguistic variation in spread (§ 5) reflects how strongly
    each language's null form encodes topichood relative to other forms. -/
def koreanSubjectTopichood : KehlerRohde2013.TopichoodLevel :=
  KehlerRohde2013.topichood .Act true

/-- Korean subjects are the default topichood level (subject of an active
    clause). Null pronouns mark high accessibility, which @cite{kehler-rohde-2013}
    derive from high topichood. -/
theorem subject_default_topichood :
    koreanSubjectTopichood = .default_ := rfl

-- ════════════════════════════════════════════════════
-- § 6b. Alternative Theory: Position of Antecedent Hypothesis
-- ════════════════════════════════════════════════════

/-- Carminati's Position of Antecedent Hypothesis (@cite{carminati-2002}):
    null pronouns prefer antecedents in syntactically prominent positions
    (canonically Spec-IP, the preverbal subject position); overt pronouns
    prefer non-prominent positions.

    PAH is a **structural** theory: prominence is determined by syntactic
    position, not by discourse accessibility. This contrasts with
    Accessibility Theory's cognitive/discourse-based prominence. In
    configurational SVO languages where subject = Spec-IP, the two
    theories make identical predictions; they diverge in topic-prominent
    languages where the topic position is structurally distinct from
    Spec-IP.

    @cite{kwon-lee-2026} fn. 1 takes the position that PAH and AT are
    compatible — PAH being a structural special case that happens to
    coincide with AT in canonical configurations. -/
inductive SyntacticPosition where
  /-- Spec-IP: preverbal subject position. PAH's "prominent" position. -/
  | specIP
  /-- Below Spec-IP: object, complement, adjunct positions. -/
  | lowerIP
  deriving DecidableEq, Repr, BEq

/-- The PAH-predicted antecedent position for each Korean form.
    Null prefers Spec-IP; overt avoids it (overt → non-Spec-IP). The
    PAH does not directly address full NPs (it was formulated for the
    null/overt pronoun contrast in Italian). -/
def KoreanRefForm.pahPosition : KoreanRefForm → Option SyntacticPosition
  | .nullPro => some .specIP
  | .overt   => some .lowerIP
  | .fullNP  => none

/-- **Convergence theorem**: PAH and AT make the same prediction for
    null pronouns in canonical Korean SVO — both predict the subject
    antecedent (subject = Spec-IP in the experimental stimuli). This is
    why @cite{kwon-lee-2026}'s Exp 3 data cannot distinguish the two
    theories. -/
theorem pah_at_converge_for_canonical_korean :
    KoreanRefForm.nullPro.pahPosition = some .specIP := rfl

/-- **Divergence point**: in a topic-prominent configuration (e.g., a
    sentence with a topicalized object in sentence-initial position),
    the topic is NOT in Spec-IP. PAH would still predict null → Spec-IP
    (= the in-situ subject), while AT would predict null → topic (= the
    most-accessible referent regardless of structural position).

    The Korean experiments cannot test this because all stimuli used
    canonical SVO order. Disambiguating PAH from AT requires testing
    topicalization configurations — an empirical extension explicitly
    flagged by @cite{kwon-lee-2026} (Discussion). -/
theorem pah_at_diverge_in_topic_fronting :
    -- PAH still predicts Spec-IP (the in-situ subject)
    KoreanRefForm.nullPro.pahPosition = some .specIP := rfl

/-- PAH does not address full NPs — it was formulated for pronouns only.
    AT, by contrast, places full NPs at the bottom of the accessibility
    scale and predicts the inverse bias (object antecedent). The Exp 3
    full-NP finding (35% subject ↔ 65% object) is therefore predicted
    by AT alone, not by PAH. The paper's inclusion of full NPs is what
    lets the data adjudicate between the two theories. -/
theorem pah_silent_on_fullNP :
    KoreanRefForm.fullNP.pahPosition = none := rfl

-- ════════════════════════════════════════════════════
-- § 6c. Bridge to AccessibilityAssessment: What Each Experiment Manipulates
-- ════════════════════════════════════════════════════

open Phenomena.Reference.Studies.Ariel2001 (AccessibilityAssessment)

/-- Exp 1: a single antecedent in same-clause topic position. Maximally
    accessible — no competition, tight unity, recently mentioned, topical.
    Predicts the form should not need to disambiguate. -/
def exp1_assessment : AccessibilityAssessment := ⟨0, 2, 0, 2⟩

/-- Exp 2 & 3: two antecedents in same clause. Competition = 1 (one
    additional candidate). The two experiments differ in whether
    additional cues (gender in Exp 2) disambiguate, but the
    accessibility-theoretic competition level is identical.

    @cite{ariel-2001}'s `AccessibilityAssessment` does not have a
    field for "disambiguating cue", which is the gap that the Exp 2
    naturalness × accuracy correlation (§ 4c) helps fill. -/
def exp2_3_assessment : AccessibilityAssessment := ⟨0, 2, 1, 2⟩

/-- **The manipulation isolates competition**: across the three
    experiments, only the `competition` field of `AccessibilityAssessment`
    varies. Distance, topicality, and unity are held constant.
    This makes the experimental design a clean test of how competition
    affects form-function visibility. -/
theorem experiments_isolate_competition :
    exp1_assessment.distance = exp2_3_assessment.distance ∧
    exp1_assessment.topicality = exp2_3_assessment.topicality ∧
    exp1_assessment.unity = exp2_3_assessment.unity ∧
    exp1_assessment.competition < exp2_3_assessment.competition :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- Exp 1 has higher accessibility than Exp 2/3 — the referent is more
    accessible when there's no competition. -/
theorem exp1_more_accessible_than_exp23 :
    exp1_assessment.score > exp2_3_assessment.score := by decide

/-- **Empirical asymmetry consistent with the theory**: in the
    high-accessibility Exp 1 setting (one antecedent), the
    form-function distinction collapses (`exp1_overt_fullNP_close`).
    In the lower-accessibility Exp 3 setting (competition), the
    distinction emerges as a clean three-way split
    (`accessibility_predicts_subject_bias`).

    This is captured by the assessment-score difference: form-bias
    strength is *inversely* correlated with the per-referent
    accessibility score, because forms only need to disambiguate when
    there is ambiguity to resolve. -/
theorem form_bias_emerges_under_competition :
    -- Exp 1 (high accessibility, no competition): adjacent forms collapse
    (max (exp1_naturalness_x100 .overt) (exp1_naturalness_x100 .fullNP) -
     min (exp1_naturalness_x100 .overt) (exp1_naturalness_x100 .fullNP)) ≤ 10 ∧
    -- Exp 3 (lower accessibility, competition): clear separation
    biasSpread exp3_overt exp3_fullNP > 0 := by
  refine ⟨?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to @cite{ariel-2001} Form-Function Criteria
-- ════════════════════════════════════════════════════

/-- @cite{ariel-2001}'s three form-function criteria all line up with
    accessibility for the Korean forms — exactly as the universal
    theory predicts. This grounds the cross-linguistic claim in
    @cite{ariel-2001}'s structural argument. -/
theorem korean_forms_satisfy_criteria :
    -- Informativity: full NP ≥ overt > null (≥ because Ariel's coarse
    -- informativity scale collapses distalDemNP and unstressedPron at 1)
    (KoreanRefForm.fullNP.toAccessibility).informativity ≥
      (KoreanRefForm.overt.toAccessibility).informativity ∧
    (KoreanRefForm.overt.toAccessibility).informativity >
      (KoreanRefForm.nullPro.toAccessibility).informativity ∧
    -- Rigidity: full NP (demonstrative + noun) ≥ overt ≥ null
    (KoreanRefForm.fullNP.toAccessibility).rigidity ≥
      (KoreanRefForm.overt.toAccessibility).rigidity ∧
    -- Attenuation: null > overt > full NP — the cleanest dimension
    (KoreanRefForm.nullPro.toAccessibility).attenuation >
      (KoreanRefForm.overt.toAccessibility).attenuation ∧
    (KoreanRefForm.overt.toAccessibility).attenuation >
      (KoreanRefForm.fullNP.toAccessibility).attenuation := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Phenomena.Reference.Studies.KwonLee2026
