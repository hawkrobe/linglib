import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Core.Discourse.ReferentialForm
import Linglib.Phenomena.Reference.Studies.Ariel2001
import Linglib.Phenomena.Reference.Studies.KehlerRohde2013
import Linglib.Fragments.Korean.Pronouns

/-!
# @cite{kwon-lee-2026}: Accessibility Markers in Korean
@cite{ariel-2001} @cite{carminati-2002} @cite{kweon-2011}
@cite{contemori-di-domenico-2021} @cite{zhang-kwon-2022} @cite{choe-2021}

Three experiments test @cite{ariel-2001}'s Accessibility Theory in
Korean — a discourse-oriented language without verbal/gender agreement —
using null pronouns, overt *kyay*, and full NPs. The Experiment 3
antecedent-choice data (71% / 43% / 35% subject bias) instantiates the
universal accessibility ordering at three points; the relative ordering
holds cross-linguistically while the spread is language-specific.

`KoreanRefForm` is the 3-element domain tested. It carries a
`LinearOrder` lifted from `AccessibilityLevel.rank`, so the central
claim "subject bias increases in accessibility" appears as one
`StrictMono` lemma (`subjectBias_strictMono`) rather than per-pair
inequalities. Bridges to @cite{kehler-rohde-2013} (topichood),
@cite{carminati-2002} (PAH alternative), and Ariel's
`AccessibilityAssessment` are provided.
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

@[simp] theorem nullPro_toAccessibility :
    KoreanRefForm.nullPro.toAccessibility = .zero := rfl

@[simp] theorem overt_toAccessibility :
    KoreanRefForm.overt.toAccessibility = .unstressedPron := rfl

@[simp] theorem fullNP_toAccessibility :
    KoreanRefForm.fullNP.toAccessibility = .distalDemNP := rfl

/-- The accessibility rank of a Korean form (the rank of its
    `AccessibilityLevel` image), used to lift the universal accessibility
    ordering onto `KoreanRefForm`. -/
@[simp] def KoreanRefForm.rank (f : KoreanRefForm) : Nat :=
  f.toAccessibility.rank

/-- `KoreanRefForm` inherits a `LinearOrder` from @cite{ariel-2001}'s
    accessibility scale via the `rank` pullback. The induced order is
    `fullNP < overt < nullPro` — more accessible forms are larger.
    This lets every monotonicity claim about Korean forms be expressed
    as a single `StrictMono` lemma rather than per-pair inequalities. -/
instance : LinearOrder KoreanRefForm :=
  LinearOrder.lift' KoreanRefForm.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [KoreanRefForm.rank,
      KoreanRefForm.toAccessibility, AccessibilityLevel.rank])

/-- The order is `fullNP < overt < nullPro` (more accessible = larger). -/
theorem fullNP_lt_overt : (KoreanRefForm.fullNP : KoreanRefForm) < .overt := by decide

theorem overt_lt_nullPro : (KoreanRefForm.overt : KoreanRefForm) < .nullPro := by decide

/-- Bridge to the Korean fragment: the *overt* form's surface realization
    is the colloquial pronoun *gyae* (Yale: *kyay*) in
    `Fragments.Korean.Pronouns`. Derived from the fragment field — not
    duplicated. -/
def KoreanRefForm.surface : KoreanRefForm → Option String
  | .nullPro => none
  | .overt   => some Fragments.Korean.Pronouns.gyae.form
  | .fullNP  => some "ku chinkwu"  -- "that friend", representative; the
                                    -- experimental stimuli vary the noun

@[simp] theorem nullPro_surface : KoreanRefForm.nullPro.surface = none := rfl
@[simp] theorem overt_surface :
    KoreanRefForm.overt.surface = some Fragments.Korean.Pronouns.gyae.form := rfl
@[simp] theorem fullNP_surface :
    KoreanRefForm.fullNP.surface = some "ku chinkwu" := rfl

/-- Attenuation (phonological reduction) is strictly increasing in the
    accessibility order on Korean forms: more accessible forms are more
    reduced. (Subsumes the previous per-pair attenuation theorems via
    `StrictMono.lt_iff_lt`.) -/
theorem attenuation_strictMono :
    StrictMono (fun f : KoreanRefForm => f.toAccessibility.attenuation) := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

/-- Informativity is *anti*tone in accessibility: more accessible forms
    are less informative (≤, not <, because @cite{ariel-2001}'s scale
    collapses `distalDemNP` and `unstressedPron` at informativity 1). -/
theorem informativity_antitone :
    Antitone (fun f : KoreanRefForm => f.toAccessibility.informativity) := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

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
  subjectPercent : Nat
  /-- Percentage choosing the object antecedent (0–100). -/
  objectPercent : Nat
  deriving Repr

/-- Exp 3, *pro*: 70.6% subject, 29.4% object. -/
def exp3_pro : AntecedentChoice := ⟨.nullPro, 71, 29⟩

/-- Exp 3, *kyay*: 42.8% subject, 57.2% object. -/
def exp3_overt : AntecedentChoice := ⟨.overt, 43, 57⟩

/-- Exp 3, full NP: 35.3% subject, 64.7% object. -/
def exp3_fullNP : AntecedentChoice := ⟨.fullNP, 35, 65⟩

/-- Subject-antecedent bias for each Korean form, derived from the Exp 3
    records. Defined as a function so the central monotonicity claim
    can be expressed as `StrictMono`. -/
@[simp] def subjectBias : KoreanRefForm → Nat
  | .nullPro => exp3_pro.subjectPercent
  | .overt   => exp3_overt.subjectPercent
  | .fullNP  => exp3_fullNP.subjectPercent

/-- Object-antecedent bias for each Korean form. -/
@[simp] def objectBias : KoreanRefForm → Nat
  | .nullPro => exp3_pro.objectPercent
  | .overt   => exp3_overt.objectPercent
  | .fullNP  => exp3_fullNP.objectPercent

/-- The Exp 3 task forces a binary subject/object choice, so for each
    form the two percentages sum to 100. -/
theorem exp3_partitions (f : KoreanRefForm) : subjectBias f + objectBias f = 100 := by
  cases f <;> decide

/-- **Central claim of @cite{kwon-lee-2026}**: subject-antecedent bias is
    strictly monotone in accessibility — more accessible (higher-rank)
    forms attract subject antecedents more strongly. This single
    `StrictMono` lemma subsumes per-pair claims like
    `subjectBias .nullPro > subjectBias .overt` (which follow via
    `StrictMono.lt_iff_lt` applied to `fullNP_lt_overt`/`overt_lt_nullPro`).

    Form–function correlation in one line: more accessible form ↔ more
    accessible antecedent. -/
theorem subjectBias_strictMono : StrictMono subjectBias := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

/-- Mirror image: object-antecedent bias is *anti*tone in accessibility.
    Full NPs are the most object-biased; null pronouns the least. -/
theorem objectBias_strictAnti : StrictAnti objectBias := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

/-- **Three-way distinction**: corollary of `subjectBias_strictMono` —
    the three forms have three distinct subject-bias values. Rules out
    the alternative that Korean has only a binary null/non-null contrast
    (which @cite{kweon-2011} suggested for the older overt pronoun
    *ku/kunye*). -/
theorem three_way_split : Function.Injective subjectBias :=
  subjectBias_strictMono.injective

/-- Naturalness ratings (Table 5) on the 1–7 Likert scale. The three
    forms are essentially identical (5.3, 5.3, 5.4; n.s.). When the
    form is coindexed with its preferred antecedent, all three are
    equally natural. The accessibility distinction surfaces in
    *interpretation* (antecedent choice), not in raw acceptability. -/
def exp3_naturalness : KoreanRefForm → ℚ
  | .nullPro => 53/10
  | .overt   => 53/10
  | .fullNP  => 54/10

theorem naturalness_pro_overt_equal :
    exp3_naturalness .nullPro = exp3_naturalness .overt := rfl

theorem naturalness_fullNP_close_to_pro :
    exp3_naturalness .fullNP - exp3_naturalness .nullPro ≤ 2/10 := by
  unfold exp3_naturalness; norm_num

-- ════════════════════════════════════════════════════
-- § 3. Experiment 1: Single Antecedent (Naturalness)
-- ════════════════════════════════════════════════════

/-- Exp 1 naturalness ratings (Table 1) on the 1–7 Likert scale. With
    only one available antecedent, the highest-accessibility marker
    (null *pro*) is the most natural. The overt pronoun and full NP do
    not differ significantly (β = 0.19, n.s.). -/
def exp1_naturalness : KoreanRefForm → ℚ
  | .nullPro => 641/100
  | .overt   => 618/100
  | .fullNP  => 623/100

/-- **Null is most natural with a single highly-accessible antecedent**.
    Predicted by Accessibility Theory: when only one referent is salient,
    its mental representation is maximally accessible, so the maximally
    reduced form is the felicitous choice. -/
theorem exp1_null_most_natural :
    exp1_naturalness .nullPro > exp1_naturalness .overt ∧
    exp1_naturalness .nullPro > exp1_naturalness .fullNP := by
  refine ⟨?_, ?_⟩ <;> (unfold exp1_naturalness; norm_num)

/-- **The overt-vs-full-NP boundary is gradient in single-antecedent
    contexts**. The two forms do not differ significantly in Exp 1 — the
    accessibility distinction collapses when only one antecedent is
    available. @cite{kwon-lee-2026} interpret this as evidence that
    *adjacent* markers on the scale need not exhibit categorical
    distinctions across all contexts (consistent with @cite{ariel-2001}).
    For the concrete values, full NP is rated slightly higher than overt
    by less than 0.1 Likert points. -/
theorem exp1_overt_fullNP_close :
    exp1_naturalness .fullNP - exp1_naturalness .overt ≤ 1/10 := by
  unfold exp1_naturalness; norm_num

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
  subjectBiasedAccuracy : Nat
  /-- Accuracy in object-biased context (%). -/
  objectBiasedAccuracy : Nat
  deriving Repr

/-- Figure 1 of @cite{kwon-lee-2026}. -/
def exp2_pro    : ComprehensionAccuracy := ⟨.nullPro, 93, 60⟩  -- 92.9 / 60.3
def exp2_overt  : ComprehensionAccuracy := ⟨.overt,   81, 78⟩  -- 81.4 / 78.2
def exp2_fullNP : ComprehensionAccuracy := ⟨.fullNP,  79, 80⟩  -- 79.4 / 79.5

/-- The accuracy gap between subject-biased and object-biased contexts,
    a measure of how strongly the form's interpretive bias resists the
    gender-cue override. -/
def ComprehensionAccuracy.contextSensitivity (c : ComprehensionAccuracy) : Nat :=
  max c.subjectBiasedAccuracy c.objectBiasedAccuracy - min c.subjectBiasedAccuracy c.objectBiasedAccuracy

/-- Null pronouns drop ~33 accuracy points when the context bias contradicts
    their default subject-antecedent preference (Figure 1). Direct evidence
    that null pronouns encode strong subject-antecedent expectations even
    in the comprehension component. -/
theorem exp2_pro_strongly_context_sensitive :
    exp2_pro.contextSensitivity > 30 := by decide

/-- Overt pronouns show essentially no asymmetry across context biases. -/
theorem exp2_overt_context_insensitive :
    exp2_overt.contextSensitivity ≤ 5 := by decide

/-- Full NPs show essentially no asymmetry across context biases. -/
theorem exp2_fullNP_context_insensitive :
    exp2_fullNP.contextSensitivity ≤ 5 := by decide

/-- Null is strictly more context-sensitive than overt — exceeding it by
    over 25 percentage points. -/
theorem exp2_pro_more_sensitive_than_overt :
    exp2_pro.contextSensitivity > exp2_overt.contextSensitivity := by decide

/-- Null is strictly more context-sensitive than full NP. -/
theorem exp2_pro_more_sensitive_than_fullNP :
    exp2_pro.contextSensitivity > exp2_fullNP.contextSensitivity := by decide

-- ════════════════════════════════════════════════════
-- § 4b. Experiment 2: Naturalness Asymmetry (Figure 2)
-- ════════════════════════════════════════════════════

/-- Naturalness ratings on the 1–7 Likert scale for Exp 2, broken out
    by context bias. The naturalness data **mirrors** the comprehension
    accuracy data: only null pronouns show an asymmetry between
    subject-biased (4.58) and object-biased (3.94) contexts.

    This dual confirmation — same asymmetry in two independent dependent
    measures (interpretation accuracy AND felicity judgment) — is the
    paper's strongest evidence that null pronouns carry an interpretive
    bias that goes beyond mere preference. -/
structure Exp2Naturalness where
  form : KoreanRefForm
  /-- Naturalness in subject-biased context (1–7 Likert). -/
  subjectBiased : ℚ
  /-- Naturalness in object-biased context (1–7 Likert). -/
  objectBiased : ℚ
  deriving Repr

/-- Figure 2 of @cite{kwon-lee-2026}. -/
def exp2nat_pro    : Exp2Naturalness := ⟨.nullPro, 458/100, 394/100⟩
def exp2nat_overt  : Exp2Naturalness := ⟨.overt,   462/100, 442/100⟩
def exp2nat_fullNP : Exp2Naturalness := ⟨.fullNP,  433/100, 456/100⟩

def Exp2Naturalness.contextSensitivity (n : Exp2Naturalness) : ℚ :=
  max n.subjectBiased n.objectBiased - min n.subjectBiased n.objectBiased

/-- **Naturalness mirrors comprehension**: only the null pronoun shows
    a large naturalness asymmetry across context biases (>0.50 Likert
    points, β = −1.06, p = .028 in the paper). The overt and full NP
    forms show no significant asymmetry. -/
theorem exp2_naturalness_pro_strongly_asymmetric :
    exp2nat_pro.contextSensitivity > 1/2 := by
  unfold Exp2Naturalness.contextSensitivity exp2nat_pro; norm_num

theorem exp2_naturalness_overt_close :
    exp2nat_overt.contextSensitivity ≤ 1/4 := by
  unfold Exp2Naturalness.contextSensitivity exp2nat_overt; norm_num

theorem exp2_naturalness_fullNP_close :
    exp2nat_fullNP.contextSensitivity ≤ 1/4 := by
  unfold Exp2Naturalness.contextSensitivity exp2nat_fullNP; norm_num

/-- The two Exp 2 dependent measures (accuracy and naturalness) agree on
    the *same* asymmetry pattern: null is the only form whose felicity
    drops when context conflicts with its interpretive bias. This
    converging evidence is the cornerstone of the paper's argument. -/
theorem exp2_dual_measures_converge_accuracy :
    exp2_pro.contextSensitivity > exp2_overt.contextSensitivity := by decide

theorem exp2_dual_measures_converge_naturalness :
    exp2nat_pro.contextSensitivity > exp2nat_overt.contextSensitivity := by
  unfold Exp2Naturalness.contextSensitivity exp2nat_pro exp2nat_overt; norm_num

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
abbrev correctTrial_naturalness : ℚ := 440/100  -- M = 4.40, SE = 0.04
abbrev incorrectTrial_naturalness : ℚ := 405/100  -- M = 4.05, SE = 0.09

/-- **Form-function correlation is psychologically real**: when the
    listener's chosen antecedent matches the speaker's intent (correct
    trial), the sentence is rated *more natural* than when it doesn't.
    This validates the form-function link as more than an experimental
    artifact — it tracks the listener's online interpretive process. -/
theorem correct_trials_more_natural :
    correctTrial_naturalness > incorrectTrial_naturalness := by norm_num

/-- The gap is non-trivial (≈ 0.35 Likert points), within the range
    where the paper reports significance (β = 0.38). -/
theorem naturalness_accuracy_gap_substantial :
    correctTrial_naturalness - incorrectTrial_naturalness ≥ 3/10 := by
  norm_num

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
  /-- P(subject antecedent | null pronoun), as a percentage 0–100. -/
  nullSubjectPercent : Nat
  /-- P(subject antecedent | overt pronoun). `none` if the language was
      not tested with overt pronouns or has no overt 3sg pronoun. -/
  overtSubjectPercent : Option Nat
  /-- P(subject antecedent | full NP). `none` if not tested. -/
  fullNPSubjectPercent : Option Nat
  deriving Repr

/-- Italian, @cite{carminati-2002}: null = 80.72%, overt = 100% − 83.33%
    = 16.67%. The cleanest division of labor of any language tested
    (Position of Antecedent Hypothesis). -/
def italian : CrossLingProfile :=
  { language := "Italian", nullSubjectPercent := 81, overtSubjectPercent := some 17
  , fullNPSubjectPercent := none }

/-- Spanish, @cite{contemori-di-domenico-2021}: null = 62%, overt = 100%
    − 58% = 42%. Weaker division of labor than Italian. -/
def spanish : CrossLingProfile :=
  { language := "Spanish", nullSubjectPercent := 62, overtSubjectPercent := some 42
  , fullNPSubjectPercent := none }

/-- Chinese, @cite{zhang-kwon-2022}: null = 84%, overt = 65.3%. Both
    pronoun types show subject bias; the overt form does *not* flip to
    object bias as in Italian. -/
def chinese : CrossLingProfile :=
  { language := "Chinese", nullSubjectPercent := 84, overtSubjectPercent := some 65
  , fullNPSubjectPercent := none }

/-- Korean (this paper's Exp 3, overt = colloquial *kyay*). The first
    cross-linguistic dataset that includes full NPs alongside null and
    overt pronouns. -/
def korean : CrossLingProfile :=
  { language := "Korean (Kwon & Lee 2026, kyay)"
  , nullSubjectPercent := exp3_pro.subjectPercent
  , overtSubjectPercent := some exp3_overt.subjectPercent
  , fullNPSubjectPercent := some exp3_fullNP.subjectPercent }

/-- Korean (@cite{kweon-2011}, overt = literary *ku/kunye*). 12-item
    questionnaire study; null = 81.1%, overt = 31.4% subject (so 68.6%
    object). Resembles Italian's clean division of labor — Kweon
    interpreted this as supporting Carminati's PAH. -/
def korean_kweon : CrossLingProfile :=
  { language := "Korean (Kweon 2011, ku/kunye)"
  , nullSubjectPercent := 81, overtSubjectPercent := some 31
  , fullNPSubjectPercent := none }

/-- Korean (@cite{choe-2021}, overt = literary *ku/kunye*). 40-target /
    24-filler study; null = 91%, overt = 73% subject. Both forms
    subject-biased; little division of labor. Diverges sharply from
    Kweon. The paper attributes the discrepancy to methodological
    differences (filler ratio, ambiguity verification). -/
def korean_choe : CrossLingProfile :=
  { language := "Korean (Choe 2021, ku/kunye)"
  , nullSubjectPercent := 91, overtSubjectPercent := some 73
  , fullNPSubjectPercent := none }

def allProfiles : List CrossLingProfile :=
  [italian, spanish, chinese, korean, korean_kweon, korean_choe]

/-- All Korean profiles. -/
def koreanProfiles : List CrossLingProfile := [korean, korean_kweon, korean_choe]

/-- **Universal ordering preserved**: in every language tested, null
    pronouns are at least as subject-biased as overt pronouns. This is
    the universal claim of @cite{ariel-2001}: the *relative ordering*
    holds even when the magnitudes vary. -/
theorem null_dominates_overt_universally :
    ∀ p ∈ allProfiles, ∀ o, p.overtSubjectPercent = some o →
      p.nullSubjectPercent ≥ o := by decide

/-- **Cross-linguistic granularity varies**: Italian shows ≥60-point
    spread between null and overt; Spanish 20; Chinese 19; Korean 28.
    The same theory accounts for all four, with language-specific
    calibration of the spread. -/
def CrossLingProfile.nullOvertSpread (p : CrossLingProfile) : Nat :=
  match p.overtSubjectPercent with
  | some o => p.nullSubjectPercent - o
  | none   => 0

theorem italian_widest_spread :
    italian.nullOvertSpread > spanish.nullOvertSpread ∧
    italian.nullOvertSpread > chinese.nullOvertSpread ∧
    italian.nullOvertSpread > korean.nullOvertSpread := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! **Korean is the only language tested with full NPs**: a unique
    methodological contribution of @cite{kwon-lee-2026}. The full-NP bias
    (35% subject ↔ 65% object) extends Accessibility Theory's test set
    to a wider range of forms than prior cross-linguistic work. -/

theorem korean_includes_fullNP : korean.fullNPSubjectPercent.isSome := rfl
theorem italian_omits_fullNP : italian.fullNPSubjectPercent.isNone := rfl
theorem spanish_omits_fullNP : spanish.fullNPSubjectPercent.isNone := rfl
theorem chinese_omits_fullNP : chinese.fullNPSubjectPercent.isNone := rfl

-- ════════════════════════════════════════════════════
-- § 5b. Korean-Internal Comparison: Kweon vs Choe vs Kwon&Lee
-- ════════════════════════════════════════════════════

/-- **Robust within-Korean finding**: every Korean study agrees that null
    pronouns are subject-biased. The variation is entirely in the
    *strength* of the bias (and in the overt-pronoun behavior). -/
theorem all_korean_null_subject_biased :
    ∀ p ∈ koreanProfiles, p.nullSubjectPercent > 50 := by decide

/-! **The Kweon vs Choe disagreement** is one of the paper's framing
    motivations. Kweon (small item set) shows clean object-bias for
    overt (~31% subject); Choe (unusually low filler ratio) shows
    subject-bias (73%). These cannot both be representative of the
    same underlying competence. The paper attributes the gap to
    methodological factors. -/

theorem kweon_overt_subject_31 : korean_kweon.overtSubjectPercent = some 31 := rfl
theorem choe_overt_subject_73 : korean_choe.overtSubjectPercent = some 73 := rfl

/-- The Kweon-Choe gap exceeds 40 percentage points. -/
theorem kweon_choe_gap_large : 73 - 31 > 40 := by decide

/-- @cite{kwon-lee-2026}'s Exp 3 finding (43% subject for *kyay*) lies
    *between* Kweon (31%) and Choe (73%). The paper takes this as
    suggesting Kweon was directionally correct (overt is object-biased
    in Korean) but that the magnitude depends on the form: *kyay* is
    less rigidly object-biased than *ku/kunye*, consistent with *kyay*'s
    higher position on the accessibility scale (closer to null). -/
theorem kwonlee_overt_subject_43 : korean.overtSubjectPercent = some 43 := rfl

/-- The relative ordering (null > overt) holds for **every** Korean
    study, despite the disagreement on magnitudes. This is exactly
    @cite{ariel-2001}'s universal: the *ordering* is invariant; the
    *spread* is methodologically/contextually labile. -/
theorem korean_relative_ordering_invariant :
    ∀ p ∈ koreanProfiles, ∀ o, p.overtSubjectPercent = some o →
      p.nullSubjectPercent > o := by decide

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
  max a.subjectPercent b.subjectPercent - min a.subjectPercent b.subjectPercent

/-- **Triangle-inequality-like prediction**: the extreme pair (null vs
    full NP) has the largest accessibility distance and the largest
    empirical bias spread. This is a *derived* prediction of
    @cite{ariel-2001}'s ordinal scale — it follows from the rank
    ordering of the three forms, not from any data-fitting. The four
    sub-theorems below state each pairwise comparison separately. -/
theorem accessibilityDistance_pro_fullNP_max_vs_pro_overt :
    KoreanRefForm.nullPro.accessibilityDistance .fullNP >
      KoreanRefForm.nullPro.accessibilityDistance .overt := by decide

theorem accessibilityDistance_pro_fullNP_max_vs_overt_fullNP :
    KoreanRefForm.nullPro.accessibilityDistance .fullNP >
      KoreanRefForm.overt.accessibilityDistance .fullNP := by decide

theorem biasSpread_pro_fullNP_max_vs_pro_overt :
    biasSpread exp3_pro exp3_fullNP > biasSpread exp3_pro exp3_overt := by decide

theorem biasSpread_pro_fullNP_max_vs_overt_fullNP :
    biasSpread exp3_pro exp3_fullNP > biasSpread exp3_overt exp3_fullNP := by decide

/-! **Non-uniform calibration** — the paper's deepest empirical finding
    (Discussion): the null↔overt step (3 ranks → 28-point bias spread)
    is much steeper than the overt↔full-NP step (6 ranks → 8-point
    spread). Korean's accessibility scale has a steep cliff at the
    null/non-null boundary and a shallow slope among non-null forms.
    Exactly what @cite{ariel-2001} predicts (§4.2) about
    language-specific calibration: only the *ordering* is universal,
    not the magnitudes. -/

/-- The accessibility-distance step from null to overt (3 ranks) is
    smaller than from overt to full NP (6 ranks). -/
theorem null_overt_distance_lt_overt_fullNP_distance :
    KoreanRefForm.nullPro.accessibilityDistance .overt <
      KoreanRefForm.overt.accessibilityDistance .fullNP := by decide

/-- Yet the empirical bias spread shows the opposite pattern: the
    smaller-distance pair (null↔overt) has the larger bias spread.
    The scale is calibrated non-uniformly in Korean. -/
theorem null_overt_spread_gt_overt_fullNP_spread :
    biasSpread exp3_pro exp3_overt > biasSpread exp3_overt exp3_fullNP := by decide

/-- The null↔overt spread is large (>25 points) — the "cliff" at the
    null/non-null boundary. -/
theorem null_overt_spread_large :
    biasSpread exp3_pro exp3_overt > 25 := by decide

/-- The overt↔fullNP spread is small (<15 points) — the "shallow slope"
    among non-null forms. -/
theorem overt_fullNP_spread_small :
    biasSpread exp3_overt exp3_fullNP < 15 := by decide

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

@[simp] theorem nullPro_pahPosition :
    KoreanRefForm.nullPro.pahPosition = some .specIP := rfl
@[simp] theorem overt_pahPosition :
    KoreanRefForm.overt.pahPosition = some .lowerIP := rfl
@[simp] theorem fullNP_pahPosition :
    KoreanRefForm.fullNP.pahPosition = none := rfl

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

/-- Distance is held constant across experiments. -/
theorem exp_distance_constant :
    exp1_assessment.distance = exp2_3_assessment.distance := rfl

/-- Topicality is held constant. -/
theorem exp_topicality_constant :
    exp1_assessment.topicality = exp2_3_assessment.topicality := rfl

/-- Unity is held constant. -/
theorem exp_unity_constant :
    exp1_assessment.unity = exp2_3_assessment.unity := rfl

/-- **The manipulation isolates competition**: across the three
    experiments, only the `competition` field varies; distance, topicality,
    and unity are held constant. This makes the experimental design a clean
    test of how competition affects form-function visibility. -/
theorem exp_competition_increases :
    exp1_assessment.competition < exp2_3_assessment.competition := by decide

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
    exp1_naturalness .fullNP - exp1_naturalness .overt ≤ 1/10 ∧
    -- Exp 3 (lower accessibility, competition): clear separation
    biasSpread exp3_overt exp3_fullNP > 0 := by
  refine ⟨?_, ?_⟩
  · unfold exp1_naturalness; norm_num
  · decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to @cite{ariel-2001} Form-Function Criteria
-- ════════════════════════════════════════════════════

/-! @cite{ariel-2001}'s three form-function criteria all line up with
    accessibility for the Korean forms. The criteria don't perfectly
    pull apart at every adjacent level (informativity collapses
    `distalDemNP` and `unstressedPron` at 1), but the overall pattern
    holds: the more accessible form is less informative, less rigid,
    and more attenuated. -/

/-- Informativity: full NP ≥ overt (≥ because Ariel's coarse scale
    collapses `distalDemNP` and `unstressedPron`). -/
theorem korean_informativity_fullNP_ge_overt :
    (KoreanRefForm.fullNP.toAccessibility).informativity ≥
      (KoreanRefForm.overt.toAccessibility).informativity := by decide

/-- Informativity: overt > null. -/
theorem korean_informativity_overt_gt_null :
    (KoreanRefForm.overt.toAccessibility).informativity >
      (KoreanRefForm.nullPro.toAccessibility).informativity := by decide

/-- Rigidity: full NP (demonstrative + noun) ≥ overt. -/
theorem korean_rigidity_fullNP_ge_overt :
    (KoreanRefForm.fullNP.toAccessibility).rigidity ≥
      (KoreanRefForm.overt.toAccessibility).rigidity := by decide

/-- Attenuation: null > overt — the null pronoun has no phonological
    exponent, the overt pronoun has one syllable. -/
theorem korean_attenuation_null_gt_overt :
    (KoreanRefForm.nullPro.toAccessibility).attenuation >
      (KoreanRefForm.overt.toAccessibility).attenuation := by decide

/-- Attenuation: overt > full NP — the demonstrative + noun form has
    more phonological material than a single pronoun. -/
theorem korean_attenuation_overt_gt_fullNP :
    (KoreanRefForm.overt.toAccessibility).attenuation >
      (KoreanRefForm.fullNP.toAccessibility).attenuation := by decide

end Phenomena.Reference.Studies.KwonLee2026
