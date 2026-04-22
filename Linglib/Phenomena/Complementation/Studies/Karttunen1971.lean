import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Causation.Interpretation
import Linglib.Theories.Semantics.Attitudes.Factivity
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Copular

/-!
# Karttunen 1971: Implicative Verbs @cite{karttunen-1971}

Implicative Verbs. Language 47(2): 340–358.

## Core Contribution

Complement-taking predicates that take infinitival complements divide into
**implicative** and **non-implicative** classes based on complement entailment:

- **Implicative** (*manage*, *remember*, *bother*): "managed to VP" → VP;
  "didn't manage to VP" → ¬VP. Two-way entailment.
- **Non-implicative** (*hope*, *want*, *intend*): no complement entailment.
- **Negative implicatives** (*fail*, *forget*): entail ¬complement.
- **Sufficient-only** (*force*, *cause*): affirmative → complement, but
  negation ↛ ¬complement.
- **Necessary-only** (*be able*, *possible*): negation → ¬complement, but
  affirmative ↛ complement.

## Historical Context

Karttunen's 2×2 classification (necessary × sufficient) was the original
descriptive taxonomy. The modern consensus (@cite{nadathur-2023}) derives
the entailment patterns from **causal structure** rather than from
presuppositional schemas. The theory layer (`Causation/Implicative.lean`)
implements the modern causal analysis; this study file preserves
Karttunen's original classification and bridges it to the modern types.

Key differences from the modern analysis:
- Karttunen treats the entailment as arising from a *presupposition* that
  v(S) is a nec/suf condition for S. Nadathur derives it from causal
  sufficiency in a structural equation model.
- Karttunen's classification ignores aspect. Nadathur shows that *be able*
  is aspect-governed (perfective triggers entailment, imperfective doesn't).
- Karttunen groups *force*/*cause*/*make* together (ex. 56) as having
  the same entailment pattern (sufficient-only). Nadathur & Lauer show
  they have the same entailment pattern but **different truth conditions**:
  *make*/*force* assert causal sufficiency, while *cause* asserts causal
  necessity. This difference surfaces in overdetermination scenarios.
-/

namespace Karttunen1971

open Semantics.Causation.Implicative
open Core.Verbs (Causative)
open Fragments.English.Predicates.Verbal
open Fragments.English.Predicates.Copular (beAble)
open Core.Verbs
open Core.Causal

-- ════════════════════════════════════════════════════════════════
-- § 1. Karttunen's Four-Cell Classification (§§9–11)
-- ════════════════════════════════════════════════════════════════

/-! Karttunen's schemas:
    - (37) nec + suf: PRESUP v(S) is nec+suf for S. PROP v(S).
    - (41) nec + suf (neg): same but for ¬S.
    - (54) nec only: PRESUP v(S) is nec for S. PROP v(S).
    - (59) suf only: PRESUP v(S) is suf for S. PROP v(S).
    - neither: no complement entailment. -/

/-- Karttunen's descriptive classification of complement-entailing predicates
    as a 2×2: necessary × sufficient × polarity.

    This is the *historical* taxonomy from the 1971 paper. The modern
    causal analysis uses `ImplicativeClass` (which adds `aspectGoverned`)
    and `Causative` (which distinguishes causal mechanisms). -/
structure KarttunenClass where
  /-- v(S) is sufficient for S: affirmative entails complement. -/
  isSufficient : Bool
  /-- v(S) is necessary for S: negation entails ¬complement. -/
  isNecessary : Bool
  /-- Positive (*manage*: entails S) vs negative (*fail*: entails ¬S). -/
  polarity : Implicative
  deriving DecidableEq, Repr

-- ── Instances ──

def KarttunenClass.manage : KarttunenClass :=
  { isSufficient := true, isNecessary := true, polarity := .positive }

def KarttunenClass.fail : KarttunenClass :=
  { isSufficient := true, isNecessary := true, polarity := .negative }

/-- Sufficient only: "forced X to VP" → VP; "didn't force" ↛ ¬VP. -/
def KarttunenClass.force : KarttunenClass :=
  { isSufficient := true, isNecessary := false, polarity := .positive }

/-- Sufficient only, negative: "prevented X from VP-ing" → ¬VP. -/
def KarttunenClass.prevent : KarttunenClass :=
  { isSufficient := true, isNecessary := false, polarity := .negative }

/-- Necessary only: "wasn't able to VP" → ¬VP; "was able" ↛ VP. -/
def KarttunenClass.beAble : KarttunenClass :=
  { isSufficient := false, isNecessary := true, polarity := .positive }

/-- Neither: *hope*, *want*, *intend*. -/
def KarttunenClass.hope : KarttunenClass :=
  { isSufficient := false, isNecessary := false, polarity := .positive }

-- ── Derived predicates ──

def KarttunenClass.isTwoWay (k : KarttunenClass) : Bool :=
  k.isNecessary && k.isSufficient

def KarttunenClass.hasEntailment (k : KarttunenClass) : Bool :=
  k.isNecessary || k.isSufficient

-- ── Classification theorems ──

theorem manage_isTwoWay : KarttunenClass.manage.isTwoWay = true := rfl
theorem fail_isTwoWay : KarttunenClass.fail.isTwoWay = true := rfl
theorem force_not_twoWay : KarttunenClass.force.isTwoWay = false := rfl
theorem beAble_not_twoWay : KarttunenClass.beAble.isTwoWay = false := rfl
theorem hope_no_entailment : KarttunenClass.hope.hasEntailment = false := rfl

/-- *manage* and *fail* differ only in polarity. -/
theorem manage_fail_same_profile :
    KarttunenClass.manage.isNecessary = KarttunenClass.fail.isNecessary ∧
    KarttunenClass.manage.isSufficient = KarttunenClass.fail.isSufficient ∧
    KarttunenClass.manage.polarity ≠ KarttunenClass.fail.polarity := by
  exact ⟨rfl, rfl, by decide⟩

/-- *force* and *prevent* differ only in polarity. -/
theorem force_prevent_same_profile :
    KarttunenClass.force.isNecessary = KarttunenClass.prevent.isNecessary ∧
    KarttunenClass.force.isSufficient = KarttunenClass.prevent.isSufficient ∧
    KarttunenClass.force.polarity ≠ KarttunenClass.prevent.polarity := by
  exact ⟨rfl, rfl, by decide⟩

-- ════════════════════════════════════════════════════════════════
-- § 2. Bridge to Modern Classification (@cite{nadathur-2023})
-- ════════════════════════════════════════════════════════════════

/-- Convert KarttunenClass to ImplicativeClass (Nadathur 2023).
    Note: `aspectGoverned` is always false because Karttunen's 1971
    analysis does not account for aspect — a limitation the modern
    analysis corrects. -/
def KarttunenClass.toImplicativeClass (k : KarttunenClass) : ImplicativeClass :=
  { polarity := k.polarity
    directionality := if k.isTwoWay then .twoWay else .oneWay
    aspectGoverned := false
    prerequisite := if k.isTwoWay then some .unspecified else none }

theorem karttunen_manage_matches :
    KarttunenClass.manage.toImplicativeClass = ImplicativeClass.manage := rfl

theorem karttunen_fail_matches :
    KarttunenClass.fail.toImplicativeClass = ImplicativeClass.fail := rfl

/-- Derive KarttunenClass from an Implicative (two-way cell). -/
def karttunenOfImplicative (b : Implicative) : KarttunenClass :=
  { isSufficient := true, isNecessary := true, polarity := b }

/-- Map modern `Causative` to the Karttunen cell that matches the
    builder's **entailment pattern** (Karttunen's original criterion).

    All positive causative builders (make, force, enable, cause) share the
    same Karttunen cell: sufficient-only. This is because:
    - Affirmative "V-ed X to VP" → VP (all require the effect occurred)
    - Negation "didn't V X to VP" ↛ ¬VP (effect might occur from other causes)

    The modern insight of @cite{nadathur-lauer-2020} is that these verbs
    differ in causal MECHANISM (sufficiency vs necessity) despite sharing
    the same ENTAILMENT PATTERN. See `cause_make_same_cell_different_mechanism`. -/
def karttunenOfCausative : Causative → KarttunenClass
  | .make | .force | .enable | .cause =>
    { isSufficient := true, isNecessary := false, polarity := .positive }
  | .prevent =>
    { isSufficient := true, isNecessary := false, polarity := .negative }

theorem manage_karttunen_class :
    karttunenOfImplicative .positive = KarttunenClass.manage := rfl

theorem fail_karttunen_class :
    karttunenOfImplicative .negative = KarttunenClass.fail := rfl

theorem force_karttunen_class :
    karttunenOfCausative .force = KarttunenClass.force := rfl

theorem prevent_karttunen_class :
    karttunenOfCausative .prevent = KarttunenClass.prevent := rfl

/-- `cause` and `make` have the same Karttunen entailment cell
    (sufficient-only) despite having different causal mechanisms.
    This is the central insight of @cite{nadathur-lauer-2020}: same
    entailment pattern ≠ same truth conditions. The difference emerges
    in overdetermination scenarios where `makeSem` is true but `causeSem`
    is false (see `truth_conditionally_distinct` in Interpretation.lean). -/
theorem cause_make_same_cell_different_mechanism :
    karttunenOfCausative .cause = karttunenOfCausative .make ∧
    Causative.cause.assertsNecessity ≠ Causative.make.assertsNecessity := by
  exact ⟨rfl, by decide⟩

/-- All positive causative builders map to `KarttunenClass.force`
    (Karttunen's sufficient-only cell). -/
theorem cause_karttunen_class :
    karttunenOfCausative .cause = KarttunenClass.force := rfl

-- ════════════════════════════════════════════════════════════════
-- § 3. Fragment Verification (ex. 2)
-- ════════════════════════════════════════════════════════════════

/-! Verify that Fragment verb entries carry the correct annotations,
    matching Karttunen's inventory (ex. 2, p.341). -/

-- ── Positive implicatives ──

theorem manage_positive_implicative :
    manage.toVerbCore.implicative = some .positive := rfl

theorem remember_positive_implicative :
    remember.toVerbCore.implicative = some .positive := rfl

theorem dare_positive_implicative :
    dare.toVerbCore.implicative = some .positive := rfl

theorem bother_positive_implicative :
    bother.toVerbCore.implicative = some .positive := rfl

theorem venture_positive_implicative :
    venture.toVerbCore.implicative = some .positive := rfl

theorem condescend_positive_implicative :
    condescend.toVerbCore.implicative = some .positive := rfl

theorem happen_positive_implicative :
    happen.toVerbCore.implicative = some .positive := rfl

-- ── Negative implicatives (§10, ex. 38) ──

theorem fail_negative_implicative :
    fail.toVerbCore.implicative = some .negative := rfl

theorem forget_negative_implicative :
    forget.toVerbCore.implicative = some .negative := rfl

theorem neglect_negative_implicative :
    neglect.toVerbCore.implicative = some .negative := rfl

-- ── Non-implicatives ──

theorem hope_not_implicative :
    hope.toVerbCore.implicative = none := rfl

theorem want_not_implicative :
    want.toVerbCore.implicative = none := rfl

theorem try_not_implicative :
    try_.toVerbCore.implicative = none := rfl

theorem believe_not_implicative :
    believe.toVerbCore.implicative = none := rfl

-- ── Derived entailment predictions ──

theorem manage_entails :
    manage.toVerbCore.entailsComplement = some true := by native_decide

theorem fail_entails_not :
    fail.toVerbCore.entailsComplement = some false := by native_decide

theorem hope_no_complement_entailment :
    hope.toVerbCore.entailsComplement = none := rfl

-- ── Raising vs control ──

/-- *happen* is a raising verb, not subject-control. "It happened to rain"
    is grammatical — the matrix subject receives no theta role from *happen*.
    Karttunen (§9) describes *happen*'s presupposition as chance-dependence,
    but does not discuss its syntactic control type. -/
theorem happen_is_raising :
    happen.toVerbCore.controlType = .raising := rfl

/-- *dare* and *bother* have both presupposition (occasion verbs) AND
    implicative entailment: "John dared to speak" presupposes risk AND
    entails "John spoke." These are compatible per Karttunen §9. -/
theorem dare_presup_and_implicative :
    dare.toVerbCore.presupType = some .prerequisiteSoft ∧
    dare.toVerbCore.implicative = some .positive := ⟨rfl, rfl⟩

theorem bother_presup_and_implicative :
    bother.toVerbCore.presupType = some .prerequisiteSoft ∧
    bother.toVerbCore.implicative = some .positive := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Factive vs Implicative (§§0–2)
-- ════════════════════════════════════════════════════════════════

/-! The key diagnostic: factives preserve complement presupposition under
    negation; implicatives *reverse* the complement entailment.

    "John didn't realize he had no money" — still presupposes "he had no money."
    "John didn't manage to solve it" — entails "he didn't solve it." -/

theorem know_factive_not_implicative :
    know.toVerbCore.presupType = some .softTrigger ∧
    know.toVerbCore.implicative = none := ⟨rfl, rfl⟩

theorem manage_implicative_not_factive :
    manage.toVerbCore.implicative = some .positive ∧
    manage.toVerbCore.presupType = some .prerequisiteSoft := ⟨rfl, rfl⟩

theorem hope_neither :
    hope.toVerbCore.presupType = none ∧
    hope.toVerbCore.implicative = none := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Sufficient-Only Verbs (§11, ex. 56–59)
-- ════════════════════════════════════════════════════════════════

theorem force_has_causative :
    force.toVerbCore.causative = some .force := rfl

theorem force_asserts_sufficiency :
    Causative.force.assertsSufficiency = true := rfl

theorem force_no_necessity :
    Causative.force.assertsNecessity = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. KarttunenClass → Entailment Predictions
-- ════════════════════════════════════════════════════════════════

/-! The grounding chain: KarttunenClass → Implicative →
    causal semantics → complement entailment.

    For sufficient-positive classes, the chain is:
    `KarttunenClass.manage.polarity` = `.positive`
    → `Implicative.positive.toSemantics` = `manageSem`
    → `manage_entails_complement`: manageSem sc → complement true

    These theorems derive the entailment from the classification,
    not just re-export the theory-layer theorem. -/

/-- A sufficient-positive KarttunenClass predicts complement truth
    via the polarity field's grounded semantics. -/
theorem sufficient_positive_class_entails (sc : ImplicativeScenario)
    (k : KarttunenClass)
    (_hSuf : k.isSufficient = true) (hPol : k.polarity = .positive)
    (hSem : k.polarity.toSemantics sc) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true := by
  rw [hPol] at hSem
  exact manage_entails_complement sc hSem

/-- A sufficient-negative KarttunenClass predicts complement falsity. -/
theorem sufficient_negative_class_entails (sc : ImplicativeScenario)
    (k : KarttunenClass)
    (_hSuf : k.isSufficient = true) (hPol : k.polarity = .negative)
    (hSem : k.polarity.toSemantics sc) :
    ¬ (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true := by
  rw [hPol] at hSem
  exact fail_entails_not_complement sc hSem

/-- Instantiation: `KarttunenClass.manage` entails complement truth. -/
theorem manage_class_entails (sc : ImplicativeScenario)
    (hSem : KarttunenClass.manage.polarity.toSemantics sc) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true :=
  sufficient_positive_class_entails sc .manage rfl rfl hSem

/-- Instantiation: `KarttunenClass.fail` entails complement falsity. -/
theorem fail_class_entails (sc : ImplicativeScenario)
    (hSem : KarttunenClass.fail.polarity.toSemantics sc) :
    ¬ (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true :=
  sufficient_negative_class_entails sc .fail rfl rfl hSem

-- ════════════════════════════════════════════════════════════════
-- § 7. Double Negation (§2, ex. 13; §10, ex. 40)
-- ════════════════════════════════════════════════════════════════

/-! Double negation cancellation is a signature property of implicative
    verbs. Karttunen's examples:

    - (13) "John didn't remember not to lock his door" → "John locked his door."
    - (40a) "John didn't forget to lock his door" → (40d) "John locked his door."

    The current causal semantics models the *positive* direction
    (manageSem → complement true) and the *negative* direction
    (failSem → complement false) separately. Full double negation
    — where matrix negation and complement negation interact to yield
    a positive entailment — would require compositional negation over
    the causal model, which is not yet formalized.

    What we CAN verify: the two directions (positive entailment, negative
    entailment) are separately grounded, and two-way KarttunenClasses
    predict both directions. -/

/-- Two-way classes predict entailment in BOTH directions:
    the positive polarity grounds the affirmative direction,
    the negative polarity grounds the negation direction. -/
theorem two_way_has_both_directions (k : KarttunenClass)
    (hTwoWay : k.isTwoWay = true) :
    k.isSufficient = true ∧ k.isNecessary = true := by
  simp only [KarttunenClass.isTwoWay, Bool.and_eq_true] at hTwoWay
  exact ⟨hTwoWay.2, hTwoWay.1⟩

-- ════════════════════════════════════════════════════════════════
-- § 8. Coverage Summary
-- ════════════════════════════════════════════════════════════════

/-- All four cells of the 2×2 are populated by Fragment entries. -/
theorem all_cells_populated :
    KarttunenClass.manage.isTwoWay = true ∧     -- nec + suf: manage
    KarttunenClass.force.isTwoWay = false ∧      -- suf only: force
    KarttunenClass.beAble.isTwoWay = false ∧     -- nec only: be able
    KarttunenClass.hope.hasEntailment = false :=  -- neither: hope
  ⟨rfl, rfl, rfl, rfl⟩

-- ── Necessary-only cell: be able (§11, schema 54) ──

/-- *be able* is NOT a lexical implicative — it has no `implicative`.
    The actuality entailment is **aspect-governed** (@cite{nadathur-2023}):
    perfective "was able to VP" → VP; imperfective "was able to VP" ↛ VP.
    Karttunen (§11) notes these verbs are ambiguous between implicative
    and non-implicative readings. -/
theorem beAble_not_lexical_implicative :
    beAble.implicative = none := rfl

/-- *be able* takes infinitival complement with subject control.
    "He was able to leave" — the subject has the ability (theta role). -/
theorem beAble_infinitival_subject_control :
    beAble.complementType = .infinitival ∧
    beAble.controlType = .subjectControl := ⟨rfl, rfl⟩

/-! ### Tension with Noonan's Reality Status

    @cite{noonan-2007} classifies achievement CTPs (*manage*, *fail*) as
    IRREALIS because they take infinitival complements. But Karttunen shows
    these verbs ENTAIL complement truth — semantically realis. Complement
    *form* (irrealis) and complement *entailment* (realis) diverge for
    implicative verbs. -/

end Karttunen1971
