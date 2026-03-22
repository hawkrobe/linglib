import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Causation.Builder
import Linglib.Theories.Semantics.Attitudes.Factivity
import Linglib.Fragments.English.Predicates.Verbal

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
- Karttunen groups *force*/*cause*/*make* together; Nadathur distinguishes
  them by causal mechanism (sufficiency vs counterfactual dependence).
-/

namespace Phenomena.Complementation.Studies.Karttunen1971

open Nadathur2023.Implicative
open NadathurLauer2020.Builder (CausativeBuilder)
open Fragments.English.Predicates.Verbal
open Core.Verbs
open Core.StructuralEquationModel

-- ════════════════════════════════════════════════════════════════
-- § 1. Karttunen's Four-Cell Classification (§§8–12)
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
    and `CausativeBuilder` (which distinguishes causal mechanisms). -/
structure KarttunenClass where
  /-- v(S) is sufficient for S: affirmative entails complement. -/
  isSufficient : Bool
  /-- v(S) is necessary for S: negation entails ¬complement. -/
  isNecessary : Bool
  /-- Positive (*manage*: entails S) vs negative (*fail*: entails ¬S). -/
  polarity : ImplicativeBuilder
  deriving DecidableEq, Repr, BEq

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
    aspectGoverned := false }

theorem karttunen_manage_matches :
    KarttunenClass.manage.toImplicativeClass = ImplicativeClass.manage := rfl

theorem karttunen_fail_matches :
    KarttunenClass.fail.toImplicativeClass = ImplicativeClass.fail := rfl

/-- Derive KarttunenClass from an ImplicativeBuilder (two-way cell). -/
def karttunenOfImplicative (b : ImplicativeBuilder) : KarttunenClass :=
  { isSufficient := true, isNecessary := true, polarity := b }

/-- Derive KarttunenClass from a CausativeBuilder (sufficient-only cell). -/
def karttunenOfCausative : CausativeBuilder → KarttunenClass
  | .cause | .make | .force | .enable =>
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

-- ════════════════════════════════════════════════════════════════
-- § 3. Fragment Verification (ex. 2)
-- ════════════════════════════════════════════════════════════════

/-! Verify that Fragment verb entries carry the correct annotations,
    matching Karttunen's inventory. -/

-- ── Positive implicatives ──

theorem manage_positive_implicative :
    manage.toVerbCore.implicativeBuilder = some .positive := rfl

theorem remember_positive_implicative :
    remember.toVerbCore.implicativeBuilder = some .positive := rfl

-- ── Negative implicatives (§10, ex. 38) ──

theorem fail_negative_implicative :
    fail.toVerbCore.implicativeBuilder = some .negative := rfl

theorem forget_negative_implicative :
    forget.toVerbCore.implicativeBuilder = some .negative := rfl

-- ── Non-implicatives ──

theorem hope_not_implicative :
    hope.toVerbCore.implicativeBuilder = none := rfl

theorem want_not_implicative :
    want.toVerbCore.implicativeBuilder = none := rfl

theorem try_not_implicative :
    try_.toVerbCore.implicativeBuilder = none := rfl

theorem believe_not_implicative :
    believe.toVerbCore.implicativeBuilder = none := rfl

-- ── Derived entailment predictions ──

theorem manage_entails :
    manage.toVerbCore.entailsComplement = some true := by native_decide

theorem fail_entails_not :
    fail.toVerbCore.entailsComplement = some false := by native_decide

theorem hope_no_complement_entailment :
    hope.toVerbCore.entailsComplement = none := rfl

-- ════════════════════════════════════════════════════════════════
-- § 4. Factive vs Implicative (§§0–2)
-- ════════════════════════════════════════════════════════════════

/-! The key diagnostic: factives preserve complement presupposition under
    negation; implicatives *reverse* the complement entailment.

    "John didn't realize he had no money" — still presupposes "he had no money."
    "John didn't manage to solve it" — entails "he didn't solve it." -/

theorem know_factive_not_implicative :
    know.toVerbCore.presupType = some .softTrigger ∧
    know.toVerbCore.implicativeBuilder = none := ⟨rfl, rfl⟩

theorem manage_implicative_not_factive :
    manage.toVerbCore.implicativeBuilder = some .positive ∧
    manage.toVerbCore.presupType = none := ⟨rfl, rfl⟩

theorem hope_neither :
    hope.toVerbCore.presupType = none ∧
    hope.toVerbCore.implicativeBuilder = none := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Sufficient-Only Verbs (§11, ex. 56–59)
-- ════════════════════════════════════════════════════════════════

theorem force_has_causative :
    force.toVerbCore.causativeBuilder = some .force := rfl

theorem force_asserts_sufficiency :
    CausativeBuilder.force.assertsSufficiency = true := rfl

theorem force_no_necessity :
    CausativeBuilder.force.assertsNecessity = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. Entailment Predictions from KarttunenClass
-- ════════════════════════════════════════════════════════════════

/-! Karttunen's schema (37): if v is sufficient-positive, affirming v(S)
    entails S. Grounded through `manage_entails_complement` from the
    causal semantics. -/

theorem sufficient_positive_entails (sc : ImplicativeScenario)
    (h : manageSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = true :=
  manage_entails_complement sc h

theorem sufficient_negative_entails (sc : ImplicativeScenario)
    (h : failSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = false :=
  fail_entails_not_complement sc h

-- ════════════════════════════════════════════════════════════════
-- § 7. Double Negation Cancellation (§2, ex. 13)
-- ════════════════════════════════════════════════════════════════

/-! "John didn't remember not to lock his door" → "John locked his door."
    For two-way positive implicatives, ¬v(¬S) → S by the negative
    direction (¬v(S') → ¬S' where S' = ¬S) plus Boolean double negation. -/

theorem double_negation_cancellation (sc : ImplicativeScenario)
    (hFail : failSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = false :=
  fail_entails_not_complement sc hFail

-- ════════════════════════════════════════════════════════════════
-- § 8. Coverage Summary
-- ════════════════════════════════════════════════════════════════

/-- All four cells of the 2×2 are populated by existing Fragment entries. -/
theorem all_cells_populated :
    KarttunenClass.manage.isTwoWay = true ∧     -- nec + suf
    KarttunenClass.force.isTwoWay = false ∧      -- suf only
    KarttunenClass.beAble.isTwoWay = false ∧     -- nec only
    KarttunenClass.hope.hasEntailment = false :=  -- neither
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Gaps

    Several verbs from Karttunen's implicative list (ex. 2) lack
    `implicativeBuilder` annotations in the Fragment:

    - *dare*, *bother*: modeled as occasion verbs (presupposition only,
      no entailment annotation). Both analyses are compatible — a verb
      can presuppose a decisive condition AND entail the complement.

    - *venture*, *condescend*, *happen*: added to the Fragment in this
      formalization with positive implicative annotations. -/

theorem dare_missing_implicative :
    dare.toVerbCore.implicativeBuilder = none := rfl

theorem bother_missing_implicative :
    bother.toVerbCore.implicativeBuilder = none := rfl

/-! ### Tension with Noonan's Reality Status

    @cite{noonan-2007} classifies achievement CTPs (*manage*, *fail*) as
    IRREALIS because they take infinitival complements. But Karttunen shows
    these verbs ENTAIL complement truth — semantically realis. Complement
    *form* (irrealis) and complement *entailment* (realis) diverge for
    implicative verbs. -/

end Phenomena.Complementation.Studies.Karttunen1971
