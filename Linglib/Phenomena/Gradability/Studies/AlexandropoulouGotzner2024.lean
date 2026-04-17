import Linglib.Theories.Semantics.Gradability.Theory
import Linglib.Theories.Semantics.Gradability.Antonymy
import Linglib.Fragments.English.Predicates.Adjectival
/-!
# @cite{alexandropoulou-gotzner-2024} — Negated Gradable Adjectives
@cite{alexandropoulou-gotzner-2024}

Extension gap (contrary antonyms, two thresholds) is the structural
precondition for polarity asymmetry under negation. Contradictory antonyms
(single threshold) produce symmetric negation.

## Load-bearing connections

- `positiveMeaning'` / `contraryNegMeaning` (Theory.lean) = `positiveMeaning` /
  `negativeMeaning` (Core.lean) applied to ThresholdPair projections (§4)
- Three-region exhaustive partition from `ThresholdPair` (§5)
- Contradictory complement: `positiveMeaning` ∨ `antonymMeaning` always (§6)
- `positiveMeaning_monotone` grounds strength entailment and precision DPL (§7, §9)
-/

set_option autoImplicit false

namespace AlexandropoulouGotzner2024

open Core (NegationType)
open Core.Scale (Boundedness Degree Threshold
  Degree.toNat Threshold.toNat deg thr)
open Semantics.Gradability (GradableAdjEntry InformationalStrength
  ThresholdPair inGapRegion positiveMeaning' contraryNegMeaning contraryNeg)
open Semantics.Degree (positiveMeaning negativeMeaning antonymMeaning
  positiveMeaning_monotone)
open Fragments.English.Predicates.Adjectival
  (large small gigantic tiny clean dirty pristine filthy)
-- ============================================================================
-- § 1. Experimental Design & Stimuli
-- ============================================================================

inductive EvaluativePolarity where
  | positive | negative
  deriving Repr, DecidableEq

def classifyAdj (entry : GradableAdjEntry) : Bool :=
  match entry.antonymRelation with
  | some .contrary => true
  | _              => false

structure Condition where
  adjective : GradableAdjEntry
  strength  : InformationalStrength
  polarity  : EvaluativePolarity
  negated   : Bool
  deriving Repr

structure AdjQuadruple where
  weakPos    : GradableAdjEntry
  weakNeg    : GradableAdjEntry
  strongPos  : GradableAdjEntry
  strongNeg  : GradableAdjEntry
  isRelative : Bool
  deriving Repr

def sizeQuad : AdjQuadruple where
  weakPos := large; weakNeg := small; strongPos := gigantic; strongNeg := tiny
  isRelative := true

def cleanlinessQuad : AdjQuadruple where
  weakPos := clean; weakNeg := dirty; strongPos := pristine; strongNeg := filthy
  isRelative := false

-- ============================================================================
-- § 2. Scale Model
-- ============================================================================

abbrev Deg5 := Degree 4
abbrev Thr5 := Threshold 4

structure RelativeScale where
  θ_pos : Thr5
  θ_neg : Thr5
  gap : θ_neg ≤ θ_pos

def defaultRelativeScale : RelativeScale where
  θ_pos := thr 2; θ_neg := thr 1; gap := by decide

def notPositiveRel (d : Deg5) (s : RelativeScale) : Bool :=
  d ≤ (s.θ_pos : Degree 4)

def notNegativeRel (d : Deg5) (s : RelativeScale) : Bool :=
  (s.θ_neg : Degree 4) ≤ d

-- ============================================================================
-- § 3. Definitional Equivalences: Theory.lean ↔ Core.lean
-- ============================================================================

/-! The two-threshold model (Theory.lean) and single-threshold model (Core.lean)
    define comparison operators independently. These `rfl` proofs verify that
    the definitions agree — changing either module's definition body breaks them.
    This is the structural backbone connecting the study to shared infrastructure
    that @cite{tessler-franke-2019} also uses. -/

/-- Two-threshold positive IS single-threshold positive at θ_pos.
    Both compute `(θ : Degree max) < d`. -/
theorem positive'_eq_positiveMeaning {max : Nat}
    (d : Degree max) (tp : ThresholdPair max) :
    positiveMeaning' d tp = positiveMeaning d tp.pos := rfl

/-- Two-threshold contrary negative IS single-threshold negative at θ_neg.
    Both compute `d < (θ : Degree max)`. -/
theorem contraryNeg_eq_negativeMeaning {max : Nat}
    (d : Degree max) (tp : ThresholdPair max) :
    contraryNegMeaning d tp = negativeMeaning d tp.neg := rfl

/-- A&G's "not large" IS Core.lean's antonymMeaning at θ_pos.
    Both compute `d ≤ (θ : Degree max)`. -/
theorem notPositiveRel_eq_antonymMeaning (d : Deg5) (s : RelativeScale) :
    notPositiveRel d s = antonymMeaning d s.θ_pos := rfl

/-- Theory.lean's `contraryNeg` IS Core.lean's `negativeMeaning`.
    Both compute `d < (θ : Degree max)`. -/
theorem contraryNeg_eq_negativeMeaning' {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    contraryNeg d θ = negativeMeaning d θ := rfl

-- ============================================================================
-- § 4. Three-Region Partition
-- ============================================================================

/-! For contrary antonyms (ThresholdPair), the scale partitions into three
    regions: positive, gap, and negative. The gap is WHERE "not positive"
    diverges from "negative" — the structural basis for polarity asymmetry. -/

/-- Every degree falls in at least one of {positive, gap, negative}. -/
theorem three_region_exhaustive {max : Nat}
    (tp : ThresholdPair max) (d : Degree max) :
    positiveMeaning' d tp = true ∨
    inGapRegion d tp = true ∨
    contraryNegMeaning d tp = true := by
  simp only [positiveMeaning', inGapRegion, contraryNegMeaning,
             decide_eq_true_eq, Bool.and_eq_true]
  by_cases h1 : (tp.pos : Degree max) < d
  · exact Or.inl h1
  · by_cases h2 : d < (tp.neg : Degree max)
    · exact Or.inr (Or.inr h2)
    · push_neg at h1 h2
      exact Or.inr (Or.inl ⟨h2, h1⟩)

/-- Gap region excludes the positive region. -/
theorem gap_not_positive {max : Nat}
    (tp : ThresholdPair max) (d : Degree max)
    (h : inGapRegion d tp = true) :
    positiveMeaning' d tp = false := by
  simp only [positiveMeaning', inGapRegion, Bool.and_eq_true, decide_eq_true_eq,
             decide_eq_false_iff_not, not_lt] at *
  exact h.2

/-- Gap region excludes the negative region. -/
theorem gap_not_negative {max : Nat}
    (tp : ThresholdPair max) (d : Degree max)
    (h : inGapRegion d tp = true) :
    contraryNegMeaning d tp = false := by
  simp only [contraryNegMeaning, inGapRegion, Bool.and_eq_true, decide_eq_true_eq,
             decide_eq_false_iff_not, not_lt] at *
  exact h.1

/-- Gap = "not positive" ∧ "not negative" (biconditional).
    Connects `inGapRegion` (Theory.lean) to `positiveMeaning'` and
    `contraryNegMeaning` (also Theory.lean, but equivalent to Core.lean
    by §3 equivalences). -/
theorem gap_iff_neither {max : Nat}
    (tp : ThresholdPair max) (d : Degree max) :
    inGapRegion d tp = true ↔
    (positiveMeaning' d tp = false ∧ contraryNegMeaning d tp = false) := by
  constructor
  · exact fun h => ⟨gap_not_positive tp d h, gap_not_negative tp d h⟩
  · intro ⟨hp, hn⟩
    simp only [inGapRegion, positiveMeaning', contraryNegMeaning,
               Bool.and_eq_true, decide_eq_true_eq,
               decide_eq_false_iff_not, not_lt] at *
    exact ⟨hn, hp⟩

-- ============================================================================
-- § 5. Contradictory Complement: Why Absolutes Are Symmetric
-- ============================================================================

/-! For contradictory antonyms (single θ), positive and antonym are
    complements: every degree satisfies exactly one. No gap is possible.
    This is WHY absolute adjectives show symmetric negation (Exp 2). -/

/-- Contradictory antonyms partition the scale with no gap.
    Now derived from `Antonymy.contradictory_exhaustive`. -/
theorem contradictory_complement {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    positiveMeaning d θ = true ∨ antonymMeaning d θ = true :=
  Semantics.Gradability.Antonymy.contradictory_exhaustive d θ

/-- `antonymMeaning` IS the Boolean complement of `positiveMeaning`.
    Now derived from `Antonymy.contradictory_is_complement`. -/
theorem contradictory_is_complement {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    antonymMeaning d θ = !positiveMeaning d θ :=
  Semantics.Gradability.Antonymy.contradictory_is_complement d θ

-- ============================================================================
-- § 6. Monotonicity → Strength & Precision
-- ============================================================================

/-! `positiveMeaning_monotone` (Core.lean): higher threshold → informationally
    stronger. This single theorem grounds BOTH:
    1. Strong adjectives entail weak (gigantic → large)
    2. Precision upshift entails standard (pristine-reading → clean-reading) -/

/-- Strong adjectives entail weak: anything above θ_strong is above θ_weak.
    Directly applies `positiveMeaning_monotone` from Core.lean. -/
theorem strong_entails_weak (θ_weak θ_strong : Thr5)
    (h_ord : θ_weak ≤ θ_strong) (d : Deg5)
    (h_strong : positiveMeaning d θ_strong = true) :
    positiveMeaning d θ_weak = true :=
  positiveMeaning_monotone d θ_weak θ_strong h_ord h_strong

/-- Concrete: degree 4 is positive under the weak threshold (thr 2) BECAUSE
    it's positive under the strong threshold (thr 3) and monotonicity applies.
    This is a genuinely load-bearing proof: it chains Core.lean's monotonicity
    theorem through concrete threshold values. -/
theorem gigantic_entails_large :
    positiveMeaning (deg 4 : Deg5) (thr 2 : Thr5) = true :=
  positiveMeaning_monotone (deg 4) (thr 2 : Thr5) (thr 3 : Thr5) (by decide) (by native_decide)

/-- Precision upshift entails standard reading, by monotonicity.
    If d satisfies "clean" at pristine precision (θ = 3), it satisfies
    "clean" at standard precision (θ = 1). Same theorem, different reading. -/
theorem precision_entails_standard (d : Deg5)
    (h : positiveMeaning d (thr 3 : Thr5) = true) :
    positiveMeaning d (thr 1 : Thr5) = true :=
  positiveMeaning_monotone d (thr 1 : Thr5) (thr 3 : Thr5) (by decide) h

-- ============================================================================
-- § 7. Concrete Predictions (Exp 1–2)
-- ============================================================================

/-- Exp 1: "not large" at degree 0 overlaps with "small" → negative
    strengthening. -/
theorem negative_strengthening :
    let s := defaultRelativeScale
    let tp : ThresholdPair 4 := ⟨s.θ_pos, s.θ_neg, s.gap⟩
    notPositiveRel (deg 0) s = true ∧
    contraryNegMeaning (deg 0) tp = true := by native_decide

/-- Exp 1: "not small" at degree 2 is in the gap → middling reading. -/
theorem middling_reading :
    let s := defaultRelativeScale
    let tp : ThresholdPair 4 := ⟨s.θ_pos, s.θ_neg, s.gap⟩
    notNegativeRel (deg 2) s = true ∧
    positiveMeaning' (deg 2) tp = false ∧
    contraryNegMeaning (deg 2) tp = false := by native_decide

/-- Exp 1: Polarity asymmetry — strengthening witness AND middling witness. -/
theorem polarity_asymmetry :
    let s := defaultRelativeScale
    let tp : ThresholdPair 4 := ⟨s.θ_pos, s.θ_neg, s.gap⟩
    (∃ d : Deg5, notPositiveRel d s = true ∧ contraryNegMeaning d tp = true) ∧
    (∃ d : Deg5, notNegativeRel d s = true ∧ positiveMeaning' d tp = false ∧
                 contraryNegMeaning d tp = false) := by
  exact ⟨⟨deg 0, by native_decide, by native_decide⟩,
         ⟨deg 2, by native_decide, by native_decide, by native_decide⟩⟩

/-- Exp 1: Gap witnesses contrary non-entailment (eqs. 6a-b). -/
theorem contrary_nonentailment :
    let s := defaultRelativeScale
    let tp : ThresholdPair 4 := ⟨s.θ_pos, s.θ_neg, s.gap⟩
    (∃ d : Deg5, notPositiveRel d s = true ∧ contraryNegMeaning d tp = false) ∧
    (∃ d : Deg5, notNegativeRel d s = true ∧ positiveMeaning' d tp = false) := by
  exact ⟨⟨deg 2, by native_decide, by native_decide⟩,
         ⟨deg 2, by native_decide, by native_decide⟩⟩

/-- Exp 1: Strength invariance — gap depends on antonym type, not threshold. -/
theorem strength_invariance :
    classifyAdj large = classifyAdj gigantic ∧
    classifyAdj small = classifyAdj tiny := by
  simp [classifyAdj, large, small, gigantic, tiny]

/-- Exp 2: Absolute adjectives symmetric — `contradictory_complement` on Deg5. -/
theorem absolute_symmetric :
    ∀ (d : Deg5), positiveMeaning d (thr 2) = true ∨
                  antonymMeaning d (thr 2) = true := by
  native_decide

-- ============================================================================
-- § 8. Precision-Level DPL (§4.2)
-- ============================================================================

/-! "clean" in competition with "not clean" takes high-precision reading
    ≈ "pristine" (θ raised from 1 to 3). This creates a gap, explaining
    Table 7's relative-like behavior for absolutes. The entailment
    pristine-clean → standard-clean follows from `positiveMeaning_monotone`
    (§6). -/

/-- ThresholdPair for the precision-upshifted "clean" scale:
    θ_pos = 3 (pristine precision), θ_neg = 1 (filthy threshold). -/
def precisionTP : ThresholdPair 4 :=
  ⟨⟨⟨3, by omega⟩⟩, (thr 1 : Thr5), by decide⟩

/-- Precision upshift creates a gap at degree 2. -/
theorem precision_gap :
    inGapRegion (deg 2) precisionTP = true := by native_decide

/-- The precision gap is genuine: degree 2 satisfies neither positive
    (at pristine precision) nor negative. Uses `gap_iff_neither` from §4. -/
theorem precision_gap_is_neither :
    positiveMeaning' (deg 2) precisionTP = false ∧
    contraryNegMeaning (deg 2) precisionTP = false :=
  (gap_iff_neither _ _).mp (by native_decide)

/-- Precision requires shared dimension: "clean" can take "pristine"
    precision because they measure the same thing. -/
theorem precision_requires_shared_dimension :
    pristine.dimension = clean.dimension := by simp [pristine, clean]

-- ============================================================================
-- § 9. Fragment Grounding
-- ============================================================================

/-- Fragment entries determine gap/no-gap classification. -/
theorem relative_adjs_contrary :
    large.antonymRelation = some .contrary ∧
    small.antonymRelation = some .contrary ∧
    gigantic.antonymRelation = some .contrary ∧
    tiny.antonymRelation = some .contrary := by
  simp [large, small, gigantic, tiny]

theorem absolute_weak_contradictory :
    clean.antonymRelation = some .contradictory ∧
    dirty.antonymRelation = some .contradictory := by
  simp [clean, dirty]

theorem absolute_strong_contrary :
    pristine.antonymRelation = some .contrary ∧
    filthy.antonymRelation = some .contrary := by
  simp [pristine, filthy]

/-- Gap classification agrees with fragment for ALL study entries. -/
theorem classify_agrees_with_fragment :
    classifyAdj large = true ∧ classifyAdj small = true ∧
    classifyAdj clean = false ∧ classifyAdj dirty = false ∧
    classifyAdj pristine = true ∧ classifyAdj filthy = true := by
  simp [classifyAdj, large, small, clean, dirty, pristine, filthy]

/-- Size quadruple shares a dimension. -/
theorem size_same_dimension :
    large.dimension = small.dimension ∧
    large.dimension = gigantic.dimension ∧
    large.dimension = tiny.dimension := by
  simp [large, small, gigantic, tiny]

/-- Cleanliness quadruple shares a dimension. -/
theorem cleanliness_same_dimension :
    clean.dimension = dirty.dimension ∧
    clean.dimension = pristine.dimension ∧
    clean.dimension = filthy.dimension := by
  simp [clean, dirty, pristine, filthy]

end AlexandropoulouGotzner2024
