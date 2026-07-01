import Linglib.Semantics.Gradability.Basic
import Linglib.Semantics.Gradability.Antonymy
import Linglib.Fragments.English.Predicates.Adjectival
/-!
# [alexandropoulou-gotzner-2024] — Gradable Adjective Interpretation Under Negation: The Role of Competition
[alexandropoulou-gotzner-2024]

In: *Glossa: a journal of general linguistics* 9(1), pp. 1–33.

## Thesis

[alexandropoulou-gotzner-2024] (Glossa) tests whether the asymmetric vs.
symmetric interpretation patterns of negated relative vs. absolute gradable
adjectives — established in their [alexandropoulou-gotzner-2024-jos]
companion paper — depend on overt *contextual competition* between alternative
expressions. The Glossa paper finds that contextual competition is necessary
to surface the polarity asymmetry of relative adjectives but does not
discriminate the symmetric interpretation patterns of weak absolute adjectives.

The structural precondition for the asymmetry remains the **extension gap**
between contrary antonyms (two thresholds, with a borderline region) versus
the absence of a gap for contradictory antonyms (single threshold, complementary
partition). The competition mechanism the Glossa paper isolates operates on
top of this structural distinction.

The paper situates its findings in the [horn-1989] vs. [krifka-2007b]
controversy over the source of negative strengthening; that controversy is
the central topic of the companion JoS paper, formalised in
`AlexandropoulouGotzner2024JoS.lean`. The Krifka-2007 hidden-agreement bridge
theorem (lexical commitment ↔ output of pragmatic strengthening) lives there.

## Substrate consumed

- `Semantics/Degree/Basic.lean` — `positiveMeaning`, `antonymMeaning`,
  `positiveMeaning_monotone` (all `Prop`-valued, decidable).
- `Semantics/Gradability/Theory.lean` — `ThresholdPair`,
  `positiveMeaning'`, `contraryNegMeaning`, `notContraryNegMeaning`,
  `inGapRegion` (all `abbrev`s over the Core primitives).
- `Semantics/Gradability/Antonymy.lean` — `contradictory_exhaustive`,
  `contradictory_is_complement` (used in §4).
- `Fragments/English/Predicates/Adjectival.lean` — `large/small/gigantic/tiny`
  and `clean/dirty/pristine/filthy` lexical entries.

## Verified citations

PDF audit of `glossa-9919-alexandropoulou.pdf` confirms: the precision-shift
mechanism (§7 here) is Glossa §4.2; equations (6a-b) are the contrary
non-entailments. The paper has five sections (ending at §5 Conclusion) — no
§6/§7/§9 paper-section refs exist; any internal "§N" labels in this file
refer to the Lean file's own structure, not to the paper.

## Out of scope (deferred to JoS file)

The three-case typology (weak relative / weak absolute / strong gradable),
the [horn-1989] vs. [krifka-2007b] prediction signatures, the
strong-adjective challenge to Horn, and the Krifka 2007 hidden-agreement
bridge theorem all live in `AlexandropoulouGotzner2024JoS.lean`.
-/

namespace AlexandropoulouGotzner2024

open Core.Order (Boundedness)
open Semantics.Degree (Degree Threshold deg thr)
open Semantics.Gradability (GradableAdjective ThresholdPair inGapRegion
  positiveMeaning' contraryNegMeaning notContraryNegMeaning)
open Semantics.Degree (positiveMeaning antonymMeaning positiveMeaning_monotone)
open English.Predicates.Adjectival
  (large small gigantic tiny clean dirty pristine filthy)

-- ============================================================================
-- § 1. Experimental Stimuli
-- ============================================================================

/-- A four-cell stimulus design: two pairs of antonymic adjectives at the
    weak/strong informational levels for a single dimension. The Glossa paper
    uses size (large/small/gigantic/tiny) as the relative case and cleanliness
    (clean/dirty/pristine/filthy) as the absolute case. -/
structure AdjQuadruple where
  weakPos    : GradableAdjective
  weakNeg    : GradableAdjective
  strongPos  : GradableAdjective
  strongNeg  : GradableAdjective
  deriving Repr

def sizeQuad : AdjQuadruple where
  weakPos := large; weakNeg := small; strongPos := gigantic; strongNeg := tiny

def cleanlinessQuad : AdjQuadruple where
  weakPos := clean; weakNeg := dirty; strongPos := pristine; strongNeg := filthy

/-- A quadruple's relative-vs-absolute classification is *derived* from the
    Fragment's `scaleType`: open scales (no inherent bounds) are relative;
    bounded scales (lower/upper/closed) are absolute. The Fragment is the
    single source of truth — this avoids the duplicate-stipulation pattern
    the cross-framework reconciler flagged in the original audit. -/
def AdjQuadruple.isRelative (q : AdjQuadruple) : Bool :=
  q.weakPos.scaleType == .open_

-- ============================================================================
-- § 2. Scale Model
-- ============================================================================

/-- 5-degree scale (matching the 1–5 Likert response scales used in the
    Glossa experiments). -/
abbrev Deg5 := Degree 4

abbrev Thr5 := Threshold 4

/-- Reference threshold pair: substrate-imposed θ_pos = 2, θ_neg = 1, giving
    a one-degree gap at deg 2. The Glossa paper does not commit to specific
    threshold values; this choice is a substrate convenience for stating
    Lean-checkable predictions. -/
def defaultTP : ThresholdPair 4 where
  pos := thr 2
  neg := thr 1

-- ============================================================================
-- § 3. Three-Region Partition
-- ============================================================================

/-! For contrary antonyms (`ThresholdPair`), the scale partitions into three
    regions: positive, gap, negative. The gap is **where** "not positive"
    diverges from "negative" — the structural basis for polarity asymmetry. -/

/-- Every degree falls in at least one of {positive, gap, negative}. -/
theorem three_region_exhaustive {max : Nat}
    (tp : ThresholdPair max) (d : Degree max) :
    positiveMeaning' d tp ∨ inGapRegion d tp ∨ contraryNegMeaning d tp := by
  by_cases h1 : (tp.pos : Degree max) < d
  · exact Or.inl h1
  · by_cases h2 : d < (tp.neg : Degree max)
    · exact Or.inr (Or.inr h2)
    · push_neg at h1 h2
      exact Or.inr (Or.inl ⟨h2, h1⟩)

/-- Gap region excludes the positive region. -/
theorem gap_not_positive {max : Nat}
    (tp : ThresholdPair max) (d : Degree max)
    (h : inGapRegion d tp) : ¬ positiveMeaning' d tp :=
  not_lt.mpr h.2

/-- Gap region excludes the contrary-negative region. -/
theorem gap_not_negative {max : Nat}
    (tp : ThresholdPair max) (d : Degree max)
    (h : inGapRegion d tp) : ¬ contraryNegMeaning d tp :=
  not_lt.mpr h.1

/-- Gap holds iff the degree is neither positive nor contrary-negative. -/
theorem gap_iff_neither {max : Nat}
    (tp : ThresholdPair max) (d : Degree max) :
    inGapRegion d tp ↔ ¬ positiveMeaning' d tp ∧ ¬ contraryNegMeaning d tp := by
  constructor
  · intro h; exact ⟨gap_not_positive tp d h, gap_not_negative tp d h⟩
  · intro ⟨hp, hn⟩
    exact ⟨not_lt.mp hn, not_lt.mp hp⟩

-- ============================================================================
-- § 4. Contradictory Complement: Why Absolutes Are Symmetric
-- ============================================================================

/-! For contradictory antonyms (single θ), positive and antonym partition the
    scale with no gap: every degree satisfies exactly one. This is **why**
    absolute adjectives like *clean*/*dirty* show symmetric negation patterns
    in the Glossa experiments. -/

/-- Contradictory antonyms exhaust the scale. Delegates to the substrate
    lemma in `Antonymy.lean`. -/
theorem contradictory_complement {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    positiveMeaning d θ ∨ antonymMeaning d θ :=
  Semantics.Gradability.Antonymy.contradictory_exhaustive d θ

/-- `antonymMeaning` is the propositional complement of `positiveMeaning`.
    Delegates to the substrate lemma in `Antonymy.lean`. -/
theorem contradictory_is_complement {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    antonymMeaning d θ ↔ ¬ positiveMeaning d θ :=
  Semantics.Gradability.Antonymy.contradictory_is_complement d θ

-- ============================================================================
-- § 5. Monotonicity → Strength & Precision
-- ============================================================================

/-! `positiveMeaning_monotone` (Core): higher threshold ⇒ informationally
    stronger. This single substrate theorem grounds both:
    1. Strong adjectives entail weak (gigantic ⇒ large).
    2. Precision upshift entails standard (pristine-precision ⇒ standard
       precision; cf. Glossa §4.2 precision-shift mechanism in §7 below). -/

/-- Strong adjectives entail weak. -/
theorem strong_entails_weak (θ_weak θ_strong : Thr5)
    (h_ord : θ_weak ≤ θ_strong) (d : Deg5)
    (h_strong : positiveMeaning d θ_strong) :
    positiveMeaning d θ_weak :=
  positiveMeaning_monotone d θ_weak θ_strong h_ord h_strong

/-- Concrete witness: degree 4 is positive at the weak threshold (thr 2)
    BECAUSE it is positive at the strong threshold (thr 3) and monotonicity
    propagates. -/
theorem gigantic_entails_large :
    positiveMeaning (deg 4 : Deg5) (thr 2 : Thr5) :=
  positiveMeaning_monotone (deg 4) (thr 2 : Thr5) (thr 3 : Thr5)
    (by decide) (by decide)

/-- Precision upshift entails the standard reading: a degree satisfying
    "clean" at pristine precision (θ = 3) satisfies "clean" at standard
    precision (θ = 1). Same monotonicity theorem, different reading. -/
theorem precision_entails_standard (d : Deg5)
    (h : positiveMeaning d (thr 3 : Thr5)) :
    positiveMeaning d (thr 1 : Thr5) :=
  positiveMeaning_monotone d (thr 1 : Thr5) (thr 3 : Thr5) (by decide) h

-- ============================================================================
-- § 6. Predictions for Contrary Antonyms
-- ============================================================================

/-! Lean-checkable witnesses for the structural predictions the Glossa paper
    makes about negated contrary antonyms. Theorem names describe what the
    proofs actually establish, not the pragmatic phenomena the names might
    suggest in informal exposition (negative strengthening, middling readings)
    — those are pragmatic *inferences* from the structural facts witnessed
    here, not the structural facts themselves. -/

/-- At `defaultTP`, the bottom of the scale satisfies both "not positive" (the
    antonym predicate) and the contrary-negative predicate. This overlap is a
    *necessary* condition for negative strengthening (Glossa §1, Horn 1989)
    but does not derive the pragmatic inference. -/
theorem defaultTP_witnesses_overlap_at_zero :
    antonymMeaning (deg 0 : Deg5) defaultTP.pos ∧
    contraryNegMeaning (deg 0 : Deg5) defaultTP :=
  ⟨by decide, by decide⟩

/-- At `defaultTP`, degree 2 is in the gap: neither positive nor
    contrary-negative. This is the structural basis for the "middling"
    reading of *not small* discussed in the Glossa paper. -/
theorem defaultTP_gap_at_two :
    notContraryNegMeaning (deg 2 : Deg5) defaultTP ∧
    ¬ positiveMeaning' (deg 2 : Deg5) defaultTP ∧
    ¬ contraryNegMeaning (deg 2 : Deg5) defaultTP :=
  ⟨by decide, by decide, by decide⟩

/-- Polarity asymmetry: there exist witnesses for both
    (i) "not positive ⇒ negative" overlap (deg 0) and
    (ii) "not negative ⇏ positive" gap (deg 2). -/
theorem polarity_asymmetry_witnesses :
    (∃ d : Deg5, antonymMeaning d defaultTP.pos ∧ contraryNegMeaning d defaultTP) ∧
    (∃ d : Deg5, notContraryNegMeaning d defaultTP ∧
                 ¬ positiveMeaning' d defaultTP ∧
                 ¬ contraryNegMeaning d defaultTP) :=
  ⟨⟨deg 0, by decide, by decide⟩,
   ⟨deg 2, by decide, by decide, by decide⟩⟩

/-- Contrary non-entailment witnesses (Glossa eqs. 6a–b):
    (i) "not positive" does not entail "contrary negative" (deg 2 is a
        counterexample to *not large* ⇒ *small*).
    (ii) "not negative" does not entail "positive" (deg 2 is a
         counterexample to *not small* ⇒ *large*). -/
theorem contrary_nonentailment_witnesses :
    (∃ d : Deg5, antonymMeaning d defaultTP.pos ∧ ¬ contraryNegMeaning d defaultTP) ∧
    (∃ d : Deg5, notContraryNegMeaning d defaultTP ∧ ¬ positiveMeaning' d defaultTP) :=
  ⟨⟨deg 2, by decide, by decide⟩,
   ⟨deg 2, by decide, by decide⟩⟩

/-- The contrary/contradictory split depends on antonym type, not on
    informational strength: weak (large/small) and strong (gigantic/tiny)
    relative adjectives both have contrary antonyms. -/
theorem strength_invariance :
    large.antonymRelation = some .contrary ∧
    gigantic.antonymRelation = some .contrary ∧
    small.antonymRelation = some .contrary ∧
    tiny.antonymRelation = some .contrary :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- For contradictory antonyms, every degree is positive or in the antonym
    region — no gap. Hence symmetric negation. Demonstrated at θ = thr 2
    on `Deg5` via `contradictory_complement`. -/
theorem absolute_symmetric (d : Deg5) :
    positiveMeaning d (thr 2 : Thr5) ∨ antonymMeaning d (thr 2 : Thr5) :=
  contradictory_complement d (thr 2)

-- ============================================================================
-- § 7. Precision-Level Mechanism (Glossa §4.2)
-- ============================================================================

/-! The Glossa paper's §4.2 proposes that absolute adjectives behaving
    relative-like under negation results from a precision-level shift driven
    by the availability of more-precise alternatives: *clean* in competition
    with a more demanding alternative reading (≈ *pristine*) takes the
    high-precision threshold, creating a structural gap.

    The precision-shifted scale is encoded as a `ThresholdPair` with the
    positive threshold raised. Note: the Glossa paper does not give an
    operational specification for *which* precision parameter applies in
    *which* discourse context; the mechanism is sketched, not formalised.

    [haslinger-2025]'s *potential p-equivalence* substrate addresses
    related precision-shift phenomena via a different competition formalism;
    bridging the two accounts is out of scope here. -/

/-- ThresholdPair for the precision-upshifted "clean" scale: θ_pos = 3
    (pristine precision), θ_neg = 1 (filthy threshold) — `defaultTP` with the
    positive threshold raised one notch. -/
def precisionTP : ThresholdPair 4 where
  pos := thr 3
  neg := thr 1

/-- Precision upshift creates a gap at degree 2. -/
theorem precision_gap : inGapRegion (deg 2 : Deg5) precisionTP :=
  ⟨by decide, by decide⟩

/-- The precision gap is genuine: degree 2 satisfies neither positive (at
    pristine precision) nor contrary-negative. Reuses §3's `gap_iff_neither`
    and the `precision_gap` witness. -/
theorem precision_gap_is_neither :
    ¬ positiveMeaning' (deg 2 : Deg5) precisionTP ∧
    ¬ contraryNegMeaning (deg 2 : Deg5) precisionTP :=
  (gap_iff_neither _ _).mp precision_gap

/-- Precision shift requires a shared dimension: *clean* can take *pristine*
    precision because the two adjectives measure the same dimension. -/
theorem precision_requires_shared_dimension :
    pristine.dimension = clean.dimension := rfl

-- ============================================================================
-- § 8. Fragment Grounding
-- ============================================================================

/-- Relative-adjective Fragment entries are classified as contrary. -/
theorem relative_adjs_contrary :
    large.antonymRelation = some .contrary ∧
    small.antonymRelation = some .contrary ∧
    gigantic.antonymRelation = some .contrary ∧
    tiny.antonymRelation = some .contrary :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Weak absolute Fragment entries are classified as contradictory. -/
theorem absolute_weak_contradictory :
    clean.antonymRelation = some .contradictory ∧
    dirty.antonymRelation = some .contradictory :=
  ⟨rfl, rfl⟩

/-- Strong absolute Fragment entries are classified as contrary
    (extreme absolutes have a gap, per Glossa §3 / Kennedy & McNally 2005). -/
theorem absolute_strong_contrary :
    pristine.antonymRelation = some .contrary ∧
    filthy.antonymRelation = some .contrary :=
  ⟨rfl, rfl⟩

/-- `AdjQuadruple.isRelative` agrees with the experimental design: size is
    relative (open scale), cleanliness is absolute (closed scale). The
    classification is structural — it reads off the Fragment's `scaleType`. -/
theorem isRelative_classification :
    sizeQuad.isRelative = true ∧ cleanlinessQuad.isRelative = false := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- Size quadruple shares a dimension. -/
theorem size_same_dimension :
    large.dimension = small.dimension ∧
    large.dimension = gigantic.dimension ∧
    large.dimension = tiny.dimension :=
  ⟨rfl, rfl, rfl⟩

/-- Cleanliness quadruple shares a dimension. -/
theorem cleanliness_same_dimension :
    clean.dimension = dirty.dimension ∧
    clean.dimension = pristine.dimension ∧
    clean.dimension = filthy.dimension :=
  ⟨rfl, rfl, rfl⟩

end AlexandropoulouGotzner2024
