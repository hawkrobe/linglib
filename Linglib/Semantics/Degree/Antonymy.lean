import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Degree.Adjective
import Linglib.Core.Logic.Aristotelian.Basic
import Linglib.Semantics.Degree.Discrete

/-!
# Antonymy: Contradictory vs. Contrary Negation
[krifka-2007b] [cruse-1986] [horn-1989]

Two models of gradable adjective antonymy and their formal properties.

**Contradictory model** (single threshold θ): happy and unhappy partition the
scale. `contradictoryNeg d θ = !positiveMeaning d θ` — double negation
eliminates and "not unhappy" = "happy".

**Contrary model** (two thresholds θ_neg < θ_pos): happy and unhappy leave a
gap. `notContraryNegMeaning d tp ≠ positiveMeaning' d tp` in the gap region.
Double negation does NOT eliminate.

[krifka-2007b] argues that antonyms are *literally* contradictory (single
θ) and the gap emerges through pragmatic strengthening (M-principle). The
contrary model captures the *effective* semantics after strengthening. Both
models are formalized here; the pragmatic derivation connecting them is in
`Studies/Krifka2007.lean`.

The core operations (`contradictoryNeg`, `contraryNeg`, `inGapRegion`,
`ThresholdPair`, `positiveMeaning'`, `contraryNegMeaning`, `notContraryNegMeaning`)
are defined in `Gradability/Adjective.lean`.
-/

set_option autoImplicit false

namespace Degree.Antonymy


/-! ### Contradictory Negation: Involutory (DNE holds) -/

/-- Contradictory negation is the propositional complement of positive meaning.
    Both compute threshold comparisons: `d ≤ ↑θ` vs `↑θ < d`. -/
@[simp] theorem contradictory_is_complement {max : Nat}
    (d : Bounded max) (θ : Threshold max) :
    contradictoryNeg d θ ↔ ¬ positiveMeaning d θ := by
  simp only [contradictoryNeg, notPositiveMeaning, positiveMeaning,
    Core.Order.Comparison.mem_over, Core.Order.Comparison.rel, id_eq, not_lt]

/-- Double contradictory negation eliminates: "not [not happy]" = "happy".

    [krifka-2007b]: this is the LITERAL semantics. If antonyms are
    contradictory, then "not unhappy" and "happy" are synonymous —
    the puzzle that motivates pragmatic strengthening. -/
theorem contradictory_dne {max : Nat}
    (d : Bounded max) (θ : Threshold max) :
    ¬ contradictoryNeg d θ ↔ positiveMeaning d θ := by
  rw [contradictory_is_complement, not_not]

/-- Under contradictory semantics, the scale is exhaustively partitioned:
    every degree is either positive or in the antonym region, with no gap. -/
theorem contradictory_exhaustive {max : Nat}
    (d : Bounded max) (θ : Threshold max) :
    positiveMeaning d θ ∨ contradictoryNeg d θ := by
  by_cases h : positiveMeaning d θ
  · exact Or.inl h
  · exact Or.inr ((contradictory_is_complement d θ).mpr h)

/-! ### Contrary Negation: Gap (DNE fails) -/

/-- The gap region is exactly "not unhappy" ∧ "not happy": degrees that escape
    the contrary negative without reaching the positive threshold. -/
@[simp] theorem gap_iff_not_neg_and_not_pos {max : Nat}
    (d : Bounded max) (tp : ThresholdPair max) :
    inGapRegion d tp ↔ notContraryNegMeaning d tp ∧ ¬ positiveMeaning' d tp := by
  simp only [inGapRegion, notContraryNegMeaning, positiveMeaning',
             Degree.positiveMeaning, Core.Order.Comparison.mem_over,
             Core.Order.Comparison.rel, id_eq, not_lt]

/-- When the gap is strict (θ_neg < θ_pos), there exists a degree that is
    "not unhappy" but NOT "happy" — double negation through contrary fails.
    Witness: the negative threshold itself (as a degree). -/
theorem contrary_gap_exists {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    ∃ d : Bounded max, notContraryNegMeaning d tp ∧ ¬ positiveMeaning' d tp := by
  refine ⟨↑tp.neg, le_refl _, ?_⟩
  simp only [positiveMeaning', Degree.positiveMeaning,
    Core.Order.Comparison.mem_over, Core.Order.Comparison.rel, id_eq, not_lt]
  exact le_of_lt h

/-- The gap region is nonempty when θ_neg < θ_pos. -/
theorem gap_nonempty {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    ∃ d : Bounded max, inGapRegion d tp := by
  obtain ⟨d, h1, h2⟩ := contrary_gap_exists tp h
  exact ⟨d, (gap_iff_not_neg_and_not_pos d tp).mpr ⟨h1, h2⟩⟩

end Degree.Antonymy

/-! ### The surface quadruplet and prediction skeleton
[cruse-1986] [horn-1989] [krifka-2007b] [tessler-franke-2019]

Absorbed from the retired `AntonymPrediction.lean`: `AntonymForm`
(happy / not happy / unhappy / not unhappy), its two contested
denotations, and the complexity/prediction skeleton.
-/

namespace Degree

open Features (NegationType Asymmetry)

-- ============================================================================
-- § 1. The Four Surface Forms
-- ============================================================================

/-- The four surface forms generated from an antonymic adjective pair
    `(positive, negative)` by sentential negation. Four-cell substrate;
    no semantic commitment — a paper claiming all four forms collapse to
    two (contradictory analysis) and a paper claiming a four-way gap
    (contrary analysis) both consume this enum and provide their own
    denotations. -/
inductive AntonymForm where
  | positive       -- "happy"
  | notPositive    -- "not happy"
  | negative       -- "unhappy"
  | notNegative    -- "not unhappy"
  deriving Repr, DecidableEq, Fintype

/-- Default morphological-syntactic complexity of each form: count of
    negation operators (morphological *un-* + syntactic *not*), scaled to
    [krifka-2007b]'s integer ordering 0 < 2 < 3 < 5. Matches
    [tessler-franke-2019]'s `utteranceCost` exactly.

    Per-paper analyses may override the cost (TF2020 uses a `ℚ`-valued
    coercion of this; Krifka's Economy constraint reads it directly). -/
def AntonymForm.complexity : AntonymForm → Nat
  | .positive    => 0   -- monomorphemic
  | .negative    => 2   -- un- prefix (morphologically complex)
  | .notPositive => 3   -- syntactic not (syntactically complex)
  | .notNegative => 5   -- not + un- (both)

/-- The complexity ordering is strictly monotone across the quadruplet in
    the canonical order positive < negative < notPositive < notNegative. -/
theorem AntonymForm.complexity_strictMono :
    complexity .positive < complexity .negative ∧
    complexity .negative < complexity .notPositive ∧
    complexity .notPositive < complexity .notNegative := by
  decide

-- ============================================================================
-- § 2. Two Extensional Denotations
-- ============================================================================

/-- **Contradictory denotation** of an antonym form on a single threshold `θ`.
    Both poles share `θ`; the four forms collapse to two distinct truth
    values (positive/notNegative ≡ `d > θ`; notPositive/negative ≡ `d ≤ θ`).
    This is the literal-semantic position [krifka-2007b] attributes to
    antonyms before pragmatic strengthening. -/
abbrev AntonymForm.contradictoryDenot {max : Nat} (θ : Threshold max)
    (q : AntonymForm) (d : Bounded max) : Prop :=
  match q with
  | .positive    => positiveMeaning d θ      -- d > θ
  | .notPositive => ¬ positiveMeaning d θ    -- d ≤ θ
  | .negative    => ¬ positiveMeaning d θ    -- d ≤ θ (same! contradictory antonym)
  | .notNegative => positiveMeaning d θ      -- d > θ (DNE restores positive)

/-- **Strengthened denotation** of an antonym form on a `ThresholdPair`. Two
    thresholds `tp.neg ≤ tp.pos`; the borderline region `[tp.neg, tp.pos]`
    lifts notNegative ("not unhappy") away from positive ("happy") and
    notPositive ("not happy") away from negative ("unhappy"). This is the
    effective-semantic position post-pragmatic-strengthening (Krifka 2007 §4)
    or the lexically-encoded position (Alexandropoulou-Gotzner 2024). -/
abbrev AntonymForm.strengthenedDenot {max : Nat} (tp : ThresholdPair max)
    (q : AntonymForm) (d : Bounded max) : Prop :=
  match q with
  | .positive    => positiveMeaning' d tp        -- d > tp.pos
  | .notPositive => contradictoryNeg d tp.pos    -- d ≤ tp.pos
  | .negative    => contraryNegMeaning d tp      -- d < tp.neg
  | .notNegative => notContraryNegMeaning d tp   -- d ≥ tp.neg

-- ============================================================================
-- § 3. Anchor Theorems
-- ============================================================================

/-- Under the contradictory denotation, the `negative`-`notPositive` and
    `notNegative`-`positive` form pairs are extensionally identical. This is
    the formal puzzle [krifka-2007b] solves pragmatically: literal
    contradictory semantics predicts *not unhappy* ≡ *happy*. -/
theorem contradictoryDenot_synonymy {max : Nat}
    (θ : Threshold max) (d : Bounded max) :
    (AntonymForm.contradictoryDenot θ .negative d ↔
     AntonymForm.contradictoryDenot θ .notPositive d) ∧
    (AntonymForm.contradictoryDenot θ .notNegative d ↔
     AntonymForm.contradictoryDenot θ .positive d) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Under the strengthened denotation with strict gap (`tp.neg < tp.pos`),
    the `notNegative` and `positive` extensions come apart: there exists a
    degree (the negative threshold itself) where *not unhappy* holds but
    *happy* does not. This is the witness for the polarity asymmetry. -/
theorem strengthenedDenot_breaks_synonymy {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    ∃ d : Bounded max,
      AntonymForm.strengthenedDenot tp .notNegative d ∧
      ¬ AntonymForm.strengthenedDenot tp .positive d :=
  Antonymy.contrary_gap_exists tp h

/-! ### Grounding in the Aristotelian opposition relation

The antonym classification is not a stipulated tag: the two form denotations
genuinely stand in the substrate's `Aristotelian.IsContradictory` / `IsContrary`
([deklerck-demey-2025]), so `predictionForAntonymy` rides on a real opposition. -/

open Aristotelian in
/-- **Contradictory denotation ⇒ `IsContradictory`.** With a single threshold the
negative form is the literal complement of the positive form, so the two are
complementary in the Boolean algebra `Degree → Prop` — forced (it is `IsCompl`).
`contradictoryDenot_synonymy` (DNE collapse) is a corollary. -/
theorem isContradictory_contradictoryDenot {max : Nat} (θ : Threshold max) :
    IsContradictory
      (fun d : Bounded max => AntonymForm.contradictoryDenot θ .positive d)
      (fun d => AntonymForm.contradictoryDenot θ .negative d) :=
  isCompl_compl

open Aristotelian in
/-- **Strengthened denotation with a strict gap ⇒ `IsContrary`.** Positive
(`d > tp.pos`) and contrary-negative (`d < tp.neg`) are jointly impossible
(`Disjoint`) but, by the gap `[tp.neg, tp.pos]`, not jointly exhaustive
(`¬ Codisjoint` — `contrary_gap_exists` is the witness). -/
theorem isContrary_strengthenedDenot {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Bounded max) < (tp.pos : Bounded max)) :
    IsContrary
      (fun d : Bounded max => AntonymForm.strengthenedDenot tp .positive d)
      (fun d => AntonymForm.strengthenedDenot tp .negative d) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    funext d
    simp only [AntonymForm.strengthenedDenot, positiveMeaning', contraryNegMeaning,
      Degree.positiveMeaning, Degree.negativeMeaning,
      Pi.inf_apply, Pi.bot_apply, inf_Prop_eq]
    exact eq_false (fun ⟨h1, h2⟩ => absurd (h1.trans h2) (lt_asymm h))
  · rw [codisjoint_iff]
    obtain ⟨d, hd1, hd2⟩ := Antonymy.contrary_gap_exists tp h
    intro hco
    have hd := congrFun hco d
    simp only [AntonymForm.strengthenedDenot, positiveMeaning', contraryNegMeaning,
      notContraryNegMeaning, Degree.positiveMeaning, Degree.negativeMeaning,
      Pi.sup_apply, Pi.top_apply, sup_Prop_eq] at hd hd1 hd2
    rcases of_eq_true hd with hp | hn
    · exact hd2 hp
    · exact absurd hn (not_lt.mpr hd1)

-- ============================================================================
-- § 4. Prediction Skeleton
-- ============================================================================

/-- **Anchored prediction skeleton.** Map an antonymy type to predicted
    polarity-asymmetry direction:

    - `.contradictory ↦ .symmetric` — anchored by `isContradictory_contradictoryDenot`
      (the forms are genuinely complementary, so the contradictory base collapses
      notPositive and negative; no asymmetry to derive).
    - `.contrary ↦ .asymmetric` — anchored by `isContrary_strengthenedDenot`
      (the forms are genuinely contrary, so the gap admits a witness where
      notNegative holds but positive does not).

    The map thus rides on the substrate's `IsContradictory`/`IsContrary` between the
    two form denotations — the antonym tag is the real opposition, not a stipulation.

    Consumed by per-paper prediction signatures (Horn 1989, Krifka 2007,
    Alexandropoulou-Gotzner 2024 JoS) which read this map via
    `predictionForEntry` against a Fragment lexical entry's
    `antonymRelation` field. -/
def predictionForAntonymy : NegationType → Asymmetry
  | .contradictory => .symmetric
  | .contrary      => .asymmetric

/-- Read prediction off a Fragment lexical entry's `antonymRelation`. Defaults
    to `.symmetric` for entries without an explicit antonymy classification. -/
def predictionForEntry (e : GradableAdjective) : Asymmetry :=
  e.antonymRelation.elim .symmetric predictionForAntonymy

end Degree
