import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Theories.Semantics.Events.StratifiedReference
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic

/-!
# Krifka (1989) "Nominal Reference, Temporal Constitution and Quantification"

The foundational paper connecting nominal reference properties (mass/count/plural)
to aspectual properties (telic/atelic) via thematic role homomorphisms. This module
builds on the polymorphic mereological infrastructure in `Mereology.lean` and the
thematic role properties in `Krifka1998.lean` to provide:

1. **Nominal reference instantiation**: mass nouns = CUM, count nouns = QUA,
   bare plurals = AlgClosure (§1)
2. **QMOD bridge theorems**: QMOD + extensive measure → QUA (§2)
3. **Temporal adverbials via QMOD**: "V for δ" as a QMOD instance (§3)
4. **Unified telicity transfer chain**: the full Krifka 1989 story connecting
   nominal reference → VP aspect (§4)
5. **Bridge to Scontras's measurement framework** (§5)

## References

- Krifka, M. (1989). Nominal reference, temporal constitution and quantification
  in event semantics. In R. Bartsch et al. (eds.), *Semantics and Contextual
  Expression*, 75–115. Foris.
- Krifka, M. (1998). The origins of telicity.
- Champollion, L. (2017). *Parts of a Whole*. OUP.
- Scontras, G. (2014). *The Semantics of Measurement*. Harvard dissertation.
-/

namespace EventSemantics.Krifka1989

open EventSemantics
open EventSemantics.Mereology
open EventSemantics.Krifka1998
open EventSemantics.StratifiedReference
open Core.Time
open TruthConditional.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Nominal Reference Properties
-- ════════════════════════════════════════════════════

/-- Mass nouns have cumulative reference: water ⊕ water = water.
    Krifka (1989) §2: mass nouns denote predicates satisfying CUM. -/
abbrev MassNoun {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop := CUM P

/-- Count nouns have quantized reference: no proper part of a cat is a cat.
    Krifka (1989) §2: count nouns denote predicates satisfying QUA. -/
abbrev CountNoun {α : Type*} [PartialOrder α] (P : α → Prop) : Prop := QUA P

/-- Bare plurals are algebraic closures: *CAT = the closure of CAT under ⊕.
    Krifka (1989) §2: bare plurals denote *P, the smallest superset of P
    closed under sum formation. -/
abbrev BarePlural {α : Type*} [SemilatticeSup α] (P : α → Prop) : α → Prop :=
  AlgClosure P

/-- Bare plurals are cumulative (reuses `algClosure_cum` from Mereology). -/
theorem barePlural_cum {α : Type*} [SemilatticeSup α] {P : α → Prop} :
    CUM (BarePlural P) :=
  algClosure_cum

-- ════════════════════════════════════════════════════
-- § 2. QMOD Bridge Theorems
-- ════════════════════════════════════════════════════

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- QMOD produces QUA predicates when μ is extensive and n > 0.
    Krifka (1989) §2: "three kilos of rice" is QUA because no proper
    part of a 3kg entity also weighs 3kg (extensivity of weight).
    Chains to `extMeasure_qua` from Krifka1998. -/
theorem qmod_qua
    {R : α → Prop} {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n) :
    QUA (QMOD R μ n) := by
  intro x y ⟨_, hx_eq⟩ hlt ⟨_, hy_eq⟩
  have hμ_qua := extMeasure_qua (μ := μ) n hn
  exact hμ_qua x y hx_eq hlt hy_eq

/-- The full Krifka 1989 quantizing story: a CUM mass noun combined with
    QMOD (via an extensive measure) yields a QUA measure phrase.
    "rice" is CUM → "three kilos of rice" = QMOD(rice, μ_kg, 3) is QUA. -/
theorem qmod_of_cum_is_qua
    {R : α → Prop} (_hCum : CUM R)
    {μ : α → ℚ} [ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n) :
    QUA (QMOD R μ n) :=
  qmod_qua hn

-- ════════════════════════════════════════════════════
-- § 3. Temporal Adverbials via QMOD
-- ════════════════════════════════════════════════════

/-- Duration measure: maps events to the length of their runtime.
    This is a wrapper around τ (runtime extraction) composed with
    an interval-length function.
    Krifka (1989): temporal adverbials modify via QMOD on duration. -/
def durationMeasure {Time : Type*} [LinearOrder Time]
    (len : Interval Time → ℚ) : Ev Time → ℚ :=
  λ e => len e.runtime

/-- "V for δ" as QMOD: the for-adverbial restricts VP events to those
    whose duration equals δ. This connects Krifka's (1989) QMOD analysis
    to Champollion's (2017) `forAdverbialMeaning`.

    Krifka: "run for an hour" = QMOD(run, duration, 1hr)
    Champollion: "run for δ" = λe. run(e) ∧ τ(e) = δ ∧ SSR(run)(e)

    The QMOD analysis captures the duration constraint; Champollion adds
    the SSR requirement for felicity. The two are complementary:
    QMOD explains why the resulting VP is QUA (telic-like bounded),
    while SSR explains why the base predicate must be atelic. -/
theorem forAdverbial_subsumes_qmod
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {V : Ev Time → Prop} {len : Interval Time → ℚ}
    {dur : Interval Time} {e : Ev Time}
    (h : forAdverbialMeaning V dur e) :
    QMOD V (durationMeasure len) (len dur) e :=
  ⟨h.1, by simp [durationMeasure, h.2.1]⟩

-- ════════════════════════════════════════════════════
-- § 4. Unified Telicity Transfer Chain — THE PAYOFF
-- ════════════════════════════════════════════════════

/-- **CUM transfer (atelic)**: CumTheta + CUM noun → CUM VP.
    "eat apples" yields a CUM (atelic) VP because:
    1. APPLES (bare plural) is CUM (`barePlural_cum`)
    2. EAT has a CumTheta incremental theme (follows from SINC in CEM)
    3. CumTheta + CUM(OBJ) → CUM(VP) (`sinc_cum_propagation`)

    CUM is Krifka's mereological characterization of atelicity: the VP
    has cumulative reference, so no natural endpoint. The connection to
    VendlerClass goes via `vendlerClass_atelic_implies_cum_intent` in
    Mereology.lean: atelic classes (states, activities) have CUM. -/
theorem cum_transfer {θ : α → β → Prop} {OBJ : α → Prop}
    (hCumTheta : CumTheta θ) (hObj : CUM OBJ) :
    CUM (VP θ OBJ) :=
  sinc_cum_propagation hCumTheta hObj

/-- **QUA transfer (telic)**: QUA noun + SINC + UP verb → QUA VP.
    "eat two apples" yields a QUA (telic) VP because:
    1. TWO-APPLES is QUA (count noun + numeral → quantized)
    2. EAT has a SINC incremental theme with UP
    3. SINC + UP + QUA(OBJ) → QUA(VP) (`qua_propagation_sinc`)

    QUA is Krifka's mereological characterization of telicity: the VP has
    quantized reference, so it has a natural endpoint. The connection to
    VendlerClass goes via `vendlerClass_telic_implies_qua_intent` in
    Mereology.lean: telic classes (achievements, accomplishments) have QUA. -/
theorem qua_transfer {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hSinc : SINC θ) (hQua : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_propagation_sinc hUP hSinc hQua

/-- **The full Krifka 1989 measure phrase story**: QMOD(mass_noun, extensive_μ, n)
    + SINC verb → QUA VP (telic).

    "eat three kilos of rice" yields a QUA VP because:
    1. RICE is CUM (mass noun)
    2. "three kilos of rice" = QMOD(rice, μ_kg, 3) is QUA (`qmod_of_cum_is_qua`)
    3. EAT has a SINC incremental theme with UP
    4. SINC + UP + QUA(QMOD) → QUA(VP) (`qua_propagation_sinc`)

    This is the central result of Krifka 1989: measure phrases turn mass
    nouns into quantized predicates, and quantization propagates through
    strictly incremental verbs to yield telic (QUA) VPs. -/
theorem measure_phrase_makes_qua
    {R : α → Prop} (_hCum : CUM R)
    {μ : α → ℚ} [ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n)
    {θ : α → β → Prop} (hUP : UP θ) (hSinc : SINC θ) :
    QUA (VP θ (QMOD R μ n)) :=
  qua_propagation_sinc hUP hSinc (qmod_of_cum_is_qua _hCum hn)

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Scontras's Measurement Framework
-- ════════════════════════════════════════════════════

/-! ### Scontras vs. Krifka: different properties, different predicates

Scontras's (2014) QU (quantity-uniform) applies to the **base predicate**:
QU_μ(rice) says that rice-quantities of the same μ-measure can be summed.

Krifka's (1989) QUA applies to the **modified predicate**: QUA("three kilos
of rice") says no proper part of a 3kg-of-rice entity is also 3kg-of-rice.

These are complementary: QU is a precondition on the base noun for measure
modification to be felicitous, while QUA is a *consequence* of the
modification that drives telicity transfer. The bridge between them:
when MeasureFn is extensive, QMOD produces QUA predicates, which is exactly
the quantizing effect that Krifka's telicity transfer chain requires. -/

/-- A `MeasureFn` is extensive (in Krifka's sense) when its underlying
    function satisfies `ExtMeasure`: additivity over non-overlapping entities
    and positivity. This bridges Scontras's measurement framework to
    Krifka's mereological telicity machinery. -/
def MeasureFn.IsExtensive {E : Type*} [SemilatticeSup E]
    (μ : TruthConditional.Measurement.MeasureFn E) : Prop :=
  ExtMeasure E μ.apply

/-- When a measure term uses the default exact relation (= n), `applyNumeral n`
    checks μ(x) == n. This is the Boolean analog of Krifka's QMOD.
    Stated for the default-rel constructor to ensure definitional equality. -/
theorem measureTerm_default_applyNumeral_eq
    {E : Type*} (μ : TruthConditional.Measurement.MeasureFn E)
    (n : ℚ) (x : E) :
    ({ measureFn := μ } : TruthConditional.Measurement.MeasureTermSem E).applyNumeral n x
      = (μ.apply x == n) := rfl

/-- When a `MeasureFn` is extensive (in Krifka's sense), QMOD with that
    measure function at any positive value produces a QUA predicate.
    This bridges Scontras's `MeasureFn` to Krifka's telicity machinery. -/
theorem extensive_measureFn_qmod_qua
    {E : Type*} [inst : SemilatticeSup E]
    {μ : TruthConditional.Measurement.MeasureFn E}
    (hExt : MeasureFn.IsExtensive μ)
    {R : E → Prop} {n : ℚ} (hn : 0 < n) :
    QUA (QMOD R μ.apply n) := by
  have : @ExtMeasure E inst μ.apply := hExt
  exact @qmod_qua E inst _ _ this n hn

end EventSemantics.Krifka1989
