import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.Incrementality
import Linglib.Theories.Semantics.Events.CumulativityPropagation
import Linglib.Theories.Semantics.Events.StratifiedReference
import Linglib.Theories.Semantics.Measurement.Basic

/-!
# Measure Phrases and Quantizing Modification (QMOD)
@cite{krifka-1989} @cite{champollion-2017} @cite{scontras-2014}

Quantizing modification (QMOD): a measure phrase like *three kilos*
combines with a CUM mass noun like *rice* to produce a QUA measure
phrase like *three kilos of rice*. The mechanism is: QMOD restricts a
CUM predicate by an extensive measure, and the extensivity guarantees
that no proper part of an n-measure entity also has measure n.

Plus: temporal adverbials (*for an hour*) as QMOD on duration via the
runtime trace τ; the full measure-phrase-yields-telic-VP chain
(`measure_phrase_makes_qua`); and the bridge to @cite{scontras-2014}'s
`MeasureFn` framework via the `MeasureFn.IsExtensive` predicate.

Topic-named (not paper-named): defines the deep substrate that
@cite{krifka-1989} §3 develops, that @cite{champollion-2017}'s
*for*-adverbial analysis depends on, and that @cite{scontras-2014}'s
measurement framework connects to.

## Sections

1. QMOD theorems (qmod_qua, qmod_of_cum_is_qua) — K89 §2 / T6
2. Temporal adverbials via QMOD (durationMeasure, forAdverbial_subsumes_qmod) — K89 §3
3. measure_phrase_makes_qua — K89 §4 unified telicity transfer
4. Scontras MeasureFn bridge — K89 §5

-/

namespace Semantics.Events.MeasurePhrases

open Mereology
open Semantics.Events.Mereology
open Semantics.Events.ThematicRoleProperties
open Semantics.Events.Incrementality
open Semantics.Events.CumulativityPropagation (VP qua_propagation)
open Semantics.Events.StratifiedReference
open Core.Time

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

-- ════════════════════════════════════════════════════
-- § 1. QMOD Bridge Theorems (K89 §2)
-- ════════════════════════════════════════════════════

/-- QMOD produces QUA predicates when μ is extensive and n > 0.
    @cite{krifka-1989} §2: "three kilos of rice" is QUA because no proper
    part of a 3kg entity also weighs 3kg (extensivity of weight).
    Chains to `extMeasure_qua` from `Core/Mereology.lean`. -/
theorem qmod_qua
    {R : α → Prop} {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n) :
    QUA (QMOD R μ n) := by
  intro x y ⟨_, hx_eq⟩ hlt ⟨_, hy_eq⟩
  have hμ_qua := extMeasure_qua (μ := μ) n hn
  exact hμ_qua x y hx_eq hlt hy_eq

/-- The full @cite{krifka-1989} quantizing story: a CUM mass noun
    combined with QMOD (via an extensive measure) yields a QUA measure
    phrase. "rice" is CUM → "three kilos of rice" = QMOD(rice, μ_kg, 3)
    is QUA. -/
theorem qmod_of_cum_is_qua
    {R : α → Prop} (_hCum : CUM R)
    {μ : α → ℚ} [ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n) :
    QUA (QMOD R μ n) :=
  qmod_qua hn

-- ════════════════════════════════════════════════════
-- § 2. Temporal Adverbials via QMOD (K89 §3)
-- ════════════════════════════════════════════════════

/-- Duration measure: maps events to the length of their runtime.
    Wrapper around τ (runtime extraction) composed with an
    interval-length function.
    @cite{krifka-1989}: temporal adverbials modify via QMOD on
    duration. -/
def durationMeasure {Time : Type*} [LinearOrder Time]
    (len : Interval Time → ℚ) : Event Time → ℚ :=
  λ e => len e.runtime

/-- "V for δ" as QMOD: the for-adverbial restricts VP events to those
    whose duration equals δ. This connects @cite{krifka-1989}'s QMOD
    analysis to @cite{champollion-2017}'s `forAdverbialMeaning`.

    Krifka: "run for an hour" = QMOD(run, duration, 1hr)
    Champollion: "run for δ" = λe. run(e) ∧ τ(e) = δ ∧ SSR(run)(e)

    The QMOD analysis captures the duration constraint; Champollion
    adds the SSR requirement for felicity. The two are complementary:
    QMOD explains why the resulting VP is QUA (telic-like bounded),
    while SSR explains why the base predicate must be atelic. -/
theorem forAdverbial_subsumes_qmod
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    {V : Event Time → Prop} {len : Interval Time → ℚ}
    {dur : Interval Time} {e : Event Time}
    (h : forAdverbialMeaning V dur e) :
    QMOD V (durationMeasure len) (len dur) e :=
  ⟨h.1, by simp [durationMeasure, h.2.1]⟩

-- ════════════════════════════════════════════════════
-- § 3. The full @cite{krifka-1989} measure phrase story
-- ════════════════════════════════════════════════════

/-- **The full @cite{krifka-1989} measure phrase story**
    (canonical typeclass form): QMOD(mass_noun, extensive_μ, n) +
    `[IsSincVerb θ]` → QUA VP (telic).

    "eat three kilos of rice" yields a QUA VP because:
    1. RICE is CUM (mass noun)
    2. "three kilos of rice" = QMOD(rice, μ_kg, 3) is QUA (`qmod_of_cum_is_qua`)
    3. EAT has `[IsSincVerb eat.theme]` (bundling SINC + UP + CumTheta)
    4. QUA propagates through `qua_propagation` to the VP

    This is the central result of @cite{krifka-1989}: measure phrases
    turn mass nouns into quantized predicates, and quantization
    propagates through strictly incremental verbs to yield telic (QUA)
    VPs. -/
theorem measure_phrase_makes_qua
    {R : α → Prop} (hCum : CUM R)
    {μ : α → ℚ} [ExtMeasure α μ]
    {n : ℚ} (hn : 0 < n)
    {θ : α → β → Prop} [IsSincVerb θ] :
    QUA (VP θ (QMOD R μ n)) :=
  qua_propagation (qmod_of_cum_is_qua hCum hn)

/-! ### Scontras vs. Krifka

The substrate-level bridges between @cite{scontras-2014}'s `MeasureFn` and
@cite{krifka-1989}'s `Mereology.ExtMeasure` / `QMOD` / `QUA` machinery —
`MeasureFn.IsExtensive`, `extensive_measureFn_qmod_qua`,
`MeasureFn.applyNumeral_iff_qmod` — live in
`Theories/Semantics/Measurement/Basic.lean` (see § 8 there). They were
previously sited here, but they're properties of `MeasureFn` rather than
of event-side QMOD machinery, so they belong with the canonical
`MeasureFn` definition. -/

end Semantics.Events.MeasurePhrases
