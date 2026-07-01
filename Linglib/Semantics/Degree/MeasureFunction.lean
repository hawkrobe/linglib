import Linglib.Semantics.ArgumentStructure.Affectedness.Defs
import Linglib.Semantics.Events.Basic
import Mathlib.Order.Defs.LinearOrder

/-!
# Measure Functions, Difference Functions, and Measure of Change
[kennedy-levin-2008] [hay-kennedy-levin-1999] [kennedy-mcnally-2005]
[bartsch-vennemann-1972] [kennedy-1999]

The substrate for [kennedy-levin-2008]'s "Measure of Change"
analysis of degree achievements (DAs) — the time-indexed measure
functions that gradable adjectives lexicalise (introduced in
[hay-kennedy-levin-1999] eq. 11; restated in K&L 2008 §7.3.1
main text on p. 167), the difference functions derived from them
(K&L eq. 23), and the measure-of-change function `m_Δ` that powers
the DA semantics (K&L eq. 25).

## K&L 2008 §7.3 in Lean

| K&L primitive                                | This file                       |
|----------------------------------------------|---------------------------------|
| Measure function `m : e × t → d` (HKL eq. 11; K&L p. 167) | `MeasureFunction α δ Time` |
| Scale `⟨S, R, δ⟩` (K&L fn 8)                 | `[LinearOrder δ]`               |
| Difference function `m_d^↑` (K&L eq. 23)     | `differenceFunction`            |
| Measure of change `m_Δ` (K&L eq. 25)         | `measureOfChange`               |
| `init(e)` / `fin(e)` time projection         | event runtime start/finish      |

K&L 2008 fn 9 is about the *alternative* ⟨d,⟨e,t⟩⟩ analysis (Cresswell,
von Stechow, Heim, Klein), NOT the time-indexed measure function. The
time-indexing originates with [hay-kennedy-levin-1999] eq. 11.

## Bridge to Beavers' affectedness hierarchy

K&L (§7.3.3) derive variable telicity from scale structure: closed-scale
DAs (*straighten, darken, fill, empty*) are default telic (their `m_Δ`
inherits a maximum from the base adjective's scale, licensing the
maximum-standard interpretation by Interpretive Economy); open-scale
DAs (*widen, deepen*) are obligatorily atelic (no maximum, only
minimum-standard "comparative" reading available).

This maps directly onto Beavers eq. (60):
- closed-scale DA → `IsQuantizedAffected θ` with `g_φ = scale max`
- open-scale DA → `IsNonQuantizedAffected θ` (some final degree, no
  specific commitment)

The bridge is `MeasureFunction.toHasScalarResult` below: any
time-indexed measure function induces a `HasScalarResult` instance
where `resultAt x g e := m x e.runtime.snd = g`. Verb-specific
`IsQuantizedAffected` / `IsNonQuantizedAffected` instances then
quantify over the scale's maximum (or its absence).

## Sections

1. `MeasureFunction` — time-indexed measure (K&L footnote 9)
2. `differenceFunction` — m clamped at d as new minimum (K&L eq. 23)
3. `measureOfChange` — `m_Δ(x)(e)` (K&L eq. 25)
4. `MeasureFunction.toHasScalarResult` — bridge to Beavers substrate
5. Identity / monotonicity theorems

-/

namespace Degree.MeasureFunction

open Semantics.ArgumentStructure.Affectedness

-- ════════════════════════════════════════════════════
-- § 1. MeasureFunction (K&L 2008 footnote 9)
-- ════════════════════════════════════════════════════

set_option linter.dupNamespace false in
/-- A **time-indexed measure function** `m : α → Time → δ`
    ([hay-kennedy-levin-1999] eq. 11; restated in
    [kennedy-levin-2008] §7.3.1 main text p. 167): a function
    from objects and times to degrees on a scale.

    "An object can have different degrees of height, weight, temperature,
    etc. at different times" — so the K&L analysis relativises the
    measure to time. The adjective `cool` denotes a function `cool`
    from objects `x` and times `t` returning the temperature of `x`
    at `t`.

    Lean encoding: a plain function abbreviation. The K&L analysis only
    needs the function; structural bundling (lexical form, scale
    boundedness tag, etc.) lives in consumer-side
    `Verb/DegreeAchievement.lean`.

    For typeclass-resolution participation (so `HasScalarResult` and
    `HasLatentScale` instances synthesise automatically), use the
    `HasMeasureFunction α δ Time` typeclass below — the mathlib pattern
    of pairing a function abbrev with a typeclass wrapper, analogous to
    `Set α := α → Prop` (abbrev) plus the various `[Membership]` /
    `[SetLike]` (typeclass) interfaces.

    The duplicated `MeasureFunction` namespace (file-level
    `Degree.MeasureFunction` + the type itself) is harmless
    here — same pattern as mathlib's `Function` files. The `set_option
    linter.dupNamespace false in` immediately above silences the
    namespace-duplication warning for this single declaration. -/
abbrev MeasureFunction (α : Type*) (δ : Type*) (Time : Type*) :=
  α → Time → δ

/-- The typeclass form of `MeasureFunction`: a verb commits to a
    canonical time-indexed measure on dimension `δ`. Per-verb instance
    (one per (α, δ, Time) triple a verb's lexical content addresses).

    Mathlib pattern: cf. `MetricSpace α` (typeclass providing `dist`),
    `MeasurableSpace α` (typeclass providing `MeasurableSet`). The
    typeclass enables instance synthesis — any verb declaring a
    `[HasMeasureFunction α δ Time]` instance automatically gets
    `[HasScalarResult α δ (Event Time)]` and `[HasLatentScale α (Event Time)]`
    via the auto-synthesis instances in §5 below, opening Beavers'
    affectedness typeclass chain to the verb without explicit smart
    constructor calls.

    The auto-synthesis is what makes the K&L → Beavers bridge
    "structural" rather than "smart-constructor": consumers who
    declare HasMeasureFunction get Beavers' typeclasses for free. -/
class HasMeasureFunction (α : Type*) (δ : Type*) (Time : Type*) where
  /-- The verb's canonical time-indexed measure function. -/
  measure : α → Time → δ

-- ════════════════════════════════════════════════════
-- § 2. Difference Function (K&L 2008 eq. 23)
-- ════════════════════════════════════════════════════

/-- [kennedy-levin-2008] eq. (23) **Difference function** `m_d^↑`:
    just like measure function `m` except clamped at `d` as the new
    minimum — its range is `{d' ∈ S | d ≤ d'}`, and for any x, t in
    the domain of `m`, if `m(x)(t) ≤ d` then `m_d^↑(x)(t) = d`.

    Implements K&L's (23.i)+(23.ii) as a single `max` operation:
    `m_d^↑ x t = max d (m x t)`. The result is always `≥ d`, and equals
    `m x t` when `m x t > d`, equals `d` otherwise.

    Used in the comparative semantics of `wider than the carpet`
    (K&L eq. 24): `wide_{wide(c)}^↑(x)(t) ≥ stnd(wide_{wide(c)}^↑)`. -/
def differenceFunction {α δ Time : Type*} [LinearOrder δ]
    (m : MeasureFunction α δ Time) (d : δ) :
    MeasureFunction α δ Time :=
  fun x t => max d (m x t)

/-- The difference function's value is always at least the clamping
    minimum. Direct from `le_max_left`. -/
theorem differenceFunction_ge_clamp {α δ Time : Type*} [LinearOrder δ]
    (m : MeasureFunction α δ Time) (d : δ) (x : α) (t : Time) :
    d ≤ differenceFunction m d x t :=
  le_max_left d (m x t)

/-- When the underlying measure already exceeds the clamp, the
    difference function returns the underlying measure unchanged. -/
theorem differenceFunction_eq_measure {α δ Time : Type*} [LinearOrder δ]
    (m : MeasureFunction α δ Time) (d : δ) (x : α) (t : Time)
    (h : d ≤ m x t) :
    differenceFunction m d x t = m x t := by
  simp [differenceFunction, max_eq_right h]

-- ════════════════════════════════════════════════════
-- § 3. Measure of Change (K&L 2008 eq. 25)
-- ════════════════════════════════════════════════════

/-- [kennedy-levin-2008] eq. (25) **Measure of change**
    `m_Δ(x)(e) = m_{m(x)(init(e))}^↑(x)(fin(e))`.

    The measure of change function takes an object `x` and an event
    `e`, returns the degree representing the amount `x` changes in
    the property measured by `m` as a result of participating in `e`.

    Concretely: clamp `m` at `m(x)(init(e))` (the initial degree),
    evaluate at `fin(e)` (the final time). When `m(x)(fin(e)) ≥
    m(x)(init(e))` (monotone increase), the result is `m(x)(fin(e))`
    (final degree). When `m(x)(fin(e)) < m(x)(init(e))` (no positive
    change), the result is `m(x)(init(e))` (initial degree, the
    "zero" of the derived scale).

    The Lean signature takes the initial and final times explicitly
    rather than an event, keeping the substrate event-type-agnostic.
    The convenience overload `measureOfChangeOnEvent` specialises to
    `Event Time` events with the runtime-interval projections. -/
def measureOfChange {α δ Time : Type*} [LinearOrder δ]
    (m : MeasureFunction α δ Time) (x : α) (initT finT : Time) : δ :=
  differenceFunction m (m x initT) x finT

/-- Identity theorem: when initial and final times coincide, the
    measure of change is the initial degree (no change). -/
theorem measureOfChange_self {α δ Time : Type*} [LinearOrder δ]
    (m : MeasureFunction α δ Time) (x : α) (t : Time) :
    measureOfChange m x t t = m x t := by
  simp [measureOfChange, differenceFunction]

/-- The measure of change is always at least the initial degree
    (clamped from below). Direct from `differenceFunction_ge_clamp`. -/
theorem measureOfChange_ge_init {α δ Time : Type*} [LinearOrder δ]
    (m : MeasureFunction α δ Time) (x : α) (initT finT : Time) :
    m x initT ≤ measureOfChange m x initT finT :=
  differenceFunction_ge_clamp m (m x initT) x finT

/-- When the patient's degree increases over the event, the measure
    of change equals the final degree. -/
theorem measureOfChange_eq_final {α δ Time : Type*} [LinearOrder δ]
    (m : MeasureFunction α δ Time) (x : α) (initT finT : Time)
    (h : m x initT ≤ m x finT) :
    measureOfChange m x initT finT = m x finT :=
  differenceFunction_eq_measure m (m x initT) x finT h

-- ════════════════════════════════════════════════════
-- § 4. Event-specialised Measure of Change
-- ════════════════════════════════════════════════════

/-- Specialisation of `measureOfChange` to `Event Time` events: extract
    init/fin times from the event's runtime interval. -/
def measureOfChangeOnEvent {α δ Time : Type*} [LinearOrder δ] [LinearOrder Time]
    (m : MeasureFunction α δ Time) (x : α) (e : Event Time) : δ :=
  measureOfChange m x e.runtime.fst e.runtime.snd

-- ════════════════════════════════════════════════════
-- § 5. Auto-synthesis bridges to Beavers' substrate
-- ════════════════════════════════════════════════════

/-- **Auto-synthesis instance**: a verb with a canonical measure
    function (`[HasMeasureFunction α δ Time]`) automatically has a
    Beavers `HasScalarResult` instance.

    `HasScalarResult.resultAt x g e := measure x e.runtime.snd = g`
    — patient `x` ends event `e` holding degree `g` of the property
    measured by the verb's measure function.

    This is the load-bearing structural bridge from K&L 2008's
    measure-function framework to Beavers' affectedness substrate.
    Once a verb declares `[HasMeasureFunction]`, downstream
    `IsNonQuantizedAffected.mk'` and `IsQuantizedAffected.mk'`
    constructors find the `HasScalarResult` instance by typeclass
    synthesis — no explicit constructor invocation needed.

    Mathlib pattern: cf. `[MetricSpace α] : TopologicalSpace α`
    (instance synthesising the general framework's typeclass from
    a specific framework's typeclass). -/
instance HasScalarResult.ofHasMeasureFunction
    {α δ Time : Type*} [LinearOrder Time] [HasMeasureFunction α δ Time] :
    HasScalarResult α δ (Event Time) where
  resultAt x g e := HasMeasureFunction.measure x e.runtime.snd = g

/-- Companion smart constructor: `HasMeasureFunction`-backed verbs
    can also be given a Beavers `HasLatentScale` instance via this
    function. NOT an `instance` because `δ` doesn't appear in the
    `HasLatentScale α (Event Time)` conclusion — Lean's typeclass
    synthesiser cannot infer which dimension's measure function to
    use, so the instance arrow can't fire automatically.

    Consumers using `HasMeasureFunction` should manually call
    `HasLatentScale.ofHasMeasureFunction` (passing δ explicitly via
    `(δ := someDim)`) when they need the Potential affectedness level.
    For verbs already declaring `HasScalarResult` via the auto-instance
    above, this is the parallel constructor.

    The body `latentScale _ _ := True` is correct content (not a
    placeholder): a verb with a measure function definitionally puts
    its patient on a scale, so the latent-scale relation holds for
    every patient/event pair. The Potential affectedness level
    (`∀x∀e[θ(x,e) → latentScale x e]`) reduces to `θ`-membership
    when `latentScale` is `True`, which matches Beavers' (60d)
    semantics for verbs whose patients are scale-typed by lexical
    commitment. For pure force-recipient verbs (no result state,
    e.g., *push, scrub*), users provide their own `HasLatentScale`
    instance with the nontrivial force-applied relation directly.

    `@[reducible]` is required by Lean for class-type `def`s (without
    it Lean warns that typeclass resolution will not see through the
    definition). This is unrelated to the body's content; it's purely
    a typeclass-elaboration hygiene marker. -/
@[reducible]
def HasLatentScale.ofHasMeasureFunction
    {α δ Time : Type*} [LinearOrder Time] [HasMeasureFunction α δ Time] :
    HasLatentScale α (Event Time) where
  latentScale _ _ := True

end Degree.MeasureFunction
