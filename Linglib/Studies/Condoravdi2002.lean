import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Modality.TemporalAxes
import Linglib.Fragments.English.Auxiliaries

/-!
# @cite{condoravdi-2002}: Temporal Interpretation of Modals

Condoravdi, C. (2002). Temporal Interpretation of Modals: Modals for the
Present and for the Past. In D. Beaver, S. Kaufmann, B. Clark, & L. Casillas
(Eds.), *The Construction of Meaning*. CSLI Publications.

## Core claims

1. **Uniform modal semantics**: modals for the present and modals for the
   past share a single meaning. No implicit tense under the modal.
2. **Decompositional analysis**: "might have" parses as MAY(PERF(φ)),
   not as a single lexical item MIGHT-HAVE.
3. **Temporal expansion**: modals expand evaluation to a forward interval
   rather than shifting it. Forward orientation follows from this for
   eventive predicates; present-or-future for stative predicates.
4. **Scope–modality correlation**: MODAL > PERF yields the epistemic
   reading; PERF > MODAL yields the counterfactual (metaphysical)
   reading. This follows from the diversity condition: metaphysical
   modal bases require non-settledness, which the past cannot provide.

## Architecture

- The AT relation (`at'`/`atForward`) and its forward-expansion variants
  are defined in the *AT relation* section below; the eventive case reuses
  Klein's perfective viewpoint (`Aspect.PRFV`).
- Branching-time, settledness, and diversity live in
  `Semantics/Modality/HistoricalAlternatives.lean`.
- This file composes them into Condoravdi's specific operators and
  derives the paper's predictions.
- The `mayCore`/`may` split (point-evaluation vs forward-expansion; see
  *Modal cores vs. prospective modals*) is the hook downstream studies
  consume to model modals whose prospectivity is not lexicalized — the
  locus of this account's cross-linguistic contrasts.
-/

namespace Condoravdi2002

open Core.Time
open Features (Dynamicity)
open Semantics.Aspect
open HistoricalAlternatives
open Semantics.Modality (TemporalPerspective TemporalOrientation)

/-! ## The AT relation

@cite{condoravdi-2002}'s temporal-instantiation relation `AT(t, w, P)`,
dispatching on eventuality sort (after @cite{kamp-rohrer-1983},
@cite{partee-1984}): events require temporal inclusion `τ(e) ⊆ t`, states
temporal overlap `τ(e) ∘ t`. The eventive case is definitionally Klein's
perfective viewpoint (`Aspect.PRFV`) and is reused rather than re-stipulated;
the forward-expansion variants are Condoravdi's modal apparatus (evaluation
expanded to the half-open `[t, _)`), consumed by the modal operators below. -/

section AtRelation
variable {W Time : Type*} [LinearOrder Time]

/-- Eventive AT, `AT(t, w, P)` for eventive `P`: an event of `P` whose runtime
    is included in `t`. Definitionally Klein's perfective `Aspect.PRFV`;
    Condoravdi writes the conjuncts predicate-first, `PRFV` relation-first. -/
def atEvent (P : W → Event Time → Prop) : IntervalPred W Time := PRFV P

/-- Stative AT, `AT(t, w, P)` for stative `P`: an event of `P` whose runtime
    merely overlaps `t`. Weaker than `Aspect.IMPF` (proper inclusion), so it
    has no Aspect counterpart and stays a local definition. -/
def atState (P : W → Event Time → Prop) : IntervalPred W Time :=
  fun w t => ∃ e : Event Time, e.τ.overlaps t ∧ P w e

/-- The AT relation, dispatching on eventuality sort. The paper's third case
    (properties of times) is vacuous here: the event predicate is eventuality-valued. -/
def at' (sort : Dynamicity) (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    Prop :=
  match sort with
  | .dynamic => atEvent P w t
  | .stative => atState P w t

/-- Eventive instantiation is stronger than stative: an event included in the
    interval certainly overlaps it. -/
theorem atState_of_atEvent (P : W → Event Time → Prop) (w : W) (t : Interval Time)
    (h : atEvent P w t) : atState P w t :=
  let ⟨e, hSub, hP⟩ := h
  ⟨e, Interval.subinterval_overlaps hSub, hP⟩

/-- `atEvent` is monotone in the reference interval. -/
theorem atEvent_mono {t₁ t₂ : Interval Time} (P : W → Event Time → Prop) (w : W)
    (hSub : t₁.subinterval t₂) (h : atEvent P w t₁) : atEvent P w t₂ :=
  let ⟨e, heSub, hP⟩ := h
  ⟨e, ⟨le_trans hSub.1 heSub.1, le_trans heSub.2 hSub.2⟩, hP⟩

/-- `atState` is monotone in the reference interval: overlap with a subinterval
    entails overlap with the containing interval. -/
theorem atState_mono {t₁ t₂ : Interval Time} (P : W → Event Time → Prop) (w : W)
    (hSub : t₁.subinterval t₂) (h : atState P w t₁) : atState P w t₂ :=
  let ⟨e, hOv, hP⟩ := h
  ⟨e, ⟨le_trans hOv.1 hSub.2, le_trans hSub.1 hOv.2⟩, hP⟩

/-! ### Forward expansion

@cite{condoravdi-2002}: modals expand the evaluation time forward to `[t, _)`
rather than shifting it. Since `Interval` requires finite bounds, the
constraints are expressed directly: for events the runtime starts at or after
`t`; for states it persists at or past `t`. -/

/-- Event instantiated in the future of `t` — `AT([t, _), w, P)` for eventive
    `P`: the event starts at or after `t`. -/
def atEventForward (P : W → Event Time → Prop) (w : W) (t : Time) : Prop :=
  ∃ e : Event Time, t ≤ e.τ.start ∧ P w e

/-- State instantiated through `t` — `AT([t, _), w, P)` for stative `P`: the
    state persists at or past `t`. -/
def atStateForward (P : W → Event Time → Prop) (w : W) (t : Time) : Prop :=
  ∃ e : Event Time, t ≤ e.τ.finish ∧ P w e

/-- Forward AT, dispatching on eventuality sort. -/
def atForward (sort : Dynamicity) (P : W → Event Time → Prop) (w : W) (t : Time) :
    Prop :=
  match sort with
  | .dynamic => atEventForward P w t
  | .stative => atStateForward P w t

/-- Forward stative is weaker than forward eventive: if the event starts at or
    after `t`, its finish is also at or after `t`. -/
theorem atStateForward_of_atEventForward (P : W → Event Time → Prop) (w : W)
    (t : Time) (h : atEventForward P w t) : atStateForward P w t :=
  let ⟨e, hStart, hP⟩ := h
  ⟨e, le_trans hStart e.τ.valid, hP⟩

/-- `atEvent` at a point `[t, t]` implies `atEventForward` at `t`. -/
theorem atEventForward_of_atEvent_point (P : W → Event Time → Prop) (w : W) (t : Time)
    (h : atEvent P w (Interval.point t)) : atEventForward P w t :=
  let ⟨e, hSub, hP⟩ := h
  ⟨e, hSub.1, hP⟩

/-- `atState` at a point `[t, t]` implies `atStateForward` at `t`. -/
theorem atStateForward_of_atState_point (P : W → Event Time → Prop) (w : W) (t : Time)
    (h : atState P w (Interval.point t)) : atStateForward P w t :=
  let ⟨e, hOv, hP⟩ := h
  ⟨e, hOv.2, hP⟩

end AtRelation

/-! ## Operators -/

section Operators
variable {W Time : Type*} [LinearOrder Time]

/-- Present tense: instantiates a property at the utterance time. The
    temporal anchor is a single point. -/
def pres (sort : Dynamicity) (P : W → Event Time → Prop) (t : Time)
    (w : W) : Prop :=
  at' sort P w (Interval.point t)

/-- Perfect: shifts evaluation to a prior time. There is some `t' < t` at
    which the property holds. -/
def perf (sort : Dynamicity) (P : W → Event Time → Prop) (w : W)
    (t : Time) : Prop :=
  ∃ t' : Time, t' < t ∧ at' sort P w (Interval.point t')

/-! ### Modal cores vs. prospective modals

The temporal evaluator is factored out: `mayCore`/`wollCore` quantify
over the modal base and check the prejacent at the perspective point,
while `may`/`woll` apply forward temporal expansion. Condoravdi's
English `might`/`would` use the prospective versions — futurity is
lexicalized in the modal. The point-evaluation cores are the hook for
modals whose futurity is *not* lexicalized but supplied by a separate
prospective operator; `may_of_mayCore_dynamic` relates the two. -/

/-- Modal possibility core: ∃ w' ∈ MB(w,t), the prejacent holds at
    the point `t` in `w'`. No forward expansion. -/
def mayCore (MB : W → Time → Set W) (sort : Dynamicity)
    (P : W → Event Time → Prop) (w : W) (t : Time) : Prop :=
  ∃ w' ∈ MB w t, at' sort P w' (Interval.point t)

/-- MAY/MIGHT: existential quantification over the modal base, with
    forward temporal expansion. The English modal lexicalizes the
    prospective choice (@cite{condoravdi-2002}). -/
def may (MB : W → Time → Set W) (sort : Dynamicity)
    (P : W → Event Time → Prop) (w : W) (t : Time) : Prop :=
  ∃ w' ∈ MB w t, atForward sort P w' t

/-- Modal necessity core: ∀ w' ∈ MB(w,t), the prejacent holds at
    the point `t` in `w'`. No forward expansion. -/
def wollCore (MB : W → Time → Set W) (sort : Dynamicity)
    (P : W → Event Time → Prop) (w : W) (t : Time) : Prop :=
  ∀ w' ∈ MB w t, at' sort P w' (Interval.point t)

/-- WOLL: universal quantification over the modal base, with forward
    temporal expansion. The untensed modal underlying *will* / *would*. -/
def woll (MB : W → Time → Set W) (sort : Dynamicity)
    (P : W → Event Time → Prop) (w : W) (t : Time) : Prop :=
  ∀ w' ∈ MB w t, atForward sort P w' t

/-- For dynamic predicates, `mayCore` implies `may`: forward expansion
    is a weakening when the prejacent is checked at a point. The
    pointwise instantiation gives an event whose start lies at or
    after `t`, which is exactly what `atEventForward` requires. -/
theorem may_of_mayCore_dynamic (MB : W → Time → Set W)
    (P : W → Event Time → Prop) (w : W) (t : Time)
    (h : mayCore MB .dynamic P w t) : may MB .dynamic P w t := by
  obtain ⟨w', hMem, hAt⟩ := h
  refine ⟨w', hMem, ?_⟩
  exact atEventForward_of_atEvent_point P w' t hAt

/-- For stative predicates, `mayCore` implies `may`: pointwise state
    overlap entails forward state persistence at the point. -/
theorem may_of_mayCore_stative (MB : W → Time → Set W)
    (P : W → Event Time → Prop) (w : W) (t : Time)
    (h : mayCore MB .stative P w t) : may MB .stative P w t := by
  obtain ⟨w', hMem, hAt⟩ := h
  refine ⟨w', hMem, ?_⟩
  exact atStateForward_of_atState_point P w' t hAt

/-! ## Composed scope readings

The two scope orderings of MAY and PERF that derive epistemic vs.
counterfactual modality. The trivial single-operator examples
("He might run", "He might be here") are inlined as docstrings on
`may` rather than given separate names. -/

/-- "He may have won" — *epistemic* reading. The modal scopes over the
    perfect (PRES > MAY > PERF). Modal base evaluated at `t`; the
    perfect back-shifts inside the modal's scope. -/
def mayEpistemic (MB : W → Time → Set W) (P : W → Event Time → Prop)
    (t : Time) (w : W) : Prop :=
  ∃ w' ∈ MB w t, perf .dynamic P w' t

/-- "He might have won" — *counterfactual* reading. The perfect scopes
    over the modal (PRES > PERF > MAY). The perfect shifts the modal
    base's evaluation point to a past `t'`; the modal then quantifies
    over worlds compatible with the past, with the property in
    `[t', _)`. -/
def mightCounterfactual (MB : W → Time → Set W) (P : W → Event Time → Prop)
    (t : Time) (w : W) : Prop :=
  ∃ t' : Time, t' < t ∧ may MB .dynamic P w t'

end Operators

/-! ## Reading classification

Readings are classified along the canonical modal-temporal axes
(`Semantics/Modality/TemporalAxes.lean`): `TemporalPerspective`
(present/past evaluation of the modal base) and `TemporalOrientation`
(direction from the perspective to the prejacent). Condoravdi's typology
uses only the `future` and `past` orientations; the `present`-orientation
cell of `TemporalOrientation` goes unused. -/

/-- The three attested readings of an English modal-perfect string. The
    fourth combination (past perspective + past orientation) is
    unattested and excluded by construction. -/
inductive ModalReading where
  /-- "He might win." Future-oriented from a present perspective. -/
  | present
  /-- "He may have already won." Past-oriented from a present
      perspective (PRES > MAY > PERF). -/
  | epistemic
  /-- "He might still have won." Future-oriented from a past
      perspective (PRES > PERF > MAY). -/
  | counterfactual
  deriving DecidableEq, Repr

/-- Modal-base evaluation time of a reading. -/
def ModalReading.perspective : ModalReading → TemporalPerspective
  | .present | .epistemic => .present
  | .counterfactual       => .past

/-- Direction of temporal reference of a reading. -/
def ModalReading.orientation : ModalReading → TemporalOrientation
  | .present | .counterfactual => .future
  | .epistemic                 => .past

/-! ## Bridge to Klein's viewpoint operators -/

section KleinBridge
variable {W Time : Type*} [LinearOrder Time]

/-- Condoravdi's eventive `perf` entails Klein's `perfSimple`: a prior
    point of instantiation gives a degenerate PTS `[t', t']`
    right-bounded at `t`. -/
theorem perf_eventive_implies_perfSimple
    (P : W → Event Time → Prop) (w : W) (t : Time)
    (h : perf .dynamic P w t) : perfSimple P ⟨w, t⟩ := by
  obtain ⟨t', hlt, e, hSub, hP⟩ := h
  exact ⟨⟨t', t, le_of_lt hlt⟩, rfl, e,
    ⟨hSub.1, le_trans hSub.2 (le_of_lt hlt)⟩, hP⟩

/-- @cite{klein-1994}'s imperfective entails Condoravdi's stative AT: proper
    inclusion of the reference interval in the event runtime implies overlap. -/
theorem atState_of_impf (P : W → Event Time → Prop) (w : W) (t : Interval Time)
    (h : IMPF P w t) : atState P w t :=
  let ⟨e, hPSub, hP⟩ := h
  have hOv : e.τ.overlaps t :=
    Interval.overlaps_symm (Interval.subinterval_overlaps
      (Interval.properSubinterval_implies_subinterval _ _ hPSub))
  ⟨e, hOv, hP⟩

end KleinBridge

/-! ## Scope–modality correlation

The relative scope of MODAL and PERF correlates with the kind of
modality expressed:

- **MODAL > PERF (epistemic)**: the modal's perspective is present; the
  property under it is back-shifted past. Past properties are settled,
  so the diversity condition blocks a metaphysical base — only
  epistemic modality remains available.
- **PERF > MODAL (counterfactual)**: the modal's perspective is a past
  time; the property is in that past's future. Future properties are
  not settled, so a metaphysical base is available. -/

section ScopeCorrelation
variable {W Time : Type*} [LinearOrder Time]

/-- When MAY scopes over PERF, the property under the modal is *back-
    shifted past*. If this property is settled in the common ground (as
    past properties are), then a metaphysical modal base cannot satisfy
    diversity — restricting MODAL > PERF to epistemic modality. -/
theorem modal_over_perf_blocks_metaphysical
    (history : HistoricalAlternatives W Time)
    (MB : W → Time → Set W)
    (cg : Set W) (now : Time)
    (P : W → Event Time → Prop)
    (hMB : ∀ w ∈ cg, ∀ w' ∈ MB w now, histEquiv history now w w')
    (hSettled : settled history cg now (λ w => perf .dynamic P w now)) :
    ¬ diverse MB cg now (λ w => perf .dynamic P w now) :=
  settled_not_diverse history MB cg now _ hMB hSettled

/-- When PERF scopes over MAY (counterfactual reading), the metaphysical
    base at the past perspective `t' ≤ now` is a superset of the one at
    `now`: backwards-closure of historical equivalence makes the past
    base wider. This is the structural source of the counterfactual
    reading's "could have been otherwise" force. -/
theorem counterfactual_widens_domain
    (history : HistoricalAlternatives W Time)
    (hBC : history.backwardsClosed) (w : W)
    {t' now : Time} (hle : t' ≤ now) :
    metaphysicalBase history w now ⊆ metaphysicalBase history w t' :=
  metaphysicalBase_antitone hBC w hle

end ScopeCorrelation

/-! ## Adverb compatibility

Frame adverbials are intersective predicate modifiers: they restrict
temporal reference to a period relative to the reference time. A frame
adverb is *compatible* with a modal reading exactly when its selected
period intersects the temporal region the modal projects. The eight
(in)compat theorems below follow from `lt_irrefl`/`lt_of_lt_of_le`/
`le_refl` rather than a lookup table. -/

section Adverbs
variable {Time : Type*} [LinearOrder Time]

/-- "Yesterday": strictly before the reference time. -/
def yesterday (now : Time) : Set Time := {t | t < now}

/-- "Now": the reference time itself. -/
def nowAdv (now : Time) : Set Time := {now}

/-- "Tomorrow": strictly after the reference time. -/
def tomorrow (now : Time) : Set Time := {t | now < t}

/-- The temporal region in which a modal evaluates its scope, read off
    the AT relation:

    - **Future orientation**: `atForward` requires the property's
      temporal anchor to lie at or after the reference time. Projected
      region: `[now, ∞)`.
    - **Present orientation**: coincident with the reference time
      (unused by Condoravdi's typology). Region: `{now}`.
    - **Past orientation**: `perf` requires a strictly earlier
      instantiation time. Projected region: `(-∞, now)`.

    Note: the eventive/stative distinction is *not* recorded here. The
    AT relation permits `now = e.start` for `atEventForward`, so the
    table-style "now is incompatible with eventive future" prediction
    of the original paper is a pragmatic event-duration fact that
    `compatible` does not formally exclude. -/
def projectedRegion (orient : TemporalOrientation) (now : Time) : Set Time :=
  match orient with
  | .future  => {t | now ≤ t}
  | .present => {now}
  | .past    => {t | t < now}

/-- Compatibility: the adverb's selected period overlaps the modal's
    projected region. -/
def compatible (period : Time → Set Time) (reading : ModalReading)
    (now : Time) : Prop :=
  ∃ t, t ∈ period now ∧ t ∈ projectedRegion reading.orientation now

-- ── Modals for the present (future orientation) ──

/-- "He may get sick tomorrow." Future-oriented modal accepts a future
    adverb (witnessed via `NoMaxOrder`). -/
theorem tomorrow_present_compat [NoMaxOrder Time] (now : Time) :
    compatible (tomorrow (Time := Time)) .present now := by
  obtain ⟨t, ht⟩ := exists_gt now
  exact ⟨t, ht, le_of_lt ht⟩

/-- "*He may get sick yesterday." Future-oriented modal rejects a past
    adverb: any witness would satisfy `t < now ∧ now ≤ t`,
    contradicting `lt_irrefl`. -/
theorem yesterday_present_incompat (now : Time) :
    ¬ compatible (yesterday (Time := Time)) .present now := by
  rintro ⟨t, ht1, ht2⟩
  exact absurd (lt_of_lt_of_le ht1 ht2) (lt_irrefl _)

/-- "He may be sick now." The reference time witnesses overlap of `{now}`
    with `[now, ∞)` via `le_refl`. The eventive variant ("??He may get
    sick now") is marginal in the paper for pragmatic event-duration
    reasons; see the `projectedRegion` docstring. -/
theorem now_present_compat (now : Time) :
    compatible (nowAdv (Time := Time)) .present now :=
  ⟨now, rfl, le_refl now⟩

-- ── Modals for the past (past orientation, epistemic reading) ──

/-- "He may have gotten sick yesterday." Past-oriented modal accepts a
    past adverb (witnessed via `NoMinOrder`). -/
theorem yesterday_epistemic_compat [NoMinOrder Time] (now : Time) :
    compatible (yesterday (Time := Time)) .epistemic now := by
  obtain ⟨t, ht⟩ := exists_lt now
  exact ⟨t, ht, ht⟩

/-- "*He may have gotten sick tomorrow." Past-oriented modal rejects a
    future adverb: `now < t ∧ t < now` contradicts `lt_irrefl` via
    `lt_trans`. -/
theorem tomorrow_epistemic_incompat (now : Time) :
    ¬ compatible (tomorrow (Time := Time)) .epistemic now := by
  rintro ⟨t, ht1, ht2⟩
  exact absurd (lt_trans ht2 ht1) (lt_irrefl _)

end Adverbs

/-! ## Fragment binding -/

/-- *Might* and perfect *have* are distinct aux heads in the English
    Fragment. The decomposition "might have" = MAY(PERF(...)) and the
    scope permutation deriving the epistemic vs counterfactual reading
    both require the Fragment to classify them under different
    `auxType`s — if they ever fused (e.g., a single `might-have` modal
    entry), the analysis would not apply at the surface-form level.

    Other studies binding these Fragment entries are discoverable by
    greping `Fragments.English.Auxiliaries.<entry>` across `Studies/`. -/
theorem might_have_distinct_aux_types :
    Fragments.English.Auxiliaries.might.auxType ≠
      Fragments.English.Auxiliaries.have_.auxType := by decide

end Condoravdi2002
