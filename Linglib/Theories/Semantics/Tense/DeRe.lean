import Linglib.Core.Context.Basic
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Theories.Semantics.Reference.Acquaintance
import Linglib.Theories.Semantics.Tense.Basic

/-!
# Centered-World Temporal De Re
@cite{lewis-1979-attitudes} (centered-worlds + de se reduction);
@cite{cresswell-vonstechow-1982} (de re belief generalized);
@cite{abusch-1997} (the temporal application).

Abusch 1997's temporal de re analysis: a tense morpheme can take wide
scope over an attitude operator by occupying the *res* position. The res
contributes a **time-concept** (`Intension (KContext) T` — Abusch's
`R₁ : eeiwt` of def. 13) plus a **base-world condition** (in `w₀`, the
actual time-denotation is picked out by the concept relative to the
holder's centered context — Abusch §3, p. 9).

This file is anchored on the centered-world de re framework, not on
Abusch 1997 alone — Lewis 1979 + Cresswell & von Stechow 1982 are the
foundational layer Abusch builds on. Paper-anchored derivation theorems
live in `Phenomena/TenseAspect/Studies/Abusch1997.lean`.

## Reuse

- `Core.Intension W τ` (`Core/IntensionalLogic/Rigidity.lean`) — substrate
  for time-concepts. `IsRigid` captures the "same time across alternatives"
  property that distinguishes de re from de dicto temporal anaphora.
  `IsRigidOn` (set-relativized) is the workhorse for modal-alternative
  rigidity.
- `Core.Context.KContext W E P T` (`Core/Context/Basic.lean`) — the
  centered Kaplanian context `⟨agent, addressee, world, time, position⟩`.
  Abusch's `⟨x_self, t_now, w⟩` is a 3-field projection; `KContext` is
  the richer object the rest of linglib already commits to.
  `KContext.shiftWorldTime` provides the alternative-shift operation.
- `Semantics.Reference.Acquaintance` — polymorphic `Cover`, `nameCover`,
  `isAcquaintedWith`. The temporal-de-re reading is the
  `Idx := KContext, Res := T` instance of the same acquaintance machinery
  PLA uses for individual de re (`Theories/Semantics/Dynamic/PLA/Belief.lean`).
- `Semantics.Tense.TensePronoun.fullPresupposition` — the value-level
  shadow this file connects to (the deleted `TemporalDeRe` triple was a
  shadow of *this* shadow; see the `isFelicitousWith_iff_…` theorem
  below for the bridge).
- `Core.Modality.HistoricalAlternatives.actualHistoryBase` —
  Klecha 2016 DOX substrate, available as the metaphysical instantiation
  via `metaphysicalAlternatives`.

## Two felicity predicates (value-level vs Abusch-faithful)

- `isFelicitousWith` — local constraint check at the holder's now
  (= `holderContext.time`). The value-level shadow of Abusch's
  reading. Equivalent to `TensePronoun.fullPresupposition` (see
  shadow lemma).
- `isAbuschFelicitous` — adds Abusch §3 modal rigidity: the
  time-concept identifies the same time across an alternative-set
  parameter. The substrate is **agnostic** about whether the
  alternatives are doxastic (Hintikka belief alternatives, the
  Abusch-canonical case) or metaphysical (Lewis-Cariani-Santorio
  shared-past, Klecha 2016 DOX). The user supplies whichever set the
  consumer's framework demands; convenience constructors
  `metaphysicalAlternatives` (legacy) and `doxasticAlternatives` make
  the parallel explicit. Concept-rigidity (`Core.Intension.IsRigid`)
  is sufficient to discharge modal-rigidity for any alternative-set
  — a constant-intension concept is automatically rigid.

## Bug fixes (PR-B, 0.230.554)

- **Bug 3 (speech vs holder now)**. The structure's context field was
  named `matrixContext` and the felicity predicate checked the
  constraint against `matrixContext.time`, which test code treated as
  speech time. Per @cite{abusch-1997} §7 ULC (p. 24): "the now of an
  epistemic alternative is an upper limit for the denotation of
  tenses" — the relevant time is the **attitude holder's now**, not
  the outer speech time. Field renamed `holderContext`; semantics
  clarified in docstring; the felicity check is now correct by
  construction (the relevant time IS what `holderContext.time`
  represents).
- **Bug 1 (modal base — metaphysical vs doxastic)**.
  `IsRigidAcrossAlternatives` previously took a `WorldHistory W T`
  parameter and quantified over `actualHistoryBase`, which is
  *metaphysical* (per `Core/Modality/HistoricalAlternatives.lean`'s
  own docstring). @cite{abusch-1997} §3 quantifies over the
  believer's **doxastic** alternatives (Hintikka). Parameter type
  lifted to `Set (WorldTimeIndex W T)`; doxastic + metaphysical
  become explicit instantiation choices via convenience
  constructors.

## What's still deferred

- **LF res-movement as a `Tree C W` rewrite operator.** This file
  exposes the *output* of res-movement (a coherent ⟨concept, holder⟩
  bundle), not the syntactic operation that produces it.
- **Schlenker 2004 ↔ Abusch 1997 contrastive theorem.** Both treat
  shifted temporal reference but with different mechanisms
  (centered-world acquaintance vs tower-temporalShift); the bridge
  theorem is a follow-up.
- **PLA-side individual unification.** The `EntityConcept` analog at
  `Idx := Assignment E × WitnessSeq E` is what PLA's `Concept E` is
  (definitionally); the formal unification theorem is in
  `Phenomena/TenseAspect/Studies/Abusch1997.lean`.
- **Anand-Nevins entity-concept bridge** (PR-C target).
-/

namespace Semantics.Tense.DeRe

open Core (Intension WorldTimeIndex)
open Core.Context (KContext)
open Core.Modality.HistoricalAlternatives (WorldHistory actualHistoryBase)
open Core.Time.Tense (TensePronoun GramTense TemporalAssignment)


-- ════════════════════════════════════════════════════════════════
-- § Time-concepts and entity-concepts
-- ════════════════════════════════════════════════════════════════

/-- A **time-concept** (@cite{abusch-1997} §3, def. 13): an intension
    from a centered Kaplanian context to a time. The Lewis-style
    "way of identifying a time" Abusch's `R₁ : eeiwt` builds on. -/
abbrev TimeConcept (W E P T : Type*) := Intension (KContext W E P T) T

/-- An **entity-concept** (@cite{lewis-1979-attitudes} centered-world de re,
    @cite{cresswell-vonstechow-1982}): an intension from a centered
    Kaplanian context to an entity. The dual of `TimeConcept` —
    instantiating Abusch 1997's individual ↔ temporal de re parallel
    on the entity side at the same evaluation index. -/
abbrev EntityConcept (W E P T : Type*) := Intension (KContext W E P T) E


-- ════════════════════════════════════════════════════════════════
-- § Temporal de re reading
-- ════════════════════════════════════════════════════════════════

/-- A **temporal de re reading** (@cite{abusch-1997} §3): a time-concept
    paired with the **attitude holder's centered context**. The actual
    res-denotation is the concept evaluated at the holder's context
    (`actualRes`); the base-world condition (Abusch p. 9) is satisfied
    by construction.

    The `holderContext` field carries the attitude bearer's centered
    Kaplanian context — `agent` = the believer, `world` = her actual
    world, `time` = her **now** (the perspective time at which embedded
    tenses are evaluated, per @cite{abusch-1997} §7 ULC). It is *not*
    the outer speaker's speech context; for unembedded uses the
    speaker is treated as her own attitude holder. -/
structure TemporalDeReReading (W E P T : Type*) where
  /-- The time-concept (Abusch's R₁): the way of identifying the res
      time across centered-world alternatives. -/
  concept : TimeConcept W E P T
  /-- The attitude holder's centered Kaplanian context. Per
      @cite{abusch-1997} §7 ULC, `holderContext.time` is the relevant
      perspective time for embedded tense evaluation — *not* the outer
      speaker's speech time. -/
  holderContext : KContext W E P T

namespace TemporalDeReReading

variable {W E P T : Type*}

/-- The actual time-denotation of the res, derived from the concept and
    the holder's centered context. -/
def actualRes (dr : TemporalDeReReading W E P T) : T :=
  dr.concept dr.holderContext

/-- **Base-world coherence** (@cite{abusch-1997} §3 p. 9): the actual
    res-time equals the concept's value at the holder's centered context.
    True by construction in this substrate. -/
theorem baseCoherent (dr : TemporalDeReReading W E P T) :
    dr.concept dr.holderContext = dr.actualRes := rfl


-- ════════════════════════════════════════════════════════════════
-- § Felicity and the value-level shadow
-- ════════════════════════════════════════════════════════════════

/-- Felicity of a temporal de re reading under a tense constraint:
    the actual res-time stands in the constraint's relation to the
    **holder's now** (= `holderContext.time`). Per @cite{abusch-1997}
    §7 ULC (p. 24), the holder's now is the relevant evaluation time
    for embedded tenses — a past-marked tense res-moved from under
    `believe` is constrained to denote a time before the believer's
    now, NOT before the outer speaker's speech time. -/
def isFelicitousWith [LinearOrder T] (dr : TemporalDeReReading W E P T)
    (constraint : GramTense) : Prop :=
  constraint.constrains dr.actualRes dr.holderContext.time

/-- **Value-level shadow lemma**: a temporal de re reading is felicitous
    with `tp.constraint` iff the corresponding `TensePronoun.fullPresupposition`
    holds at any temporal assignment that resolves the variable to the
    de re reading's `actualRes` and the eval-time to the holder's now.

    This makes precise the sense in which the deleted bare-triple substrate
    `(referent, evalTime, constraint : GramTense)` was a value-level
    shadow of the centered-world account: pick `referent := dr.actualRes`,
    `evalTime := dr.holderContext.time`. -/
theorem isFelicitousWith_iff_tensePronoun_fullPresupposition
    [LinearOrder T] (dr : TemporalDeReReading W E P T) (tp : TensePronoun)
    (g : TemporalAssignment T)
    (hRes : tp.resolve g = dr.actualRes)
    (hEval : tp.evalTime g = dr.holderContext.time) :
    dr.isFelicitousWith tp.constraint ↔ tp.fullPresupposition g := by
  simp only [isFelicitousWith, TensePronoun.fullPresupposition, hRes, hEval]


-- ════════════════════════════════════════════════════════════════
-- § Modal-alternative quantification (Abusch §3)
-- ════════════════════════════════════════════════════════════════

/-- **Modal rigidity** (@cite{abusch-1997} §3, p. 9): the time-concept
    evaluates to the same time at every world-time pair in a supplied
    alternative set, when that alternative is plugged into the holder's
    centered context. This is *the* de re property — what distinguishes
    a wide-scope res-time from a de dicto descriptive concept.

    The `alternatives` parameter is **agnostic** about modal base: the
    substrate accepts any `Set (WorldTimeIndex W T)`. Abusch's canonical
    setup uses **doxastic** alternatives (the believer's Hintikka belief
    set); Klecha 2016 DOX uses **metaphysical** alternatives (worlds
    sharing the holder's actual past, via `actualHistoryBase`). The
    consumer chooses at the call site. Convenience constructors
    `metaphysicalAlternatives` and `doxasticAlternatives` provide the
    two standard instantiations. -/
def IsRigidAcrossAlternatives (dr : TemporalDeReReading W E P T)
    (alternatives : Set (WorldTimeIndex W T)) : Prop :=
  Intension.IsRigidOn (fun s : WorldTimeIndex W T =>
    dr.concept (dr.holderContext.shiftWorldTime s))
    alternatives

/-- **Full Abusch felicity** (@cite{abusch-1997} §3): value-level
    constraint check (actual res-time stands in the constraint's
    relation to the holder's now) AND modal rigidity across a
    supplied alternative-set. The value-level shadow `isFelicitousWith`
    captures only the first conjunct; this predicate is what an
    Abusch-faithful study should use. -/
def isAbuschFelicitous [LinearOrder T] (dr : TemporalDeReReading W E P T)
    (alternatives : Set (WorldTimeIndex W T)) (constraint : GramTense) : Prop :=
  dr.isFelicitousWith constraint ∧ dr.IsRigidAcrossAlternatives alternatives

/-- A rigid time-concept (constant intension, `Core.Intension.IsRigid`)
    is automatically rigid across any alternative-set. The rigid-concept
    derivations in `Studies/Abusch1997.lean` discharge
    `IsRigidAcrossAlternatives` "for free" via this lemma.

    Composes two general substrate lemmas:
    `Intension.IsRigid.precomp` (pre-composition with the
    `shiftWorldTime` map preserves rigidity) and
    `Intension.IsRigid.isRigidOn` (full rigidity implies
    rigidity-on-any-set). The chain makes the substrate's design
    visible: temporal de re ≡ rigidity preserved under the centered
    coordinate-shift, restricted to whichever alternative set the
    consumer supplies. -/
theorem IsRigidAcrossAlternatives_of_concept_isRigid
    (dr : TemporalDeReReading W E P T)
    (h : Intension.IsRigid dr.concept)
    (alternatives : Set (WorldTimeIndex W T)) :
    dr.IsRigidAcrossAlternatives alternatives :=
  (h.precomp dr.holderContext.shiftWorldTime).isRigidOn alternatives

/-- **Abusch felicity ⇒ value-level felicity**: the modal-quantified
    predicate strictly refines the value-level shadow. Old code that
    only checks `isFelicitousWith` is conservative — anything proved
    via `isAbuschFelicitous` projects through. -/
theorem isFelicitousWith_of_isAbuschFelicitous [LinearOrder T]
    (dr : TemporalDeReReading W E P T)
    (alternatives : Set (WorldTimeIndex W T))
    (constraint : GramTense)
    (h : dr.isAbuschFelicitous alternatives constraint) :
    dr.isFelicitousWith constraint := h.1


-- ════════════════════════════════════════════════════════════════
-- § Alternative-set constructors (modal-base instantiations)
-- ════════════════════════════════════════════════════════════════

/-- **Metaphysical** alternative-set instantiation (@cite{klecha-2016}
    DOX): the worlds sharing the holder's actual world's history up to
    her now, paired with times at-or-before her now. Recovers the
    pre-PR-B `WorldHistory`-based behavior as a special case. -/
def metaphysicalAlternatives [LE T]
    (history : WorldHistory W T) (dr : TemporalDeReReading W E P T) :
    Set (WorldTimeIndex W T) :=
  actualHistoryBase history dr.holderContext.toSituation

/-- **Doxastic** alternative-set instantiation (@cite{abusch-1997} §3,
    Hintikka belief alternatives): the world-time pairs the holder
    considers epistemically possible. Parameterized on a generic
    `dox : E → W → WorldTimeIndex W T → Prop` representing the
    holder's doxastic accessibility relation over centered alternatives.
    This is the modal-base @cite{abusch-1997} canonically uses, distinct
    from the metaphysical version above. -/
def doxasticAlternatives
    (dox : E → W → WorldTimeIndex W T → Prop) (dr : TemporalDeReReading W E P T) :
    Set (WorldTimeIndex W T) :=
  { s' | dox dr.holderContext.agent dr.holderContext.world s' }


-- ════════════════════════════════════════════════════════════════
-- § Acquaintance: instantiating the polymorphic substrate
-- ════════════════════════════════════════════════════════════════

/-- The Aloni cover for time-concepts: a set of `TimeConcept`s
    representing the believer's available "ways of identifying" a time.
    Instantiates `Acquaintance.Cover` at the centered-context index. -/
abbrev TimeCover (W E P T : Type*) :=
  Semantics.Reference.Acquaintance.Cover (KContext W E P T) T

/-- A time `t` is **temporally-acquainted** at the holder's context `c`
    (with respect to a time-cover `C`) when some concept in `C` picks
    out `t` at `c`. The temporal analog of @cite{lewis-1979-attitudes}'s
    acquaintance — instantiating polymorphic `isAcquaintedWith` at
    `Idx := KContext`, `Res := T`. -/
abbrev isTemporallyAcquaintedWith {W E P T : Type*}
    (t : T) (C : TimeCover W E P T) (c : KContext W E P T) : Prop :=
  Semantics.Reference.Acquaintance.isAcquaintedWith t C c

/-- The holder-anchored res-time of a de re reading is acquainted-with
    via the singleton time-cover `{dr.concept}`. The concept itself
    witnesses the acquaintance. -/
theorem actualRes_isTemporallyAcquaintedWith
    (dr : TemporalDeReReading W E P T) :
    isTemporallyAcquaintedWith dr.actualRes ({dr.concept} : TimeCover W E P T)
      dr.holderContext :=
  ⟨dr.concept, rfl, rfl⟩

end TemporalDeReReading

end Semantics.Tense.DeRe
