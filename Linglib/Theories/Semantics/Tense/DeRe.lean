import Linglib.Core.Context.Basic
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Theories.Semantics.Reference.Acquaintance
import Linglib.Theories.Semantics.Tense.Basic

/-!
# Centered-World Temporal De Re
@cite{lewis-1979} (centered-worlds + de se reduction);
@cite{cresswell-vonstechow-1982} (de re belief generalized);
@cite{abusch-1997} (the temporal application).

Abusch 1997's temporal de re analysis: a tense morpheme can take wide
scope over an attitude operator by occupying the *res* position. The res
contributes a **time-concept** (`Intension (KContext) T` — Abusch's
`R₁ : eeiwt` of def. 13) plus a **base-world condition** (in `w₀`, the
actual time-denotation is picked out by the concept relative to the
matrix context — Abusch §3, p. 9).

This file is anchored on the centered-world de re framework, not on
Abusch 1997 alone — Lewis 1979 + Cresswell & von Stechow 1982 are the
foundational layer Abusch builds on. Paper-anchored derivation theorems
live in `Phenomena/TenseAspect/Studies/Abusch1997.lean`.

## Reuse

- `Core.Intension W τ` (`Core/IntensionalLogic/Rigidity.lean`) — substrate
  for time-concepts. `IsRigid` captures the "same time across alternatives"
  property that distinguishes de re from de dicto temporal anaphora.
- `Core.Context.KContext W E P T` (`Core/Context/Basic.lean`) — the
  centered Kaplanian context `⟨agent, addressee, world, time, position⟩`.
  Abusch's `⟨x_self, t_now, w⟩` is a 3-field projection; `KContext` is
  the richer object the rest of linglib already commits to.
- `Semantics.Reference.Acquaintance` — polymorphic `Cover`, `nameCover`,
  `isAcquaintedWith`. The temporal-de-re reading is the
  `Idx := KContext, Res := T` instance of the same acquaintance machinery
  PLA uses for individual de re (`Theories/Semantics/Dynamic/PLA/Belief.lean`).
- `Semantics.Tense.TensePronoun.fullPresupposition` — the value-level
  shadow this file connects to (the deleted `TemporalDeRe` triple was a
  shadow of *this* shadow; see the `isFelicitousWith_iff_…` theorem
  below for the bridge).

## Two felicity predicates (value-level vs Abusch-faithful)

- `isFelicitousWith` — local constraint check at the matrix context.
  The value-level shadow of Abusch's reading. Equivalent to
  `TensePronoun.fullPresupposition` (see shadow lemma).
- `isAbuschFelicitous` — adds Abusch §3 modal rigidity: the time-concept
  identifies the same time across every believer-actual-history
  alternative (`Core.Modality.HistoricalAlternatives.actualHistoryBase`).
  This is what distinguishes a wide-scope res-time from a de dicto
  descriptive concept. Concept-rigidity (`Core.Intension.IsRigid`) is
  sufficient — a constant-intension concept is automatically rigid
  across alternatives.

## What's deferred

- **LF res-movement as a `Tree C W` rewrite operator.** This file exposes
  the *output* of res-movement (a coherent ⟨concept, matrix⟩ bundle), not
  the syntactic operation that produces it.
- **Schlenker 2004 ↔ Abusch 1997 contrastive theorem.** Both treat
  shifted temporal reference but with different mechanisms (centered-world
  acquaintance vs tower-temporalShift); the bridge theorem is a follow-up.
- **PLA-side individual unification.** The `EntityConcept` analog at
  `Idx := Assignment E × WitnessSeq E` is what PLA's `Concept E` is
  (definitionally); the formal unification theorem is in
  `Phenomena/TenseAspect/Studies/Abusch1997.lean`.
-/

namespace Semantics.Tense.DeRe

open Core (Intension)
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

/-- An **entity-concept** (@cite{lewis-1979} centered-world de re,
    @cite{cresswell-vonstechow-1982}): an intension from a centered
    Kaplanian context to an entity. The dual of `TimeConcept` —
    instantiating Abusch 1997's individual ↔ temporal de re parallel
    on the entity side at the same evaluation index. -/
abbrev EntityConcept (W E P T : Type*) := Intension (KContext W E P T) E


-- ════════════════════════════════════════════════════════════════
-- § Temporal de re reading
-- ════════════════════════════════════════════════════════════════

/-- A **temporal de re reading** (@cite{abusch-1997} §3): a time-concept
    paired with a matrix context. The actual res-denotation is the
    concept evaluated at the matrix context (`actualRes`); the
    base-world condition (Abusch p. 9) is satisfied by construction. -/
structure TemporalDeReReading (W E P T : Type*) where
  /-- The time-concept (Abusch's R₁): the way of identifying the res
      time across centered-world alternatives. -/
  concept : TimeConcept W E P T
  /-- The matrix Kaplanian context — the believer's "actual" anchor. -/
  matrixContext : KContext W E P T

namespace TemporalDeReReading

variable {W E P T : Type*}

/-- The actual time-denotation of the res, derived from the concept and
    the matrix context. -/
def actualRes (dr : TemporalDeReReading W E P T) : T :=
  dr.concept dr.matrixContext

/-- **Base-world coherence** (@cite{abusch-1997} §3 p. 9): the actual
    res-time equals the concept's value at the matrix context. True by
    construction in this substrate. -/
theorem baseCoherent (dr : TemporalDeReReading W E P T) :
    dr.concept dr.matrixContext = dr.actualRes := rfl


-- ════════════════════════════════════════════════════════════════
-- § Felicity and the value-level shadow
-- ════════════════════════════════════════════════════════════════

/-- Felicity of a temporal de re reading under a tense constraint:
    the (matrix-anchored) actual res-time stands in the constraint's
    relation to the matrix context's time. -/
def isFelicitousWith [LinearOrder T] (dr : TemporalDeReReading W E P T)
    (constraint : GramTense) : Prop :=
  constraint.constrains dr.actualRes dr.matrixContext.time

/-- **Value-level shadow lemma**: a temporal de re reading is felicitous
    with `tp.constraint` iff the corresponding `TensePronoun.fullPresupposition`
    holds at any temporal assignment that resolves the variable to the
    de re reading's `actualRes` and the eval-time to the matrix context's time.

    This makes precise the sense in which the deleted bare-triple substrate
    `(referent, evalTime, constraint : GramTense)` was a value-level
    shadow of the centered-world account: pick `referent := dr.actualRes`,
    `evalTime := dr.matrixContext.time`. -/
theorem isFelicitousWith_iff_tensePronoun_fullPresupposition
    [LinearOrder T] (dr : TemporalDeReReading W E P T) (tp : TensePronoun)
    (g : TemporalAssignment T)
    (hRes : tp.resolve g = dr.actualRes)
    (hEval : tp.evalTime g = dr.matrixContext.time) :
    dr.isFelicitousWith tp.constraint ↔ tp.fullPresupposition g := by
  simp only [isFelicitousWith, TensePronoun.fullPresupposition, hRes, hEval]


-- ════════════════════════════════════════════════════════════════
-- § Modal-alternative quantification (Abusch §3)
-- ════════════════════════════════════════════════════════════════

/-- **Modal rigidity** (@cite{abusch-1997} §3, p. 9): the time-concept
    evaluates to the same time at every believer-actual-history
    alternative (`Core.Modality.HistoricalAlternatives.actualHistoryBase`)
    of the matrix context. This is *the* de re property — what
    distinguishes a wide-scope res-time from a de dicto descriptive
    concept.

    The matrix context's world and time are projected to a `WorldTimeIndex`
    via `KContext.toSituation`; alternatives are the `actualHistoryBase`
    of that projection; for each alternative we replace the matrix
    context's `world` and `time` and demand the concept evaluates to
    `actualRes`. -/
def IsRigidAcrossAlternatives [LE T] (dr : TemporalDeReReading W E P T)
    (history : WorldHistory W T) : Prop :=
  ∀ s' ∈ actualHistoryBase history dr.matrixContext.toSituation,
    dr.concept { dr.matrixContext with world := s'.world, time := s'.time }
      = dr.actualRes

/-- **Full Abusch felicity** (@cite{abusch-1997} §3): value-level
    constraint check (matrix-anchored res-time stands in the constraint's
    relation to matrix time) AND modal rigidity across the believer's
    actual-history alternatives. The value-level shadow `isFelicitousWith`
    captures only the first conjunct; this predicate is what an
    Abusch-faithful study should use. -/
def isAbuschFelicitous [LinearOrder T] (dr : TemporalDeReReading W E P T)
    (history : WorldHistory W T) (constraint : GramTense) : Prop :=
  dr.isFelicitousWith constraint ∧ dr.IsRigidAcrossAlternatives history

/-- A rigid time-concept (constant intension, `Core.Intension.IsRigid`)
    is automatically rigid across any believer-actual-history alternatives.
    This is why the rigid-concept derivations in `Studies/Abusch1997.lean`
    can discharge `IsRigidAcrossAlternatives` "for free." -/
theorem IsRigidAcrossAlternatives_of_concept_isRigid [LE T]
    (dr : TemporalDeReReading W E P T)
    (h : Intension.IsRigid dr.concept) (history : WorldHistory W T) :
    dr.IsRigidAcrossAlternatives history := by
  intro s' _
  rw [h { dr.matrixContext with world := s'.world, time := s'.time }
        dr.matrixContext]
  rfl

/-- **Abusch felicity ⇒ value-level felicity**: the modal-quantified
    predicate strictly refines the value-level shadow. Old code that
    only checks `isFelicitousWith` is conservative — anything proved
    via `isAbuschFelicitous` projects through. -/
theorem isFelicitousWith_of_isAbuschFelicitous [LinearOrder T]
    (dr : TemporalDeReReading W E P T) (history : WorldHistory W T)
    (constraint : GramTense)
    (h : dr.isAbuschFelicitous history constraint) :
    dr.isFelicitousWith constraint := h.1


-- ════════════════════════════════════════════════════════════════
-- § Acquaintance: instantiating the polymorphic substrate
-- ════════════════════════════════════════════════════════════════

/-- The Aloni cover for time-concepts: a set of `TimeConcept`s
    representing the believer's available "ways of identifying" a time.
    Instantiates `Acquaintance.Cover` at the centered-context index. -/
abbrev TimeCover (W E P T : Type*) :=
  Semantics.Reference.Acquaintance.Cover (KContext W E P T) T

/-- A time `t` is **temporally-acquainted** at matrix context `c` (with
    respect to a time-cover `C`) when some concept in `C` picks out `t`
    at `c`. The temporal analog of @cite{lewis-1979}'s acquaintance —
    instantiating polymorphic `isAcquaintedWith` at `Idx := KContext`,
    `Res := T`. -/
abbrev isTemporallyAcquaintedWith {W E P T : Type*}
    (t : T) (C : TimeCover W E P T) (c : KContext W E P T) : Prop :=
  Semantics.Reference.Acquaintance.isAcquaintedWith t C c

/-- The matrix-anchored res-time of a de re reading is acquainted-with
    via the singleton time-cover `{dr.concept}`. The concept itself
    witnesses the acquaintance. -/
theorem actualRes_isTemporallyAcquaintedWith
    (dr : TemporalDeReReading W E P T) :
    isTemporallyAcquaintedWith dr.actualRes ({dr.concept} : TimeCover W E P T)
      dr.matrixContext :=
  ⟨dr.concept, rfl, rfl⟩

end TemporalDeReReading

end Semantics.Tense.DeRe
