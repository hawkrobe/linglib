import Linglib.Semantics.Reference.Context.Basic
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Tense.Embedding

/-!
# Centered-world temporal de re

[abusch-1997]'s temporal de re: a tense morpheme can take wide scope over
an attitude operator by occupying the *res* position. The res contributes
a time-concept (`TimeConcept`) plus a base-world condition — in the base
world, the res denotation is picked out by an acquaintance relation
relative to the holder's centered context ([abusch-1997] §3 p. 9). The
centered-world framework is [lewis-1979-attitudes]'s de se reduction as
generalized by [cresswell-vonstechow-1982]; Abusch develops it for
individuals in §3 (the acquaintance relation `R₁ : eeiwt`, eq. 12, and
the centered-proposition assembly, eq. 13) and applies it to times in §4
(temporal acquaintance relations) and §11. Paper-anchored derivation
theorems live in `Studies/Abusch1997.lean`.

## Implementation notes

Time-concepts are `Intensional.Intension`s from the centered Kaplanian
context `Semantics.Context.KContext`
(`Semantics/Reference/Context/Basic.lean`) — Abusch's `⟨x_self, t_now, w⟩`
is a three-field projection of the richer context the rest of linglib
commits to. Rigidity across alternatives is `Intension.IsRigidOn` after
`KContext.shiftWorldTime`; the alternative set is a bare
`Set (Index W T)`, so doxastic (Hintikka belief alternatives,
the Abusch-canonical case) and metaphysical ([klecha-2016] DOX via
`HistoricalAlternatives.actualHistoryBase`) modal bases are call-site
instantiations (`doxasticAlternatives`, `metaphysicalAlternatives`).
-/

namespace Tense.DeRe

open Intensional (Intension Index)
open Semantics.Context (KContext)
open HistoricalAlternatives (actualHistoryBase)


/-! ### Time-concepts -/

/-- A **time-concept**: an intension from a centered Kaplanian context to
    a time — a way of identifying a time across centered-world
    alternatives. The temporal instance of [abusch-1997]'s
    centered-proposition framework (§3 develops it for individuals via
    the acquaintance relation `R₁ : eeiwt`, eq. 12; §4 applies it to
    times). -/
abbrev TimeConcept (W E P T : Type*) := Intension (KContext W E P T) T


/-! ### Temporal de re reading -/

/-- A **temporal de re reading** ([abusch-1997] §3): a time-concept paired
    with the attitude holder's centered context. The actual res-denotation
    is the concept evaluated at the holder's context (`actualRes`), so the
    base-world condition (§3 p. 9) holds by construction. -/
@[ext]
structure TemporalDeReReading (W E P T : Type*) where
  /-- The time-concept: the way of identifying the res time across
      centered-world alternatives. -/
  concept : TimeConcept W E P T
  /-- The attitude holder's centered Kaplanian context. Per
      [abusch-1997] §7 ULC, `holderContext.time` is the holder's now —
      the perspective time for embedded tense evaluation, *not* the
      outer speaker's speech time. -/
  holderContext : KContext W E P T

namespace TemporalDeReReading

variable {W E P T : Type*}

/-- The actual time-denotation of the res: the concept evaluated at the
    holder's centered context. -/
def actualRes (dr : TemporalDeReReading W E P T) : T :=
  dr.concept dr.holderContext


/-! ### Felicity -/

/-- Value-level felicity of a temporal de re reading under a tense
    constraint: the actual res-time stands in the constraint's relation
    to the **holder's now** ([abusch-1997] §7 ULC, p. 24–25) — a
    past-marked tense res-moved from under *believe* must denote a time
    before the believer's now, not before the outer speech time. -/
def IsFelicitousWith [LinearOrder T] (dr : TemporalDeReReading W E P T)
    (constraint : Finset Ordering) : Prop :=
  Core.Order.holds constraint dr.actualRes dr.holderContext.time

/-- **Modal rigidity**: the time-concept evaluates to the same time at
    every world-time pair in the alternative set — what distinguishes a
    wide-scope res-time from a de dicto descriptive concept. This lifts
    [abusch-1997]'s base-world condition (§3 p. 9) to a quantification
    over the holder's alternatives; Abusch herself states the analysis
    through acquaintance relations, not rigidity. The alternative set is
    modal-base-agnostic: doxastic ([abusch-1997]'s Hintikka setup) or
    metaphysical ([klecha-2016] DOX) — see the constructors below. -/
def IsRigidAcrossAlternatives (dr : TemporalDeReReading W E P T)
    (alternatives : Set (Index W T)) : Prop :=
  Intension.IsRigidOn (fun s : Index W T =>
    dr.concept (dr.holderContext.shiftWorldTime s))
    alternatives

/-- **Felicity** of a temporal de re reading ([abusch-1997] §3): the
    value-level constraint check at the holder's now
    (`IsFelicitousWith`) together with modal rigidity across the
    supplied alternative set (`IsRigidAcrossAlternatives`). -/
def IsFelicitous [LinearOrder T] (dr : TemporalDeReReading W E P T)
    (alternatives : Set (Index W T)) (constraint : Finset Ordering) : Prop :=
  dr.IsFelicitousWith constraint ∧ dr.IsRigidAcrossAlternatives alternatives

/-- A rigid time-concept (`Intensional.Intension.IsRigid`) is rigid
    across any alternative set: pre-composition with `shiftWorldTime`
    preserves rigidity (`IsRigid.precomp`), and full rigidity restricts
    to any set (`IsRigid.isRigidOn`). -/
theorem isRigidAcrossAlternatives_of_isRigid
    (dr : TemporalDeReReading W E P T)
    (h : Intension.IsRigid dr.concept)
    (alternatives : Set (Index W T)) :
    dr.IsRigidAcrossAlternatives alternatives :=
  (h.precomp dr.holderContext.shiftWorldTime).isRigidOn alternatives


/-! ### Alternative-set constructors (modal-base instantiations) -/

/-- **Metaphysical** alternative set ([klecha-2016] DOX): the worlds
    sharing the holder's actual history up to her now, paired with times
    at-or-before her now. -/
def metaphysicalAlternatives [LE T]
    (history : HistoricalAlternatives W T) (dr : TemporalDeReReading W E P T) :
    Set (Index W T) :=
  actualHistoryBase history dr.holderContext.toIndex

/-- **Doxastic** alternative set ([abusch-1997] §3, Hintikka belief
    alternatives): the world-time pairs the holder considers possible,
    for a doxastic accessibility relation `dox` over centered
    alternatives. -/
def doxasticAlternatives
    (dox : E → W → Index W T → Prop) (dr : TemporalDeReReading W E P T) :
    Set (Index W T) :=
  { s' | dox dr.holderContext.agent dr.holderContext.world s' }

end TemporalDeReReading

end Tense.DeRe
