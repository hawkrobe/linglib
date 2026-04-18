import Linglib.Core.StringHom
import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone

/-!
# Phonological Tiers

@cite{goldsmith-1976} @cite{belth-2026}

Phonology-flavored re-export of `Core.StringHom`'s `Tier` abstraction. A
phonological tier is a per-symbol partial map from segmental units to the
tier alphabet, lifted to strings via `List.filterMap`. This is the same
mathematical object whether we are projecting:

- a tonal tier from TBUs (@cite{goldsmith-1976}),
- a sibilant tier from segments for harmony (@cite{rose-walker-2004}),
- or any learned tier projection from D2L (@cite{belth-2026}).

The `Phonology.Tier α β` abbreviation is *definitionally equal* to
`Core.Tier α β` — phonological constraint constructors that take
`project : C → List α` (e.g. `mkOCP`) accept `Tier.apply T` directly,
no adapter needed.

## Standard Constructors

- `Tier.byFeature` — project segments specified for a feature value (e.g.
  the [+nasal] tier).
- `Tier.byFeaturePred` — project segments matching a feature-spec predicate.
- `Tier.tonal` — extract the tonal tier from a TBU sequence
  (@cite{goldsmith-1976}). This **is** the canonical `tonalTier` of
  `BasemapCorrespondence.lean`, factored through `Tier.apply`.
-/

namespace Phonology

open Core

universe u v

/-- A phonological tier projection. Definitionally equal to `Core.Tier`. -/
abbrev Tier (α : Type u) (β : Type v) : Type _ := Core.Tier α β

namespace Tier

-- ---- Re-export the Core operations under the `Phonology.Tier` namespace ----

/-- Lift a tier to a list-level projection. -/
abbrev apply {α : Type u} {β : Type v} :
    Tier α β → List α → List β := Core.Tier.apply
/-- Lift a tier carrying source indices (matches @cite{belth-2026} `proj(x,T)`). -/
abbrev applyI {α : Type u} {β : Type v} :
    Tier α β → List α → List (β × ℕ) := Core.Tier.applyI
/-- Identity tier. -/
abbrev id' {α : Type u} : Tier α α := Core.Tier.id'
/-- Empty tier. -/
abbrev empty {α : Type u} {β : Type v} : Tier α β := Core.Tier.empty
/-- Class-predicate tier. -/
abbrev byClass {α : Type u} (p : α → Bool) : Tier α α := Core.Tier.byClass p
/-- Total-function tier. -/
abbrev total {α : Type u} {β : Type v} (f : α → β) : Tier α β := Core.Tier.total f

-- ---- Phonology-specific constructors ----------------------------------------

/-- Project segments where feature `f` has the specified value `v`.
    The standard "[+nasal] tier" or "[−back] tier" for harmony analyses. -/
def byFeature (f : Feature) (v : Bool) : Tier Segment Segment :=
  Core.Tier.byClass (fun s => s.hasValue f v)

/-- Project segments matching an arbitrary feature-spec predicate.
    Useful for natural-class tiers (e.g. project all sibilants). -/
def byFeaturePred (p : Segment → Bool) : Tier Segment Segment :=
  Core.Tier.byClass p

/-- The canonical tonal tier (@cite{goldsmith-1976}): every TBU projects
    to its tone. This is `Tier.total TBU.tone` — length-preserving and
    total (no erasure). -/
def tonal {S : Type} : Tier (Phonology.Autosegmental.GrammaticalTone.TBU S)
                          Phonology.Autosegmental.RegisterTier.ToneFeature :=
  Core.Tier.total Phonology.Autosegmental.GrammaticalTone.TBU.tone

/-- The tonal tier projection equals the historical `List.map TBU.tone`
    formulation. Used to ground `BasemapCorrespondence.tonalTier` through
    the unified `Tier.apply` interface. -/
theorem apply_tonal {S : Type}
    (tbus : List (Phonology.Autosegmental.GrammaticalTone.TBU S)) :
    apply tonal tbus = tbus.map Phonology.Autosegmental.GrammaticalTone.TBU.tone :=
  Core.Tier.apply_total _ _

end Tier

end Phonology
